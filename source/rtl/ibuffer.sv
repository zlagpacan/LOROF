/*
    Filename: ibuffer.sv
    Author: zlagpacan
    Description: RTL for Instruction Buffer
    Spec: LOROF/spec/design/ibuffer.md
*/

`include "corep.vh"

module ibuffer (

    // seq
    input logic CLK,
    input logic nRST,

    // enq
    input logic                         enq_valid,
    input corep::ibuffer_enq_info_t     enq_info,
    input logic                         enq_fetch_hit_valid,
    input corep::fetch16B_t             enq_fetch_hit_fetch16B,

    // enq feedback
    output logic                        enq_ready,
    output corep::fmid_t                enq_fmid,

    // fetch miss return
    input logic                 fetch_miss_return_valid,
    input corep::fmid_t         fetch_miss_return_fmid,
    input corep::fetch16B_t     fetch_miss_return_fetch16B,

    // deq
    output logic                                deq_valid,
    output corep::ibuffer_deq_entry_t [3:0]     deq_entry_by_way,

    // def feedback
    input logic                                 deq_ready,

    // restart
    input logic restart_valid
);

    // to allow distram w/ 1 write port, can only do one of miss return or hit return on same-cycle
        // icache's choice if want to use
            // i.e. can use read port for miss access replay

    // ----------------------------------------------------------------
    // Signals:

    // info distram
    corep::ibuffer_idx_t        info_distram_rindex;
    corep::ibuffer_enq_info_t   info_distram_rdata;

    logic                       info_distram_wen;
    corep::ibuffer_idx_t        info_distram_windex;
    corep::ibuffer_enq_info_t   info_distram_wdata;

    // instr distram
    corep::ibuffer_idx_t    instr_distram_rindex;
    corep::fetch16B_t       instr_distram_rdata;

    logic                   instr_distram_wen;
    corep::ibuffer_idx_t    instr_distram_windex;
    corep::fetch16B_t       instr_distram_wdata;

    // distram control
    logic distram_enq_valid;
    logic distram_enq_ready;
    logic distram_deq_valid;
    logic distram_ptr_says_deq_valid;
    logic distram_deq_ready;

    corep::ibuffer_idx_t    distram_enq_ptr, distram_enq_ptr_plus_1;
    corep::ibuffer_idx_t    distram_deq_ptr, distram_deq_ptr_plus_1;

    // fetch miss control
    logic [corep::IBUFFER_ENTRIES-1:0]          fetch_miss_waiting_by_entry;
    corep::fmid_t [corep::IBUFFER_ENTRIES-1:0]  fetch_miss_fmid_by_entry;

    logic [corep::IBUFFER_ENTRIES-1:0]  fetch_miss_fill_valid_by_entry;
    logic                               fetch_miss_fill_valid;
    corep::ibuffer_idx_t                fetch_miss_fill_idx;

    logic                               fetch_hit_fill_valid;

    // fmid tracker
    logic           fmid_tracker_new_id_consume;
    logic           fmid_tracker_new_id_ready;
    corep::fmid_t   fmid_tracker_new_id;

    logic           fmid_tracker_old_id_done;
    corep::fmid_t   fmid_tracker_old_id;

    // 2x entry shift reg for dynamic deq
    corep::ibuffer_enq_info_t   info_by_reg         [1:0];
    corep::fetch16B_t           instr16B_by_reg     [1:0];

    logic shift0_valid;
    logic shift1_valid;

    // 2x8 entry shift reg helper signals
    logic [1:0]                             valid_by_reg;
    logic [1:0][corep::FETCH_LANES-1:0]     valid_vec_by_reg;
    logic [1:0][corep::FETCH_LANES-1:0]     uncompressed_vec_by_reg;
    logic [1:0][corep::FETCH_LANES-1:0]     redirect_vec_by_reg;

    logic [1:0][corep::FETCH_LANES-1:0]     deqing_vec_by_reg;

    // deq control
    logic [3:0]                                 deq_valid_by_way;
    logic [3:0][corep::LOG_FETCH_LANES+1-1:0]   deq_first2B_idx_by_way;
    logic [3:0][corep::LOG_FETCH_LANES+1-1:0]   deq_second2B_idx_by_way;

    // ----------------------------------------------------------------
    // Logic:

    // distram control
    generate
        // power-of-2 # entries can use simple +1 for ptr's
        if (corep::IBUFFER_ENTRIES & (corep::IBUFFER_ENTRIES - 1) == 0) begin
            assign distram_enq_ptr_plus_1 = distram_enq_ptr + 1;
            assign distram_deq_ptr_plus_1 = distram_deq_ptr + 1;
        end

        // otherwise, manual wraparound for ptr's
        else begin
            always_comb begin
                if (distram_enq_ptr == corep::IBUFFER_ENTRIES - 1) begin
                    distram_enq_ptr_plus_1 = 0;
                end
                else begin
                    distram_enq_ptr_plus_1 = distram_enq_ptr + 1;
                end
                if (distram_deq_ptr == corep::IBUFFER_ENTRIES - 1) begin
                    distram_deq_ptr_plus_1 = 0;
                end
                else begin
                    distram_deq_ptr_plus_1 = distram_deq_ptr + 1;
                end
            end
        end
    endgenerate
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            distram_enq_ptr <= 0;
            distram_deq_ptr <= 0;
            distram_enq_ready <= 1'b1;
            distram_ptr_says_deq_valid <= 1'b0;
        end
        else begin
            if (distram_enq_valid) begin
                distram_enq_ptr <= distram_enq_ptr_plus_1;
            end

            if (distram_deq_ready & distram_deq_valid) begin
                distram_deq_ptr <= distram_deq_ptr_plus_1;
            end

            if ((distram_enq_valid) & ~(distram_deq_ready & distram_deq_valid)) begin
                distram_enq_ready <= distram_enq_ptr_plus_1 != distram_deq_ptr;
                distram_ptr_says_deq_valid <= 1'b1;
            end

            if ((distram_deq_ready & distram_deq_valid) & ~(distram_enq_valid)) begin
                distram_enq_ready <= 1'b1;
                distram_ptr_says_deq_valid <= distram_deq_ptr_plus_1 != distram_enq_ptr;
            end

            // top priority restart
            if (restart_valid) begin
                distram_enq_ptr <= 0;
                distram_deq_ptr <= 0;
                distram_enq_ready <= 1'b1;
                distram_ptr_says_deq_valid <= 1'b0;
            end
        end
    end
    always_comb begin
        // only enq into distram on true enq condition
        distram_enq_valid = enq_valid & enq_ready;

        // only deq from distram if entry not waiting on miss fill
        distram_deq_valid = distram_ptr_says_deq_valid & ~fetch_miss_waiting_by_entry[distram_deq_ptr];
    end

    // info distram IO
    always_comb begin
        info_distram_rindex = distram_deq_ptr;
        
        info_distram_wen = distram_enq_valid;
        info_distram_windex = distram_enq_ptr;
        info_distram_wdata = enq_info;
    end

    // instr distram IO
    always_comb begin
        instr_distram_rindex = distram_deq_ptr;

        instr_distram_wen = fetch_miss_fill_valid | fetch_hit_fill_valid;
        instr_distram_windex = fetch_miss_fill_valid ? fetch_miss_fill_idx : distram_enq_ptr;
        instr_distram_wdata = fetch_miss_fill_valid ? fetch_miss_return_fetch16B : enq_fetch_hit_fetch16B;
    end

    // distram's
    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::ibuffer_enq_info_t)),
        .OUTER_WIDTH(corep::IBUFFER_ENTRIES)
    ) INFO_DISTRAM (
        .CLK(CLK),
        .rindex(info_distram_rindex),
        .rdata(info_distram_rdata),
        .wen(info_distram_wen),
        .windex(info_distram_windex),
        .wdata(info_distram_wdata)
    );
    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::fetch16B_t)),
        .OUTER_WIDTH(corep::IBUFFER_ENTRIES)
    ) INSTR_DISTRAM (
        .CLK(CLK),
        .rindex(instr_distram_rindex),
        .rdata(instr_distram_rdata),
        .wen(instr_distram_wen),
        .windex(instr_distram_windex),
        .wdata(instr_distram_wdata)
    );

    // fetch miss logic
    always_comb begin
        for (int i = 0; i < corep::IBUFFER_ENTRIES; i++) begin
            if (
                fetch_miss_return_valid
                & fetch_miss_waiting_by_entry[i]
                & (fetch_miss_return_fmid == fetch_miss_fmid_by_entry[i])
            ) begin
                fetch_miss_fill_valid_by_entry[i] = 1'b1;
            end
            else begin
                fetch_miss_fill_valid_by_entry[i] = 1'b0;
            end
        end
    end
    one_hot_enc #(
        .WIDTH(corep::IBUFFER_ENTRIES)
    ) FETCH_MISS_FILL_IDX_ONE_HOT_ENC (
        .one_hot_in(fetch_miss_fill_valid_by_entry),
        .valid_out(fetch_miss_fill_valid),
        .index_out(fetch_miss_fill_idx)
    );
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            for (int i = 0; i < corep::IBUFFER_ENTRIES; i++) begin
                fetch_miss_waiting_by_entry[i] <= 1'b0;
                fetch_miss_fmid_by_entry[i] <= 0;
            end
        end
        else begin
            if (distram_enq_valid) begin
                fetch_miss_waiting_by_entry[distram_enq_ptr] <= ~enq_fetch_hit_valid;
                fetch_miss_fmid_by_entry[distram_enq_ptr] <= fmid_tracker_new_id;
            end
            if (fetch_miss_fill_valid) begin
                fetch_miss_waiting_by_entry[fetch_miss_fill_idx] <= 1'b0;
            end
        end
    end
    always_comb begin
        enq_ready = 
            // underlying distram must be ready
            distram_enq_ready
            // no miss fill this cycle or no hit fill this cycle
            & (~fetch_miss_fill_valid | ~enq_fetch_hit_valid)
            // new fmid available or have hit so don't need one
            & (fmid_tracker_new_id_ready | enq_fetch_hit_valid)
        ;
        enq_fmid = fmid_tracker_new_id;

        fetch_hit_fill_valid = enq_valid & enq_ready & enq_fetch_hit_valid;
    end

    // id_tracker
    id_tracker #(
        .ID_COUNT(corep::FMID_COUNT)
    ) FMID_TRACKER (
        .CLK(CLK),
        .nRST(nRST),
        .new_id_consume(fmid_tracker_new_id_consume),
        .new_id_ready(fmid_tracker_new_id_ready),
        .new_id(fmid_tracker_new_id),
        .old_id_done(fmid_tracker_old_id_done),
        .old_id(fmid_tracker_old_id)
    );
    always_comb begin
        fmid_tracker_new_id_consume = enq_valid & enq_ready & ~enq_fetch_hit_valid;

        fmid_tracker_old_id_done = fetch_miss_return_valid;
        fmid_tracker_old_id = fetch_miss_return_fmid;
    end

    // distram deq -> shift reg enq logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            info_by_reg[0] <= '0;
            info_by_reg[1] <= '0;

            instr16B_by_reg[0] <= '0;
            instr16B_by_reg[1] <= '0;

            valid_by_reg <= 2'b00;
            valid_vec_by_reg <= '0;
            uncompressed_vec_by_reg <= '0;
            redirect_vec_by_reg <= '0;
        end
        else begin
            if (shift1_valid) begin
                info_by_reg[1] <= info_distram_rdata;
                instr16B_by_reg[1] <= instr_distram_rdata;

                valid_by_reg[1] <= distram_deq_valid & distram_deq_ready;
                valid_vec_by_reg[1] <= {corep::FETCH_LANES{distram_deq_valid & distram_deq_ready}} & info_distram_rdata.valid_by_lane;
                for (int i = 0; i < corep::FETCH_LANES; i++) begin
                    uncompressed_vec_by_reg[1][i] <= instr_distram_rdata[i][1:0] == 2'b11;
                end
                redirect_vec_by_reg[1] <= info_distram_rdata.redirect_taken_by_lane;
            end
            else if (deq_ready) begin
                valid_by_reg[1] <= valid_by_reg[1] & |(valid_vec_by_reg[1] & ~deqing_vec_by_reg[1]);
                valid_vec_by_reg[1] <= valid_vec_by_reg[1] & ~deqing_vec_by_reg[1];
            end

            if (shift0_valid) begin
                info_by_reg[0] <= info_by_reg[1];
                instr16B_by_reg[0] <= instr16B_by_reg[1];

                valid_by_reg[0] <= valid_by_reg[1] & |(valid_vec_by_reg[1] & ~deqing_vec_by_reg[1]);
                valid_vec_by_reg[0] <= valid_vec_by_reg[1] & ~deqing_vec_by_reg[1];
                uncompressed_vec_by_reg[0] <= uncompressed_vec_by_reg[1];
                redirect_vec_by_reg[0] <= redirect_vec_by_reg[1];
            end
            else if (deq_ready) begin
                valid_by_reg[0] <= valid_by_reg[0] & |(valid_vec_by_reg[0] & ~deqing_vec_by_reg[0]);
                valid_vec_by_reg[0] <= valid_vec_by_reg[0] & ~deqing_vec_by_reg[0];
            end

            // top priority restart
            if (restart_valid) begin
                valid_by_reg <= '0;
                valid_vec_by_reg <= '0;
            end
        end
    end

    // shift reg deq logic
    always_comb begin
        deq_valid = |deq_valid_by_way;

        // shift0 on shift reg 0 available next cycle
        shift0_valid = 
            deq_ready & (
                ~valid_by_reg[0]
                | &(~valid_vec_by_reg[0] | deqing_vec_by_reg[0])
            );

        // shift1 on shift reg 1 available next cycle
        shift1_valid = ~valid_by_reg[1] | shift0_valid;
            // deq invalidation of reg 1 impossible without shift0_valid, so shift0_valid covers it

        distram_deq_ready = shift1_valid;
    end

    // ibuffer_deqer for instr demuxing to 4 ways and deqing vec
    ibuffer_deqer IBUFFER_DEQER (
        .valid_vec(valid_vec_by_reg),
        .uncompressed_vec(uncompressed_vec_by_reg),
        .redirect_vec(redirect_vec_by_reg),
        .count_vec(),
        .deqing_vec(deqing_vec_by_reg),
        .valid_by_way(deq_valid_by_way),
        .first_idx_by_way(deq_first2B_idx_by_way),
        .second_idx_by_way(deq_second2B_idx_by_way)
    );

    // deq muxing
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            deq_entry_by_way[way].valid = deq_valid_by_way[way];

            if (uncompressed_vec_by_reg[deq_first2B_idx_by_way[way][3]][deq_first2B_idx_by_way[way][2:0]]) begin
                deq_entry_by_way[way].btb_hit = info_by_reg[deq_second2B_idx_by_way[way][3]].btb_hit_by_lane[deq_second2B_idx_by_way[way][2:0]];
                deq_entry_by_way[way].redirect_taken = info_by_reg[deq_second2B_idx_by_way[way][3]].redirect_taken_by_lane[deq_second2B_idx_by_way[way][2:0]];
                deq_entry_by_way[way].mid_instr_redirect = info_by_reg[deq_first2B_idx_by_way[way][3]].redirect_taken_by_lane[deq_first2B_idx_by_way[way][2:0]];
                deq_entry_by_way[way].bcb_idx = info_by_reg[deq_second2B_idx_by_way[way][3]].bcb_idx;
                if (
                    info_by_reg[deq_second2B_idx_by_way[way][3]].redirect_taken_by_lane[deq_second2B_idx_by_way[way][2:0]]
                    | deq_second2B_idx_by_way[way][2:0] == 3'h7
                ) begin
                    deq_entry_by_way[way].tgt_pc38 = info_by_reg[deq_second2B_idx_by_way[way][3]].tgt_pc38;
                end
                else begin
                    deq_entry_by_way[way].tgt_pc38 = {info_by_reg[deq_second2B_idx_by_way[way][3]].src_pc35, {deq_second2B_idx_by_way[way][2:0] + 3'b001}[2:0]};
                end
                deq_entry_by_way[way].page_fault = info_by_reg[deq_first2B_idx_by_way[way][3]].page_fault | info_by_reg[deq_second2B_idx_by_way[way][3]].page_fault;
                deq_entry_by_way[way].access_fault = info_by_reg[deq_first2B_idx_by_way[way][3]].access_fault | info_by_reg[deq_second2B_idx_by_way[way][3]].access_fault;
            end
            else begin
                deq_entry_by_way[way].btb_hit = info_by_reg[deq_first2B_idx_by_way[way][3]].btb_hit_by_lane[deq_first2B_idx_by_way[way][2:0]];
                deq_entry_by_way[way].redirect_taken = info_by_reg[deq_first2B_idx_by_way[way][3]].redirect_taken_by_lane[deq_first2B_idx_by_way[way][2:0]];
                deq_entry_by_way[way].mid_instr_redirect = 1'b0;
                deq_entry_by_way[way].bcb_idx = info_by_reg[deq_first2B_idx_by_way[way][3]].bcb_idx;
                if (
                    info_by_reg[deq_first2B_idx_by_way[way][3]].redirect_taken_by_lane[deq_first2B_idx_by_way[way][2:0]]
                    | deq_first2B_idx_by_way[way][2:0] == 3'h7
                ) begin
                    deq_entry_by_way[way].tgt_pc38 = info_by_reg[deq_first2B_idx_by_way[way][3]].tgt_pc38;
                end
                else begin
                    deq_entry_by_way[way].tgt_pc38 = {info_by_reg[deq_first2B_idx_by_way[way][3]].src_pc35, {deq_first2B_idx_by_way[way][2:0] + 3'b001}[2:0]};
                end
                deq_entry_by_way[way].page_fault = info_by_reg[deq_first2B_idx_by_way[way][3]].page_fault;
                deq_entry_by_way[way].access_fault = info_by_reg[deq_first2B_idx_by_way[way][3]].access_fault;
            end

            deq_entry_by_way[way].src_pc38 = {info_by_reg[deq_first2B_idx_by_way[way][3]].src_pc35, deq_first2B_idx_by_way[way][2:0]};
            deq_entry_by_way[way].mdp = info_by_reg[deq_first2B_idx_by_way[way][3]].mdp_by_lane[deq_first2B_idx_by_way[way][2:0]];
            deq_entry_by_way[way].fetch4B = {
                instr16B_by_reg[deq_second2B_idx_by_way[way][3]][deq_second2B_idx_by_way[way][2:0]],
                instr16B_by_reg[deq_first2B_idx_by_way[way][3]][deq_first2B_idx_by_way[way][2:0]]
            };
        end
    end

endmodule