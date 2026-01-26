/*
    Filename: gbpt.sv
    Author: zlagpacan
    Description: RTL for Global Branch Prediction Table
    Spec: LOROF/spec/design/gbpt.md
*/

`include "corep.vh"

module gbpt (

    // seq
    input logic CLK,
    input logic nRST,

    // arch state
    input corep::ASID_t arch_asid,

    // read req stage
    input logic                             read_req_valid,
    input corep::fetch_idx_t                read_req_fetch_index,
    input corep::GH_t                       read_req_gh,

    // read resp stage
    output logic [corep::FETCH_LANES-1:0]   read_resp_taken_by_lane,

    // update
    input logic             update_valid,
    input corep::PC38_t     update_pc38,
    input corep::GH_t       update_gh,
    input logic             update_taken
);

    // ----------------------------------------------------------------
    // Functions:

    function corep::GBPT_idx_t index_hash(corep::PC38_t pc38, corep::GH_t gh, corep::ASID_t asid);
        // low fetch index ^ gh ^ low asid
        index_hash = pc38[37 : corep::LOG_FETCH_LANES];
        index_hash ^= gh;
        index_hash ^= asid;
    endfunction

    function logic [1:0] tbc_updater(logic [1:0] last_state, logic is_taken);
        // {taken, strong}
            // SN: 01
            // WN: 00 -> want as default for fast warmup
            // WT: 10
            // ST: 11
        unique casez ({last_state, is_taken})
            3'b000: tbc_updater = 2'b01; // WN -> N -> SN
            3'b001: tbc_updater = 2'b11; // WN -> T -> ST
            3'b010: tbc_updater = 2'b01; // SN -> N -> SN
            3'b011: tbc_updater = 2'b00; // SN -> T -> WN
            3'b100: tbc_updater = 2'b01; // WT -> N -> SN
            3'b101: tbc_updater = 2'b11; // WT -> T -> ST
            3'b110: tbc_updater = 2'b10; // ST -> N -> WT
            3'b111: tbc_updater = 2'b11; // ST -> T -> ST
        endcase
    endfunction

    // ----------------------------------------------------------------
    // Signals:

    // gbpt array bram IO
        // index w/ gbpt index
    logic               gbpt_array_bram_read_port0_next_valid;
    corep::GBPT_idx_t   gbpt_array_bram_read_port0_next_index;
    corep::GBPT_set_t   gbpt_array_bram_read_port0_set;

    logic               gbpt_array_bram_read_port1_next_valid;
    corep::GBPT_idx_t   gbpt_array_bram_read_port1_next_index;
    corep::GBPT_set_t   gbpt_array_bram_read_port1_set;

    logic [$bits(corep::GBPT_set_t)/8-1:0]  gbpt_array_bram_write_byten;
    corep::GBPT_idx_t                       gbpt_array_bram_write_index;
    corep::GBPT_set_t                       gbpt_array_bram_write_set;

    // update write stage
    corep::fetch_lane_t     update_write_lane;
    logic                   update_write_taken;
    logic                   update_write_last_valid;
    logic                   update_write_forward;
    corep::GBPT_set_t       update_write_old_set;
    corep::GBPT_set_t       update_selected_old_set;

    // ----------------------------------------------------------------
    // Logic:

    // read req logic
    always_comb begin
        gbpt_array_bram_read_port0_next_valid = read_req_valid;
        gbpt_array_bram_read_port0_next_index = index_hash({read_req_fetch_index, {corep::LOG_FETCH_LANES{1'b0}}}, read_req_gh, arch_asid);
    end

    // read resp logic
    always_comb begin
        // simple decode msb as taken vs. not taken
        for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin
            read_resp_taken_by_lane[lane] = gbpt_array_bram_read_port0_set[lane][1];
        end
    end

    // update logic
    always_comb begin
        gbpt_array_bram_read_port1_next_valid = update_valid;
        gbpt_array_bram_read_port1_next_index = index_hash(update_pc38, update_gh, arch_asid);
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            gbpt_array_bram_write_byten <= '0;
            gbpt_array_bram_write_index <= 0;

            update_write_lane <= 0;
            update_write_taken <= 1'b0;
            update_write_last_valid <= 1'b0;
            update_write_forward <= 1'b0;
            update_write_old_set <= '0;
        end
        else begin
            gbpt_array_bram_write_byten <= {$bits(gbpt_array_bram_write_byten){update_valid}};
            gbpt_array_bram_write_index <= gbpt_array_bram_read_port1_next_index;

            update_write_lane <= corep::fetch_lane_bits(update_pc38);
            update_write_taken <= update_taken;
            update_write_last_valid <= update_valid;
            update_write_forward <= update_write_last_valid & (gbpt_array_bram_read_port1_next_index == gbpt_array_bram_write_index);
            update_write_old_set <= gbpt_array_bram_write_set;
        end
    end
    always_comb begin
        // check forward old set
        if (update_write_forward) begin
            update_selected_old_set = update_write_old_set;
        end
        else begin
            update_selected_old_set = gbpt_array_bram_read_port1_set;
        end

        // default old set values
        gbpt_array_bram_write_set = update_selected_old_set;

        // update lane of interest
        gbpt_array_bram_write_set[update_write_lane] = tbc_updater(update_selected_old_set[update_write_lane], update_write_taken);
    end

    // gbpt array bram
    bram_2rport_1wport #(
        .INNER_WIDTH($bits(corep::GBPT_set_t)),
        .OUTER_WIDTH(corep::GBPT_SETS)
    ) GBPT_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .port0_ren(gbpt_array_bram_read_port0_next_valid),
        .port0_rindex(gbpt_array_bram_read_port0_next_index),
        .port0_rdata(gbpt_array_bram_read_port0_set),
        .port1_ren(gbpt_array_bram_read_port1_next_valid),
        .port1_rindex(gbpt_array_bram_read_port1_next_index),
        .port1_rdata(gbpt_array_bram_read_port1_set),
        .wen_byte(gbpt_array_bram_write_byten),
        .windex(gbpt_array_bram_write_index),
        .wdata(gbpt_array_bram_write_set)
    );

endmodule