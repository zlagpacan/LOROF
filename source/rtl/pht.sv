/*
    Filename: pht.sv
    Author: zlagpacan
    Description: RTL for Pattern History Table
    Spec: LOROF/spec/design/pht.md
*/

`include "corep.vh"

module pht (

    // seq
    input logic CLK,
    input logic nRST,

    // read req stage
    input logic                 read_req_valid,
    input corep::fetch_idx_t    read_req_fetch_idx,
    input corep::gh_t           read_req_gh,
    input corep::asid_t         read_req_asid,

    // read resp stage
    input corep::fetch_lane_t   read_resp_redirect_lane,

    output logic                read_resp_taken,

    // update
    input logic             update_valid,
    input corep::pc38_t     update_pc38,
    input corep::gh_t       update_gh,
    input corep::asid_t     update_asid,
    input logic             update_taken
);

    // ----------------------------------------------------------------
    // Functions:

    function corep::pht_idx_t index_hash(corep::fetch_idx_t fetch_idx, corep::gh_t gh, corep::asid_t asid);
        // low fetch index ^ low gh bits above lane ^ low reversed asid aligned to msb
        index_hash = fetch_idx;
        index_hash ^= gh[corep::GH_LENGTH-1 : corep::LOG_FETCH_LANES];
        // reversing asid from index msb
            // go down from msb until run out of pht index or asid bits
        for (int i = 0; i < (corep::LOG_PHT_SETS < corep::ASID_WIDTH ? corep::LOG_PHT_SETS : corep::ASID_WIDTH); i++) begin
            index_hash[corep::LOG_PHT_SETS-1 - i] ^= asid[i];
        end
    endfunction

    function corep::fetch_lane_t lane_hash(corep::fetch_lane_t fetch_lane, corep::gh_t gh);
        // fetch lane ^ low gh bits
        lane_hash = fetch_lane;
        lane_hash ^= gh;
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

    // pht array bram IO
        // index w/ pht index
    logic               pht_array_bram_read_port0_next_valid;
    corep::pht_idx_t    pht_array_bram_read_port0_next_index;
    corep::pht_set_t    pht_array_bram_read_port0_set;

    logic               pht_array_bram_read_port1_next_valid;
    corep::pht_idx_t    pht_array_bram_read_port1_next_index;
    corep::pht_set_t    pht_array_bram_read_port1_set;

    logic [$bits(corep::pht_set_t)/8-1:0]   pht_array_bram_write_byten;
    corep::pht_idx_t                        pht_array_bram_write_index;
    corep::pht_set_t                        pht_array_bram_write_set;

    // read resp stage
    corep::gh_t read_resp_gh;

    // update write stage
    corep::fetch_lane_t     update_write_lane;
    logic                   update_write_taken;
    logic                   update_write_last_valid;
    logic                   update_write_forward;
    corep::pht_set_t        update_write_old_set;
    corep::pht_set_t        update_selected_old_set;

    // ----------------------------------------------------------------
    // Logic:

    // read req logic
    always_comb begin
        pht_array_bram_read_port0_next_valid = read_req_valid;
        pht_array_bram_read_port0_next_index = index_hash(read_req_fetch_idx, read_req_gh, read_req_asid);
    end

    // read resp logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            read_resp_gh <= 0;
        end
        else begin
            read_resp_gh <= read_req_gh;
        end
    end
    always_comb begin
        // simple decode msb of redirect lane
        read_resp_taken = pht_array_bram_read_port0_set[lane_hash(read_resp_redirect_lane, read_resp_gh)][1];
    end

    // update logic
    always_comb begin
        pht_array_bram_read_port1_next_valid = update_valid;
        pht_array_bram_read_port1_next_index = index_hash(corep::fetch_idx_bits(update_pc38), update_gh, update_asid);
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            pht_array_bram_write_index <= 0;

            update_write_lane <= 0;
            update_write_taken <= 1'b0;
            update_write_last_valid <= 1'b0;
            update_write_forward <= 1'b0;
            update_write_old_set <= '0;
        end
        else begin
            pht_array_bram_write_index <= pht_array_bram_read_port1_next_index;

            update_write_lane <= lane_hash(corep::fetch_lane_bits(update_pc38), update_gh);
            update_write_taken <= update_taken;
            update_write_last_valid <= update_valid;
            update_write_forward <= update_write_last_valid & (pht_array_bram_read_port1_next_index == pht_array_bram_write_index);
            update_write_old_set <= pht_array_bram_write_set;
        end
    end
    always_comb begin
        pht_array_bram_write_byten = {$bits(pht_array_bram_write_byten){update_write_last_valid}};

        // check forward old set
        if (update_write_forward) begin
            update_selected_old_set = update_write_old_set;
        end
        else begin
            update_selected_old_set = pht_array_bram_read_port1_set;
        end

        // default old set values and update lane of interest
        pht_array_bram_write_set = update_selected_old_set;
        pht_array_bram_write_set[update_write_lane] = tbc_updater(update_selected_old_set[update_write_lane], update_write_taken);
    end

    // pht array bram
    bram_2rport_1wport #(
        .INNER_WIDTH($bits(corep::pht_set_t)),
        .OUTER_WIDTH(corep::PHT_SETS)
    ) pht_array_bram (
        .CLK(CLK),
        .nRST(nRST),
        .port0_ren(pht_array_bram_read_port0_next_valid),
        .port0_rindex(pht_array_bram_read_port0_next_index),
        .port0_rdata(pht_array_bram_read_port0_set),
        .port1_ren(pht_array_bram_read_port1_next_valid),
        .port1_rindex(pht_array_bram_read_port1_next_index),
        .port1_rdata(pht_array_bram_read_port1_set),
        .wen_byte(pht_array_bram_write_byten),
        .windex(pht_array_bram_write_index),
        .wdata(pht_array_bram_write_set)
    );

endmodule