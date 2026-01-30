/*
    Filename: mdpt.sv
    Author: zlagpacan
    Description: RTL for Memory Dependence Prediction Table
    Spec: LOROF/spec/design/mdpt.md
*/

`include "corep.vh"

module mdpt (

    // seq
    input logic CLK,
    input logic nRST,

    // arch state
    input corep::ASID_t arch_asid,

    // read req stage
    input logic                 read_req_valid,
    input corep::fetch_idx_t    read_req_fetch_index,

    // read resp stage
    output corep::MDPT_set_t    read_resp_mdp_by_lane,

    // update
    input logic             update_valid,
    input corep::PC38_t     update_pc38,
    input corep::MDP_t      update_mdp
);

    // ----------------------------------------------------------------
    // Functions:

    function corep::MDPT_idx_t index_hash(corep::fetch_idx_t fetch_index, corep::ASID_t asid);
        // low fetch index ^ low asid
        index_hash = fetch_index;
        index_hash ^= asid;
    endfunction

    // ----------------------------------------------------------------
    // Signals:

    // mdpt array bram IO
    logic               mdpt_array_bram_read_next_valid;
    corep::MDPT_idx_t   mdpt_array_bram_read_next_index;
    corep::MDPT_set_t   mdpt_array_bram_read_set;

    logic [corep::FETCH_LANES-1:0][$bits(corep::MDPT_entry_t)/8-1:0]    mdpt_array_bram_write_byten;
    corep::MDPT_idx_t                                                   mdpt_array_bram_write_index;
    corep::MDPT_set_t                                                   mdpt_array_bram_write_set;

    // update indexing
    corep::MDPT_idx_t       update_index;
    corep::fetch_lane_t     update_lane;

    // ----------------------------------------------------------------
    // Logic:

    // read logic
    always_comb begin
        mdpt_array_bram_read_next_valid = read_req_valid;
        mdpt_array_bram_read_next_index = index_hash(read_req_fetch_index, arch_asid);

        read_resp_mdp_by_lane = mdpt_array_bram_read_set;
    end

    // write logic
    always_comb begin
        update_index = index_hash(corep::fetch_idx_bits(update_pc38), arch_asid);
        update_lane = corep::fetch_lane_bits(update_pc38);

        mdpt_array_bram_write_byten = '0;
        if (update_valid) begin
            mdpt_array_bram_write_byten[update_lane] = '1;
        end
        mdpt_array_bram_write_index = update_index;
        for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin
            mdpt_array_bram_write_set[lane] = update_mdp;
        end
    end

    // mdpt array bram
    bram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::MDPT_set_t)),
        .OUTER_WIDTH(corep::MDPT_SETS)
    ) MDPT_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(mdpt_array_bram_read_next_valid),
        .rindex(mdpt_array_bram_read_next_index),
        .rdata(mdpt_array_bram_read_set),
        .wen_byte(mdpt_array_bram_write_byten),
        .windex(mdpt_array_bram_write_index),
        .wdata(mdpt_array_bram_write_set)
    );

endmodule