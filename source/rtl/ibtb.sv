/*
    Filename: ibtb.sv
    Author: zlagpacan
    Description: RTL for Indirect Branch Target Buffer
    Spec: LOROF/spec/design/ibtb.md
*/

`include "corep.vh"

module ibtb (

    // seq
    input logic CLK,
    input logic nRST,

    // read
    input corep::pc38_t     read_src_pc38,
    input corep::ibtb_gh_t  read_ibtb_gh,
    input corep::asid_t     read_asid,

    output corep::pc38_t    read_tgt_pc38,

    // update
    input logic             update_valid,
    input corep::pc38_t     update_src_pc38,
    input corep::ibtb_gh_t  update_ibtb_gh,
    input corep::asid_t     update_asid,
    input corep::pc38_t     update_tgt_pc38
);

    // ----------------------------------------------------------------
    // Functions:

    function corep::ibtb_idx_t index_hash(corep::pc38_t pc38, corep::ibtb_gh_t ibtb_gh, corep::asid_t asid);
        // low pc38 (including lane) ^ ibtb gh (low gh) ^ low asid
        index_hash = pc38;
        index_hash ^= ibtb_gh;
        index_hash ^= asid;
    endfunction

    // ----------------------------------------------------------------
    // Signals:

    // ibtb array distram IO
        // index w/ ibtb index
    corep::ibtb_idx_t   ibtb_array_distram_read_index;
    corep::pc38_t       ibtb_array_distram_read_data;

    logic               ibtb_array_distram_write_valid;
    corep::ibtb_idx_t   ibtb_array_distram_write_index;
    corep::pc38_t       ibtb_array_distram_write_data;

    // ----------------------------------------------------------------
    // Logic:

    // read logic
    always_comb begin
        ibtb_array_distram_read_index = index_hash(read_src_pc38, read_ibtb_gh, read_asid);
        
        read_tgt_pc38 = ibtb_array_distram_read_data;
    end

    // write logic
    always_comb begin
        ibtb_array_distram_write_valid = update_valid;
        ibtb_array_distram_write_index = index_hash(update_src_pc38, update_ibtb_gh, update_asid);
        ibtb_array_distram_write_data = update_tgt_pc38;
    end

    // ibtb array distram
    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::pc38_t)),
        .OUTER_WIDTH(corep::IBTB_ENTRIES)
    ) IBTB_ARRAY_DISTRAM (
        .CLK(CLK),
        .rindex(ibtb_array_distram_read_index),
        .rdata(ibtb_array_distram_read_data),
        .wen(ibtb_array_distram_write_valid),
        .windex(ibtb_array_distram_write_index),
        .wdata(ibtb_array_distram_write_data)
    );

endmodule