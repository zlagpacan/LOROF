/*
    Filename: mdpt.sv
    Author: zlagpacan
    Description: RTL for Memory Dependence Prediction Table
    Spec: LOROF/spec/design/mdpt.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module mdpt (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage
    input logic                     valid_REQ,
    input logic [31:0]              full_PC_REQ,
    input logic [ASID_WIDTH-1:0]    ASID_REQ,

    // RESP stage
    output logic [MDPT_ENTRIES_PER_BLOCK-1:0][MDPT_INFO_WIDTH-1:0] mdp_info_by_instr_RESP,

    // MDPT Update 0 stage
    input logic                         mdpt_update0_valid,
    input logic [31:0]                  mdpt_update0_start_full_PC,
    input logic [ASID_WIDTH-1:0]        mdpt_update0_ASID,
    input logic [MDPT_INFO_WIDTH-1:0]   mdpt_update0_mdp_info
);

    // ----------------------------------------------------------------
    // Signals:

    // REQ Stage:
    logic [MDPT_INDEX_WIDTH-1:0] hashed_index_REQ;

    // Dep Update 0:
    logic [MDPT_INDEX_WIDTH-1:0]                                mdpt_update0_hashed_index;
    logic [LOG_MDPT_ENTRIES_PER_BLOCK-1:0]                      mdpt_update0_instr;
    logic [MDPT_ENTRIES_PER_BLOCK-1:0][MDPT_INFO_WIDTH/8-1:0]   mdpt_update0_byte_mask_by_instr;

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    mdpt_index_hash MDPT_REQ_INDEX_HASH (
        .PC(full_PC_REQ),
        .ASID(ASID_REQ),
        .index(hashed_index_REQ)
    );

    // ----------------------------------------------------------------
    // Dep Update 0 Logic:

    assign mdpt_update0_instr = mdpt_update0_start_full_PC[LOG_MDPT_ENTRIES_PER_BLOCK + 1 - 1: 1];

    mdpt_index_hash MDPT_mdpt_UPDATE0_INDEX_HASH(
        .PC(mdpt_update0_start_full_PC),
        .ASID(mdpt_update0_ASID),
        .index(mdpt_update0_hashed_index)
    );

    always_comb begin
        mdpt_update0_byte_mask_by_instr = '0;
        mdpt_update0_byte_mask_by_instr[mdpt_update0_instr] = mdpt_update0_valid ? '1 : '0;
    end

    // ----------------------------------------------------------------
    // RAM Arrays:

    /////////////////////////////////////
    // BRAM Array shared over Entries: //
    /////////////////////////////////////

    bram_1rport_1wport #(
        .INNER_WIDTH(
            MDPT_ENTRIES_PER_BLOCK *
            MDPT_INFO_WIDTH
        ),
        .OUTER_WIDTH(MDPT_SETS)
    ) MDPT_BRAM_ARRAY (
        .CLK(CLK),
        .nRST(nRST),
        
        .ren(valid_REQ),
        .rindex(hashed_index_REQ),
        .rdata(mdp_info_by_instr_RESP),

        .wen_byte(mdpt_update0_byte_mask_by_instr),
        .windex(mdpt_update0_hashed_index),
        .wdata({MDPT_ENTRIES_PER_BLOCK{mdpt_update0_mdp_info}})
    );

endmodule