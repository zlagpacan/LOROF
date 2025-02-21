/*
    Filename: lht.sv
    Author: zlagpacan
    Description: RTL for Local History Table
    Spec: LOROF/spec/design/lht.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lht (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage
    input logic                     valid_REQ,
    input logic [31:0]              full_PC_REQ,
    input logic [ASID_WIDTH-1:0]    ASID_REQ,

    // RESP stage
    output logic [LHT_ENTRIES_PER_BLOCK-1:0][LH_LENGTH-1:0] lh_by_instr_RESP,

    // Update 0 stage
    input logic                     update0_valid,
    input logic [31:0]              update0_start_full_PC,
    input logic [ASID_WIDTH-1:0]    update0_ASID,
    input logic [LH_LENGTH-1:0]     update0_lh
);

    // ----------------------------------------------------------------
    // Signals:

    // REQ Stage:
    logic [LHT_INDEX_WIDTH-1:0] hashed_index_REQ;

    // RESP Stage:

    // Update 0:
    logic [LHT_INDEX_WIDTH-1:0]                         update0_hashed_index;
    logic [LOG_LHT_ENTRIES_PER_BLOCK-1:0]               update0_instr;
    logic [LHT_ENTRIES_PER_BLOCK-1:0][LH_LENGTH/8-1:0]  update0_byte_mask_by_instr;

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    lht_index_hash LHT_REQ_INDEX_HASH (
        .PC(full_PC_REQ),
        .ASID(ASID_REQ),
        .index(hashed_index_REQ)
    );

    // ----------------------------------------------------------------
    // Update 0 Logic:

    assign update0_instr = update0_start_full_PC[LOG_LHT_ENTRIES_PER_BLOCK+1-1 : 1];

    lht_index_hash LHT_UPDATE_INDEX_HASH (
        .PC(update0_start_full_PC),
        .ASID(update0_ASID),
        .index(update0_hashed_index)
    );

    always_comb begin
        update0_byte_mask_by_instr = '0;
        update0_byte_mask_by_instr[update0_instr] = update0_valid ? '1 : '0;
    end
    
    // ----------------------------------------------------------------
    // RAM Arrays:

    /////////////////////////////////////
    // BRAM Array shared over Instr's: //
    /////////////////////////////////////

    bram_1rport_1wport #(
        .INNER_WIDTH(
            LHT_ENTRIES_PER_BLOCK *
            LH_LENGTH
        ),
        .OUTER_WIDTH(LHT_SETS)
    ) LH_BRAM_ARRAY (
        .CLK(CLK),
        .nRST(nRST),
        
        .ren(valid_REQ),
        .rindex(hashed_index_REQ),
        .rdata(lh_by_instr_RESP),

        .wen_byte(update0_byte_mask_by_instr),
        .windex(update0_hashed_index),
        .wdata({LHT_ENTRIES_PER_BLOCK{update0_lh}})
    );

endmodule