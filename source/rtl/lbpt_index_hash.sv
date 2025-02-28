/*
    Filename: lbpt_index_hash.sv
    Author: zlagpacan
    Description: RTL for LBPT Index Hash Function
    Spec: LOROF/spec/design/lbpt_index_hash.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lbpt_index_hash (
    input logic [31:0] PC,
    input logic [LH_LENGTH-1:0] LH,
    input logic [ASID_WIDTH-1:0] ASID,
    output logic [LBPT_INDEX_WIDTH+LOG_LBPT_ENTRIES_PER_BLOCK-1:0] index
);

    logic [63:0] wide_PC;
    
    assign wide_PC = PC;
    
    // xor lowest LBPT_INDEX_WIDTH PC bits with LH
        // include within-block indexing in hash
    // xor with ASID
    always_comb begin
        index = wide_PC[LBPT_INDEX_WIDTH+LOG_LBPT_ENTRIES_PER_BLOCK + 1 - 1 : 1];
        index ^= LH;
        index ^= ASID;
    end

endmodule

