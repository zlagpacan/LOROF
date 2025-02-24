/*
    Filename: gbpt_index_hash.sv
    Author: zlagpacan
    Description: RTL for GBPT Index Hash Function
    Spec: LOROF/spec/design/gbpt_index_hash.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module gbpt_index_hash (
    input logic [31:0] PC,
    input logic [GH_LENGTH-1:0] GH,
    input logic [ASID_WIDTH-1:0] ASID,
    output logic [GBPT_INDEX_WIDTH+LOG_GBPT_ENTRIES_PER_BLOCK-1:0] index
);

    logic [63:0] wide_PC;
    
    assign wide_PC = PC;
    
    // xor lowest GBPT_INDEX_WIDTH PC bits with GH
        // include within-block indexing in hash
    // xor with ASID
    always_comb begin
        index = wide_PC[GBPT_INDEX_WIDTH+LOG_GBPT_ENTRIES_PER_BLOCK + 1 - 1 : 1];
        index ^= GH;
        index ^= ASID;
    end

endmodule

