/*
    Filename: lht_index_hash.sv
    Author: zlagpacan
    Description: RTL for LHT Index Hash Function
    Spec: LOROF/spec/design/lht_index_hash.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lht_index_hash (
    input logic [31:0] PC,
    input logic [ASID_WIDTH-1:0] ASID,
    output logic [LHT_INDEX_WIDTH-1:0] index
);

    logic [63:0] wide_PC;
    
    assign wide_PC = PC;
    
    // xor lowest LHT_INDEX_WIDTH PC bits with ASID
    always_comb begin
        index = wide_PC[LHT_INDEX_WIDTH + LHT_ENTRIES_PER_BLOCK + 1 - 1 : LHT_ENTRIES_PER_BLOCK + 1];
        index ^= ASID;
    end

endmodule

