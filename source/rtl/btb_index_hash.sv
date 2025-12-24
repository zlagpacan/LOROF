/*
    Filename: btb_index_hash.sv
    Author: zlagpacan
    Description: RTL for BTB Index Hash Function
    Spec: LOROF/spec/design/btb_index_hash.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module btb_index_hash (
    input logic [31:0] PC,
    input logic [ASID_WIDTH-1:0] ASID,
    output logic [BTB_INDEX_WIDTH-1:0] index
);

    logic [63:0] wide_PC;
    
    assign wide_PC = PC;
    
    // xor lowest BTB_INDEX_WIDTH PC bits with ASID
        // beyond the bits associated with selecting the BTB entry purely by PC
    always_comb begin
        index = wide_PC[BTB_INDEX_WIDTH+LOG_BTB_NWAY_ENTRIES_PER_BLOCK+1-1 : LOG_BTB_NWAY_ENTRIES_PER_BLOCK+1];
        index ^= ASID;
    end

endmodule

