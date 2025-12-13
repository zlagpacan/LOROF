/*
    Filename: btb_tag_hash.sv
    Author: zlagpacan
    Description: RTL for BTB Tag Hash Function
    Spec: LOROF/spec/design/btb_tag_hash.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module btb_tag_hash (
    input logic [31:0] PC,
    input logic [ASID_WIDTH-1:0] ASID,
    output logic [BTB_TAG_WIDTH-1:0] tag
);

    logic [63:0] wide_PC;
    
    assign wide_PC = PC;
    
    // xor lowest BTB_TAG_WIDTH tag bits with next lowest BTB_TAG_WIDTH tag bits
    // xor with ASID
    always_comb begin
        tag = wide_PC[BTB_TAG_WIDTH + BTB_INDEX_WIDTH + LOG_BTB_NWAY_ENTRIES_PER_BLOCK + 1 - 1 : BTB_INDEX_WIDTH + LOG_BTB_NWAY_ENTRIES_PER_BLOCK + 1];
        tag ^= wide_PC[2*BTB_TAG_WIDTH + BTB_INDEX_WIDTH + LOG_BTB_NWAY_ENTRIES_PER_BLOCK + 1 - 1 : BTB_TAG_WIDTH + BTB_INDEX_WIDTH + LOG_BTB_NWAY_ENTRIES_PER_BLOCK + 1];
        tag ^= ASID;
    end

endmodule

