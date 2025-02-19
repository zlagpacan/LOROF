/*
    Filename: btb_tag_hash.sv
    Author: zlagpacan
    Description: RTL for BTB Tag Hash Function
    Spec: LOROF/spec/design/btb_tag_hash.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb_tag_hash (
    input logic [31:0] PC,
    input logic [8:0] ASID,
    output logic [BTB_TAG_WIDTH-1:0] tag
);

    // // v1: xor lowest 4 w/ next lowest 4 above BTB index bits
    // assign tag = 
    //     PC30[LOG_BTB_ENTRIES+4-1:LOG_BTB_ENTRIES]
    //     ^
    //     PC30[LOG_BTB_ENTRIES+8-1:LOG_BTB_ENTRIES+4] 
    // ;

    // v2: 
        // xor lowest BTB_TAG_WIDTH tag bits with next lowest BTB_TAG_WIDTH tag bits
        // xor with ASID  
    always_comb begin
        tag = PC[BTB_TAG_WIDTH + BTB_INDEX_WIDTH+1 - 1:BTB_INDEX_WIDTH+1];
        tag ^= PC[2*BTB_TAG_WIDTH + BTB_INDEX_WIDTH+1 - 1:BTB_TAG_WIDTH + BTB_INDEX_WIDTH+1];
        tag ^= ASID;
    end

endmodule

