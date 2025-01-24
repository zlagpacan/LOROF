/*
    Filename: btb_tag_hash.sv
    Author: zlagpacan
    Description: RTL for BTB Target Hash Function
    Spec: LOROF/spec/design/btb.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb_tag_hash (
    input logic [29:0] PC30,
    output logic [BTB_TAG_WIDTH-1:0] tag
);

    // v1: xor lowest 4 w/ next lowest 4 above BTB index bits
    assign tag = 
        PC30[LOG_BTB_ENTRIES+4-1:LOG_BTB_ENTRIES]
        ^
        PC30[LOG_BTB_ENTRIES+8-1:LOG_BTB_ENTRIES+4] 
    ;

endmodule

