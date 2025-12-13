/*
    Filename: mem_map.sv
    Author: zlagpacan
    Description: RTL for Memory Map
    Spec: LOROF/spec/design/mem_map.md
*/

`include "system_types_pkg.vh"
import system_types_pkg::*;

module mem_map (

    // input
    input logic [PPN_WIDTH-1:0] ppn,

    // output
    output logic valid,
    output logic is_mem
);

    logic is_io;

    // io region:
        // addresses:
            // [0x0_0000_FFFF : 0x0_0000_0000]
            // [33:16] = 18'b000000000000000000
            // [15:0] = 16'bxxxxxxxxxxxxxxxx
        // non-cacheable, non-idempotent

    assign is_io = ppn[33:16] == '0;

    // regular mem region:
        // addresses:
            // [0x2_FFFF_FFFF : 0x2_0000_0000]
            // [33:32] = 2'b10
            // [31:0] = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
        // cacheable, idempotent

    assign is_mem = ppn[33:32] == 2'b10;

    // valid region:
        // mem region + io region

    assign valid = is_mem | is_io;

endmodule