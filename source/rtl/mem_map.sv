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
    input logic [PPN_WIDTH-1:0] PPN,

    // output
    output logic DRAM,
    output logic ROM,
    output logic IO
);

    // DRAM region:
        // 2 GB
        // addresses:
            // [0x3_FFFF_FFFF : 0x3_8000_0000]
            // [33:31] = 3'b111
            // [30:0] = 31'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
        // attributes:
            // executable
            // writeable
            // readable
            // cacheable
            // idempotent
    assign DRAM = PPN[33-PO_WIDTH:31-PO_WIDTH] == 3'b111;

    // ROM region:
        // 64 KB
        // addresses:
            // [0x0_0001_FFFF : 0x0_0001_0000]
            // [33:16] = 18'b00000000000000001
            // [15:0] = 16'bxxxxxxxxxxxxxxxx
        // attributes:
            // executable
            // NOT writeable
            // readable
            // cacheable
            // idempotent
    assign ROM = PPN[33-PO_WIDTH:16-PO_WIDTH] == 18'b00000000000000001;

    // IO region:
        // 64 KB
        // addresses:
            // [0x0_0000_FFFF : 0x0_0000_0000]
            // [33:16] = 18'b000000000000000000
            // [15:0] = 16'bxxxxxxxxxxxxxxxx
        // attributes:
            // NOT executable
            // writeable
            // readable
            // NOT cacheable
            // NOT idempotent
    assign IO = PPN[33-PO_WIDTH:16-PO_WIDTH] == 18'b000000000000000000;

endmodule