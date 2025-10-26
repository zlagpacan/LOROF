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
    output logic executable,
    output logic writeable,
    output logic readable
);

endmodule