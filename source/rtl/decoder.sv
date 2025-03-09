/*
    Filename: decoder.sv
    Author: zlagpacan
    Description: RTL for Decoder
    Spec: LOROF/spec/design/decoder.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module free_list (

    // input interface
    input logic uncompressed,
    input logic [31:0] instr32,
    input logic [7:0] pred_info_chunk0,
    input logic [7:0] pred_info_chunk1,

    // output interface
    output logic valid_alu_reg,
    output logic valid_mdu,
    output logic [19:0] imm20,
    output logic illegal_instr,
    output logic fetch_fault_during,
    output logic fetch_fault_after
);

endmodule