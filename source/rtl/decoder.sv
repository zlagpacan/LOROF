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
    input logic         uncompressed,
    input logic [31:0]  instr32,
    input logic [7:0]   pred_info_chunk0,
    input logic [7:0]   pred_info_chunk1,

    // output interface
    output logic        is_alu_reg,
    output logic        is_alu_imm,
    output logic        is_bru,
    output logic        is_mdu,
    output logic        is_ldu,
    output logic        is_stamou,
    output logic        is_sys,

    output logic [4:0]  op5,
    
    output logic [4:0]  A_AR,
    output logic        A_is_zero,
    output logic        is_ret_ra,

    output logic [4:0]  B_AR,
    output logic        B_is_zero,

    output logic        is_reg_write,
    output logic [4:0]  dest_AR,
    output logic        is_link_ra,

    output logic [19:0] imm20,

    output logic [] mem_ordering

    output logic illegal_instr,
    output logic fetch_fault_during,
    output logic fetch_fault_after,
    output logic fetch_fault_unrecoverable
);

    // stamou can fit into op5 if invert AMO ops

endmodule