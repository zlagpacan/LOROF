/*
    Filename: decoder.sv
    Author: zlagpacan
    Description: RTL for Decoder
    Spec: LOROF/spec/design/decoder.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module decoder (

    // input info
    input logic                             uncompressed,
    input logic [31:0]                      instr32,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   pred_info_chunk0,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   pred_info_chunk1,

    // FU select
    output logic    is_alu_reg,
    output logic    is_alu_imm,
    output logic    is_bru,
    output logic    is_mdu,
    output logic    is_ldu,
    output logic    is_stamou,
    output logic    is_sys,
    output logic    is_illegal_instr,

    // op
    output logic [4:0]  op5,
    
    // A operand
    output logic [4:0]  A_AR,
    output logic        A_is_zero,
    output logic        is_ret_ra,

    // B operand
    output logic [4:0]  B_AR,
    output logic        B_is_zero,

    // dest operand
    output logic        is_reg_write,
    output logic [4:0]  dest_AR,
    output logic        is_link_ra,

    // imm
    output logic [19:0] imm20,

    // faults
    output logic instr_yield,
    output logic non_branch_notif,
    output logic fault_after_chunk0,
    output logic fault_after_chunk1,
    output logic fault_unrecoverable
);

    // stamou can fit into op5 if invert AMO ops

endmodule