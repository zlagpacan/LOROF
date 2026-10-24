/*
    Filename: decoder.sv
    Author: zlagpacan
    Description: RTL for Decoder
    Spec: LOROF/spec/design/decoder.md
*/

// TODO: update for RV64IMAFDC
// TODO: update for floating point
    // fpnew input coding
    // tell if instr includes freg
        // not strictly is_fpu as fp loads and stores have freg's
// TODO: decode if want checkpoint

`include "core_types.vh"

module decoder (

    // environment info
    input corep::exec_mode_t    env_exec_mode,
    input logic                 env_trap_sfence,
    input logic                 env_trap_wfi,
    input logic                 env_trap_sret,
    input logic                 env_menvconfig_FIOM,
    input logic                 env_senvconfig_FIOM,

    // instr info
    input corep::fetch4B_t  fetch4B,
    input logic             btb_hit,
    input lgoic             redirect_taken,
    input logic             mid_instr_redirect,
    input corep::mdp_t      mdp,

    // FU select
    output logic is_alu_reg,
    output logic is_alu_imm,
    output logic is_bru,
    output logic is_mdu,
    output logic is_fpu,
    output logic is_ldu,
    output logic is_stamofu,
    output logic is_sysu,
    output logic is_illegal_instr,

    // op
    output logic [3:0]  op,
    output logic        dest_write,
    output logic        has_freg,
    output logic        has_imm,
    output logic        wfr,
    
    // A operand
    output logic [4:0]  A_AR,
    output logic        A_unneeded,
    output logic        A_is_zero,
    output logic        A_is_ret_ra,

    // B operand
    output logic [4:0]  B_AR,
    output logic        B_unneeded,
    output logic        B_is_zero,

    // dest operand
    output logic [4:0]  dest_AR,
    output logic        dest_is_zero,
    output logic        dest_is_link_ra,

    // imm
    output logic [19:0] imm20,

    // ordering
    output logic mem_aq,
    output logic io_aq,
    output logic mem_rl,
    output logic io_rl,

    // yielding
    output logic        instr_yield,
    output logic        restart_valid,
    output logic [1:0]  restart_pc38_offset,
    output logic        unrecoverable_fault
);

    // ----------------------------------------------------------------
    // Signals:



endmodule