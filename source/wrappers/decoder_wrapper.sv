/*
    Filename: decoder_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around decoder module. 
    Spec: LOROF/spec/design/decoder.md
*/

`timescale 1ns/100ps

`include "corep.vh"
`include "instrp.vh"

module decoder_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

    // environment info
	input corep::exec_mode_t next_env_exec_mode,
	input logic next_env_trap_sfence,
	input logic next_env_trap_wfi,
	input logic next_env_trap_sret,
	input logic next_env_menvconfig_FIOM,
	input logic next_env_senvconfig_FIOM,

    // instr info
	input corep::fetch4B_t next_fetch4B,
	input logic next_btb_hit,
	input logic next_redirect_taken,
	input logic next_mid_instr_redirect,

    // FU select
	output logic last_is_alu_reg,
	output logic last_is_alu_imm,
	output logic last_is_bru,
	output logic last_is_mdu,
	output logic last_is_fpu,
	output logic last_is_ldu,
	output logic last_is_store,
	output logic last_is_amo,
	output logic last_is_fence,
	output logic last_is_sysu,
	output logic last_is_illegal_instr,

    // op
	output logic [3:0] last_op,
	output logic last_dest_write,
	output logic last_has_freg,
	output logic last_trigger_wfr,
	output logic last_strong_want_checkpoint,
	output logic last_weak_want_checkpoint,

    // A operand
	output corep::ar6_t last_A_ar6,
	output logic last_A_unneeded,
	output logic last_A_is_zero,
	output logic last_A_is_ret_ra,

    // B operand
	output corep::ar6_t last_B_ar6,
	output logic last_B_unneeded,
	output logic last_B_is_zero,

    // C operand
	output corep::ar5_t last_C_ar5,

    // dest operand
	output corep::ar6_t last_dest_ar6,
	output logic last_dest_is_zero,
	output logic last_dest_is_link_ra,

    // imm
	output logic [19:0] last_imm20,

    // ordering
	output logic last_amo_is_double,
	output logic last_mem_aq,
	output logic last_io_aq,
	output logic last_mem_rl,
	output logic last_io_rl,

    // yielding
	output logic last_instr_yield,
	output logic last_restart_valid,
	output logic [1:0] last_restart_pc38_offset
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // environment info
	corep::exec_mode_t env_exec_mode;
	logic env_trap_sfence;
	logic env_trap_wfi;
	logic env_trap_sret;
	logic env_menvconfig_FIOM;
	logic env_senvconfig_FIOM;

    // instr info
	corep::fetch4B_t fetch4B;
	logic btb_hit;
	logic redirect_taken;
	logic mid_instr_redirect;

    // FU select
	logic is_alu_reg;
	logic is_alu_imm;
	logic is_bru;
	logic is_mdu;
	logic is_fpu;
	logic is_ldu;
	logic is_store;
	logic is_amo;
	logic is_fence;
	logic is_sysu;
	logic is_illegal_instr;

    // op
	logic [3:0] op;
	logic dest_write;
	logic has_freg;
	logic trigger_wfr;
	logic strong_want_checkpoint;
	logic weak_want_checkpoint;

    // A operand
	corep::ar6_t A_ar6;
	logic A_unneeded;
	logic A_is_zero;
	logic A_is_ret_ra;

    // B operand
	corep::ar6_t B_ar6;
	logic B_unneeded;
	logic B_is_zero;

    // C operand
	corep::ar5_t C_ar5;

    // dest operand
	corep::ar6_t dest_ar6;
	logic dest_is_zero;
	logic dest_is_link_ra;

    // imm
	logic [19:0] imm20;

    // ordering
	logic amo_is_double;
	logic mem_aq;
	logic io_aq;
	logic mem_rl;
	logic io_rl;

    // yielding
	logic instr_yield;
	logic restart_valid;
	logic [1:0] restart_pc38_offset;

    // ----------------------------------------------------------------
    // Module Instantiation:

	decoder #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // environment info
			env_exec_mode <= '0;
			env_trap_sfence <= '0;
			env_trap_wfi <= '0;
			env_trap_sret <= '0;
			env_menvconfig_FIOM <= '0;
			env_senvconfig_FIOM <= '0;

		    // instr info
			fetch4B <= '0;
			btb_hit <= '0;
			redirect_taken <= '0;
			mid_instr_redirect <= '0;

		    // FU select
			last_is_alu_reg <= '0;
			last_is_alu_imm <= '0;
			last_is_bru <= '0;
			last_is_mdu <= '0;
			last_is_fpu <= '0;
			last_is_ldu <= '0;
			last_is_store <= '0;
			last_is_amo <= '0;
			last_is_fence <= '0;
			last_is_sysu <= '0;
			last_is_illegal_instr <= '0;

		    // op
			last_op <= '0;
			last_dest_write <= '0;
			last_has_freg <= '0;
			last_trigger_wfr <= '0;
			last_strong_want_checkpoint <= '0;
			last_weak_want_checkpoint <= '0;

		    // A operand
			last_A_ar6 <= '0;
			last_A_unneeded <= '0;
			last_A_is_zero <= '0;
			last_A_is_ret_ra <= '0;

		    // B operand
			last_B_ar6 <= '0;
			last_B_unneeded <= '0;
			last_B_is_zero <= '0;

		    // C operand
			last_C_ar5 <= '0;

		    // dest operand
			last_dest_ar6 <= '0;
			last_dest_is_zero <= '0;
			last_dest_is_link_ra <= '0;

		    // imm
			last_imm20 <= '0;

		    // ordering
			last_amo_is_double <= '0;
			last_mem_aq <= '0;
			last_io_aq <= '0;
			last_mem_rl <= '0;
			last_io_rl <= '0;

		    // yielding
			last_instr_yield <= '0;
			last_restart_valid <= '0;
			last_restart_pc38_offset <= '0;
        end
        else begin

		    // environment info
			env_exec_mode <= next_env_exec_mode;
			env_trap_sfence <= next_env_trap_sfence;
			env_trap_wfi <= next_env_trap_wfi;
			env_trap_sret <= next_env_trap_sret;
			env_menvconfig_FIOM <= next_env_menvconfig_FIOM;
			env_senvconfig_FIOM <= next_env_senvconfig_FIOM;

		    // instr info
			fetch4B <= next_fetch4B;
			btb_hit <= next_btb_hit;
			redirect_taken <= next_redirect_taken;
			mid_instr_redirect <= next_mid_instr_redirect;

		    // FU select
			last_is_alu_reg <= is_alu_reg;
			last_is_alu_imm <= is_alu_imm;
			last_is_bru <= is_bru;
			last_is_mdu <= is_mdu;
			last_is_fpu <= is_fpu;
			last_is_ldu <= is_ldu;
			last_is_store <= is_store;
			last_is_amo <= is_amo;
			last_is_fence <= is_fence;
			last_is_sysu <= is_sysu;
			last_is_illegal_instr <= is_illegal_instr;

		    // op
			last_op <= op;
			last_dest_write <= dest_write;
			last_has_freg <= has_freg;
			last_trigger_wfr <= trigger_wfr;
			last_strong_want_checkpoint <= strong_want_checkpoint;
			last_weak_want_checkpoint <= weak_want_checkpoint;

		    // A operand
			last_A_ar6 <= A_ar6;
			last_A_unneeded <= A_unneeded;
			last_A_is_zero <= A_is_zero;
			last_A_is_ret_ra <= A_is_ret_ra;

		    // B operand
			last_B_ar6 <= B_ar6;
			last_B_unneeded <= B_unneeded;
			last_B_is_zero <= B_is_zero;

		    // C operand
			last_C_ar5 <= C_ar5;

		    // dest operand
			last_dest_ar6 <= dest_ar6;
			last_dest_is_zero <= dest_is_zero;
			last_dest_is_link_ra <= dest_is_link_ra;

		    // imm
			last_imm20 <= imm20;

		    // ordering
			last_amo_is_double <= amo_is_double;
			last_mem_aq <= mem_aq;
			last_io_aq <= io_aq;
			last_mem_rl <= mem_rl;
			last_io_rl <= io_rl;

		    // yielding
			last_instr_yield <= instr_yield;
			last_restart_valid <= restart_valid;
			last_restart_pc38_offset <= restart_pc38_offset;
        end
    end

endmodule