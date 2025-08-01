/*
    Filename: decoder_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around decoder module. 
    Spec: LOROF/spec/design/decoder.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module decoder_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // input info
	input logic next_uncompressed,
	input logic [31:0] next_instr32,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_pred_info_chunk0,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_pred_info_chunk1,

    // FU select
	output logic last_is_alu_reg,
	output logic last_is_alu_imm,
	output logic last_is_bru,
	output logic last_is_mdu,
	output logic last_is_ldu,
	output logic last_is_store,
	output logic last_is_amo,
	output logic last_is_fence,
	output logic last_is_sysu,
	output logic last_is_illegal_instr,

    // op
	output logic [3:0] last_op,
	output logic last_is_reg_write,

    // A operand
	output logic [4:0] last_A_AR,
	output logic last_A_unneeded,
	output logic last_A_is_zero,
	output logic last_A_is_ret_ra,

    // B operand
	output logic [4:0] last_B_AR,
	output logic last_B_unneeded,
	output logic last_B_is_zero,

    // dest operand
	output logic [4:0] last_dest_AR,
	output logic last_dest_is_zero,
	output logic last_dest_is_link_ra,

    // imm
	output logic [19:0] last_imm20,

    // pred info out
	output logic [BTB_PRED_INFO_WIDTH-1:0] last_pred_info_out,
	output logic last_missing_pred,

    // ordering
	output logic last_flush_fetch,
	output logic last_stall_mem_read,
	output logic last_stall_mem_write,
	output logic last_wait_write_buffer,

    // faults
	output logic last_instr_yield,
	output logic last_non_branch_notif_chunk0,
	output logic last_non_branch_notif_chunk1,
	output logic last_restart_on_chunk0,
	output logic last_restart_after_chunk0,
	output logic last_restart_after_chunk1,
	output logic last_unrecoverable_fault
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // input info
	logic uncompressed;
	logic [31:0] instr32;
	logic [BTB_PRED_INFO_WIDTH-1:0] pred_info_chunk0;
	logic [BTB_PRED_INFO_WIDTH-1:0] pred_info_chunk1;

    // FU select
	logic is_alu_reg;
	logic is_alu_imm;
	logic is_bru;
	logic is_mdu;
	logic is_ldu;
	logic is_store;
	logic is_amo;
	logic is_fence;
	logic is_sysu;
	logic is_illegal_instr;

    // op
	logic [3:0] op;
	logic is_reg_write;

    // A operand
	logic [4:0] A_AR;
	logic A_unneeded;
	logic A_is_zero;
	logic A_is_ret_ra;

    // B operand
	logic [4:0] B_AR;
	logic B_unneeded;
	logic B_is_zero;

    // dest operand
	logic [4:0] dest_AR;
	logic dest_is_zero;
	logic dest_is_link_ra;

    // imm
	logic [19:0] imm20;

    // pred info out
	logic [BTB_PRED_INFO_WIDTH-1:0] pred_info_out;
	logic missing_pred;

    // ordering
	logic flush_fetch;
	logic stall_mem_read;
	logic stall_mem_write;
	logic wait_write_buffer;

    // faults
	logic instr_yield;
	logic non_branch_notif_chunk0;
	logic non_branch_notif_chunk1;
	logic restart_on_chunk0;
	logic restart_after_chunk0;
	logic restart_after_chunk1;
	logic unrecoverable_fault;

    // ----------------------------------------------------------------
    // Module Instantiation:

    decoder WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // input info
			uncompressed <= '0;
			instr32 <= '0;
			pred_info_chunk0 <= '0;
			pred_info_chunk1 <= '0;

		    // FU select
			last_is_alu_reg <= '0;
			last_is_alu_imm <= '0;
			last_is_bru <= '0;
			last_is_mdu <= '0;
			last_is_ldu <= '0;
			last_is_store <= '0;
			last_is_amo <= '0;
			last_is_fence <= '0;
			last_is_sysu <= '0;
			last_is_illegal_instr <= '0;

		    // op
			last_op <= '0;
			last_is_reg_write <= '0;

		    // A operand
			last_A_AR <= '0;
			last_A_unneeded <= '0;
			last_A_is_zero <= '0;
			last_A_is_ret_ra <= '0;

		    // B operand
			last_B_AR <= '0;
			last_B_unneeded <= '0;
			last_B_is_zero <= '0;

		    // dest operand
			last_dest_AR <= '0;
			last_dest_is_zero <= '0;
			last_dest_is_link_ra <= '0;

		    // imm
			last_imm20 <= '0;

		    // pred info out
			last_pred_info_out <= '0;
			last_missing_pred <= '0;

		    // ordering
			last_flush_fetch <= '0;
			last_stall_mem_read <= '0;
			last_stall_mem_write <= '0;
			last_wait_write_buffer <= '0;

		    // faults
			last_instr_yield <= '0;
			last_non_branch_notif_chunk0 <= '0;
			last_non_branch_notif_chunk1 <= '0;
			last_restart_on_chunk0 <= '0;
			last_restart_after_chunk0 <= '0;
			last_restart_after_chunk1 <= '0;
			last_unrecoverable_fault <= '0;
        end
        else begin

		    // input info
			uncompressed <= next_uncompressed;
			instr32 <= next_instr32;
			pred_info_chunk0 <= next_pred_info_chunk0;
			pred_info_chunk1 <= next_pred_info_chunk1;

		    // FU select
			last_is_alu_reg <= is_alu_reg;
			last_is_alu_imm <= is_alu_imm;
			last_is_bru <= is_bru;
			last_is_mdu <= is_mdu;
			last_is_ldu <= is_ldu;
			last_is_store <= is_store;
			last_is_amo <= is_amo;
			last_is_fence <= is_fence;
			last_is_sysu <= is_sysu;
			last_is_illegal_instr <= is_illegal_instr;

		    // op
			last_op <= op;
			last_is_reg_write <= is_reg_write;

		    // A operand
			last_A_AR <= A_AR;
			last_A_unneeded <= A_unneeded;
			last_A_is_zero <= A_is_zero;
			last_A_is_ret_ra <= A_is_ret_ra;

		    // B operand
			last_B_AR <= B_AR;
			last_B_unneeded <= B_unneeded;
			last_B_is_zero <= B_is_zero;

		    // dest operand
			last_dest_AR <= dest_AR;
			last_dest_is_zero <= dest_is_zero;
			last_dest_is_link_ra <= dest_is_link_ra;

		    // imm
			last_imm20 <= imm20;

		    // pred info out
			last_pred_info_out <= pred_info_out;
			last_missing_pred <= missing_pred;

		    // ordering
			last_flush_fetch <= flush_fetch;
			last_stall_mem_read <= stall_mem_read;
			last_stall_mem_write <= stall_mem_write;
			last_wait_write_buffer <= wait_write_buffer;

		    // faults
			last_instr_yield <= instr_yield;
			last_non_branch_notif_chunk0 <= non_branch_notif_chunk0;
			last_non_branch_notif_chunk1 <= non_branch_notif_chunk1;
			last_restart_on_chunk0 <= restart_on_chunk0;
			last_restart_after_chunk0 <= restart_after_chunk0;
			last_restart_after_chunk1 <= restart_after_chunk1;
			last_unrecoverable_fault <= unrecoverable_fault;
        end
    end

endmodule