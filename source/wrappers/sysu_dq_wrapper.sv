/*
    Filename: sysu_dq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around sysu_dq module. 
    Spec: LOROF/spec/design/sysu_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter SYSU_DQ_ENTRIES = core_types_pkg::SYSU_DQ_ENTRIES;

module sysu_dq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
	input logic [3:0] next_dispatch_attempt_by_way,
	input logic [3:0] next_dispatch_valid_by_way,
	input logic [3:0][3:0] next_dispatch_op_by_way,
	input logic [3:0][11:0] next_dispatch_imm12_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_way,
	input logic [3:0] next_dispatch_A_ready_by_way,
	input logic [3:0] next_dispatch_A_is_zero_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_B_PR_by_way,
	input logic [3:0] next_dispatch_B_ready_by_way,
	input logic [3:0] next_dispatch_B_is_zero_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_way,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_way,

    // op dispatch feedback
	output logic [3:0] last_dispatch_ack_by_way,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // op launch to sysu
	output logic last_sysu_launch_valid,
	output logic last_sysu_launch_killed,
	output logic [3:0] last_sysu_launch_op,
	output logic [11:0] last_sysu_launch_imm12,
	output logic [LOG_PR_COUNT-1:0] last_sysu_launch_A_PR,
	output logic last_sysu_launch_A_is_zero,
	output logic [LOG_PR_COUNT-1:0] last_sysu_launch_B_PR,
	output logic last_sysu_launch_B_is_zero,
	output logic [LOG_PR_COUNT-1:0] last_sysu_launch_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_sysu_launch_ROB_index,

    // sysu launch feedback
	input logic next_sysu_launch_ready,

    // ROB kill
	input logic next_rob_kill_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_abs_head_index,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_rel_kill_younger_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op dispatch by way
	logic [3:0] dispatch_attempt_by_way;
	logic [3:0] dispatch_valid_by_way;
	logic [3:0][3:0] dispatch_op_by_way;
	logic [3:0][11:0] dispatch_imm12_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_way;
	logic [3:0] dispatch_A_ready_by_way;
	logic [3:0] dispatch_A_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_B_PR_by_way;
	logic [3:0] dispatch_B_ready_by_way;
	logic [3:0] dispatch_B_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // op launch to sysu
	logic sysu_launch_valid;
	logic sysu_launch_killed;
	logic [3:0] sysu_launch_op;
	logic [11:0] sysu_launch_imm12;
	logic [LOG_PR_COUNT-1:0] sysu_launch_A_PR;
	logic sysu_launch_A_is_zero;
	logic [LOG_PR_COUNT-1:0] sysu_launch_B_PR;
	logic sysu_launch_B_is_zero;
	logic [LOG_PR_COUNT-1:0] sysu_launch_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] sysu_launch_ROB_index;

    // sysu launch feedback
	logic sysu_launch_ready;

    // ROB kill
	logic rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	sysu_dq #(
		.SYSU_DQ_ENTRIES(SYSU_DQ_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op dispatch by way
			dispatch_attempt_by_way <= '0;
			dispatch_valid_by_way <= '0;
			dispatch_op_by_way <= '0;
			dispatch_imm12_by_way <= '0;
			dispatch_A_PR_by_way <= '0;
			dispatch_A_ready_by_way <= '0;
			dispatch_A_is_zero_by_way <= '0;
			dispatch_B_PR_by_way <= '0;
			dispatch_B_ready_by_way <= '0;
			dispatch_B_is_zero_by_way <= '0;
			dispatch_dest_PR_by_way <= '0;
			dispatch_ROB_index_by_way <= '0;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // op launch to sysu
			last_sysu_launch_valid <= '0;
			last_sysu_launch_killed <= '0;
			last_sysu_launch_op <= '0;
			last_sysu_launch_imm12 <= '0;
			last_sysu_launch_A_PR <= '0;
			last_sysu_launch_A_is_zero <= '0;
			last_sysu_launch_B_PR <= '0;
			last_sysu_launch_B_is_zero <= '0;
			last_sysu_launch_dest_PR <= '0;
			last_sysu_launch_ROB_index <= '0;

		    // sysu launch feedback
			sysu_launch_ready <= '0;

		    // ROB kill
			rob_kill_valid <= '0;
			rob_kill_abs_head_index <= '0;
			rob_kill_rel_kill_younger_index <= '0;
        end
        else begin

		    // op dispatch by way
			dispatch_attempt_by_way <= next_dispatch_attempt_by_way;
			dispatch_valid_by_way <= next_dispatch_valid_by_way;
			dispatch_op_by_way <= next_dispatch_op_by_way;
			dispatch_imm12_by_way <= next_dispatch_imm12_by_way;
			dispatch_A_PR_by_way <= next_dispatch_A_PR_by_way;
			dispatch_A_ready_by_way <= next_dispatch_A_ready_by_way;
			dispatch_A_is_zero_by_way <= next_dispatch_A_is_zero_by_way;
			dispatch_B_PR_by_way <= next_dispatch_B_PR_by_way;
			dispatch_B_ready_by_way <= next_dispatch_B_ready_by_way;
			dispatch_B_is_zero_by_way <= next_dispatch_B_is_zero_by_way;
			dispatch_dest_PR_by_way <= next_dispatch_dest_PR_by_way;
			dispatch_ROB_index_by_way <= next_dispatch_ROB_index_by_way;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= dispatch_ack_by_way;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // op launch to sysu
			last_sysu_launch_valid <= sysu_launch_valid;
			last_sysu_launch_killed <= sysu_launch_killed;
			last_sysu_launch_op <= sysu_launch_op;
			last_sysu_launch_imm12 <= sysu_launch_imm12;
			last_sysu_launch_A_PR <= sysu_launch_A_PR;
			last_sysu_launch_A_is_zero <= sysu_launch_A_is_zero;
			last_sysu_launch_B_PR <= sysu_launch_B_PR;
			last_sysu_launch_B_is_zero <= sysu_launch_B_is_zero;
			last_sysu_launch_dest_PR <= sysu_launch_dest_PR;
			last_sysu_launch_ROB_index <= sysu_launch_ROB_index;

		    // sysu launch feedback
			sysu_launch_ready <= next_sysu_launch_ready;

		    // ROB kill
			rob_kill_valid <= next_rob_kill_valid;
			rob_kill_abs_head_index <= next_rob_kill_abs_head_index;
			rob_kill_rel_kill_younger_index <= next_rob_kill_rel_kill_younger_index;
        end
    end

endmodule