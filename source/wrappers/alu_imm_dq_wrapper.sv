/*
    Filename: alu_imm_dq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_imm_dq module. 
    Spec: LOROF/spec/design/alu_imm_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_dq_wrapper (

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
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_way,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_way,

    // op dispatch feedback
	output logic [3:0] last_dispatch_ack_by_way,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // op enqueue to issue queue
	output logic last_iq_enq_valid,
	output logic [3:0] last_iq_enq_op,
	output logic [11:0] last_iq_enq_imm12,
	output logic [LOG_PR_COUNT-1:0] last_iq_enq_A_PR,
	output logic last_iq_enq_A_ready,
	output logic last_iq_enq_A_is_zero,
	output logic [LOG_PR_COUNT-1:0] last_iq_enq_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_iq_enq_ROB_index,

    // issue queue enqueue feedback
	input logic next_iq_enq_ready
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
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // op enqueue to issue queue
	logic iq_enq_valid;
	logic [3:0] iq_enq_op;
	logic [11:0] iq_enq_imm12;
	logic [LOG_PR_COUNT-1:0] iq_enq_A_PR;
	logic iq_enq_A_ready;
	logic iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] iq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] iq_enq_ROB_index;

    // issue queue enqueue feedback
	logic iq_enq_ready;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_imm_dq #(.ALU_IMM_DQ_ENTRIES(ALU_IMM_DQ_ENTRIES)) WRAPPED_MODULE (.*);

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
			dispatch_dest_PR_by_way <= '0;
			dispatch_ROB_index_by_way <= '0;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // op enqueue to issue queue
			last_iq_enq_valid <= '0;
			last_iq_enq_op <= '0;
			last_iq_enq_imm12 <= '0;
			last_iq_enq_A_PR <= '0;
			last_iq_enq_A_ready <= '0;
			last_iq_enq_A_is_zero <= '0;
			last_iq_enq_dest_PR <= '0;
			last_iq_enq_ROB_index <= '0;

		    // issue queue enqueue feedback
			iq_enq_ready <= '0;
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
			dispatch_dest_PR_by_way <= next_dispatch_dest_PR_by_way;
			dispatch_ROB_index_by_way <= next_dispatch_ROB_index_by_way;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= dispatch_ack_by_way;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // op enqueue to issue queue
			last_iq_enq_valid <= iq_enq_valid;
			last_iq_enq_op <= iq_enq_op;
			last_iq_enq_imm12 <= iq_enq_imm12;
			last_iq_enq_A_PR <= iq_enq_A_PR;
			last_iq_enq_A_ready <= iq_enq_A_ready;
			last_iq_enq_A_is_zero <= iq_enq_A_is_zero;
			last_iq_enq_dest_PR <= iq_enq_dest_PR;
			last_iq_enq_ROB_index <= iq_enq_ROB_index;

		    // issue queue enqueue feedback
			iq_enq_ready <= next_iq_enq_ready;
        end
    end

endmodule