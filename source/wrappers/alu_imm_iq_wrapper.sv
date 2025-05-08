/*
    Filename: alu_imm_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_imm_iq module. 
    Spec: LOROF/spec/design/alu_imm_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_iq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
	input logic next_iq_enq_valid,
	input logic [3:0] next_iq_enq_op,
	input logic [11:0] next_iq_enq_imm12,
	input logic [LOG_PR_COUNT-1:0] next_iq_enq_A_PR,
	input logic next_iq_enq_A_ready,
	input logic next_iq_enq_A_is_zero,
	input logic [LOG_PR_COUNT-1:0] next_iq_enq_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_iq_enq_ROB_index,

    // issue queue enqueue feedback
	output logic last_iq_enq_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // pipeline issue
	output logic last_issue_valid,
	output logic [3:0] last_issue_op,
	output logic [11:0] last_issue_imm12,
	output logic last_issue_A_forward,
	output logic last_issue_A_is_zero,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_A_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_ROB_index,

    // pipeline feedback
	input logic next_issue_ready,

    // reg read req to PRF
	output logic last_PRF_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_A_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

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

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // pipeline issue
	logic issue_valid;
	logic [3:0] issue_op;
	logic [11:0] issue_imm12;
	logic issue_A_forward;
	logic issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // pipeline feedback
	logic issue_ready;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_imm_iq #(.ALU_IMM_IQ_ENTRIES(ALU_IMM_IQ_ENTRIES)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to issue queue
			iq_enq_valid <= '0;
			iq_enq_op <= '0;
			iq_enq_imm12 <= '0;
			iq_enq_A_PR <= '0;
			iq_enq_A_ready <= '0;
			iq_enq_A_is_zero <= '0;
			iq_enq_dest_PR <= '0;
			iq_enq_ROB_index <= '0;

		    // issue queue enqueue feedback
			last_iq_enq_ready <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // pipeline issue
			last_issue_valid <= '0;
			last_issue_op <= '0;
			last_issue_imm12 <= '0;
			last_issue_A_forward <= '0;
			last_issue_A_is_zero <= '0;
			last_issue_A_bank <= '0;
			last_issue_dest_PR <= '0;
			last_issue_ROB_index <= '0;

		    // pipeline feedback
			issue_ready <= '0;

		    // reg read req to PRF
			last_PRF_req_A_valid <= '0;
			last_PRF_req_A_PR <= '0;
        end
        else begin

		    // op enqueue to issue queue
			iq_enq_valid <= next_iq_enq_valid;
			iq_enq_op <= next_iq_enq_op;
			iq_enq_imm12 <= next_iq_enq_imm12;
			iq_enq_A_PR <= next_iq_enq_A_PR;
			iq_enq_A_ready <= next_iq_enq_A_ready;
			iq_enq_A_is_zero <= next_iq_enq_A_is_zero;
			iq_enq_dest_PR <= next_iq_enq_dest_PR;
			iq_enq_ROB_index <= next_iq_enq_ROB_index;

		    // issue queue enqueue feedback
			last_iq_enq_ready <= iq_enq_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // pipeline issue
			last_issue_valid <= issue_valid;
			last_issue_op <= issue_op;
			last_issue_imm12 <= issue_imm12;
			last_issue_A_forward <= issue_A_forward;
			last_issue_A_is_zero <= issue_A_is_zero;
			last_issue_A_bank <= issue_A_bank;
			last_issue_dest_PR <= issue_dest_PR;
			last_issue_ROB_index <= issue_ROB_index;

		    // pipeline feedback
			issue_ready <= next_issue_ready;

		    // reg read req to PRF
			last_PRF_req_A_valid <= PRF_req_A_valid;
			last_PRF_req_A_PR <= PRF_req_A_PR;
        end
    end

endmodule