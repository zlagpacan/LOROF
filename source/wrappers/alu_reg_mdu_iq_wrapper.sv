/*
    Filename: alu_reg_mdu_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_reg_mdu_iq module. 
    Spec: LOROF/spec/design/alu_reg_mdu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_mdu_iq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
	input logic next_iq_enq_valid,
	input logic next_iq_enq_is_alu_reg,
	input logic next_iq_enq_is_mdu,
	input logic [3:0] next_iq_enq_op,
	input logic [LOG_PR_COUNT-1:0] next_iq_enq_A_PR,
	input logic next_iq_enq_A_ready,
	input logic next_iq_enq_A_is_zero,
	input logic [LOG_PR_COUNT-1:0] next_iq_enq_B_PR,
	input logic next_iq_enq_B_ready,
	input logic next_iq_enq_B_is_zero,
	input logic [LOG_PR_COUNT-1:0] next_iq_enq_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_iq_enq_ROB_index,

    // issue queue enqueue feedback
	output logic last_iq_enq_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // ALU reg pipeline issue
	output logic last_alu_reg_issue_valid,
	output logic [3:0] last_alu_reg_issue_op,
	output logic last_alu_reg_issue_A_forward,
	output logic last_alu_reg_issue_A_is_zero,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_alu_reg_issue_A_bank,
	output logic last_alu_reg_issue_B_forward,
	output logic last_alu_reg_issue_B_is_zero,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_alu_reg_issue_B_bank,
	output logic [LOG_PR_COUNT-1:0] last_alu_reg_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_alu_reg_issue_ROB_index,

    // ALU reg pipeline feedback
	input logic next_alu_reg_issue_ready,

    // ALU reg reg read req to PRF
	output logic last_PRF_alu_reg_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_alu_reg_req_A_PR,
	output logic last_PRF_alu_reg_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_alu_reg_req_B_PR,

    // MDU pipeline issue
	output logic last_mdu_issue_valid,
	output logic [3:0] last_mdu_issue_op,
	output logic last_mdu_issue_A_forward,
	output logic last_mdu_issue_A_is_zero,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_mdu_issue_A_bank,
	output logic last_mdu_issue_B_forward,
	output logic last_mdu_issue_B_is_zero,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_mdu_issue_B_bank,
	output logic [LOG_PR_COUNT-1:0] last_mdu_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_mdu_issue_ROB_index,

    // MDU pipeline feedback
	input logic next_mdu_issue_ready,

    // MDU reg read req to PRF
	output logic last_PRF_mdu_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_mdu_req_A_PR,
	output logic last_PRF_mdu_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_mdu_req_B_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op enqueue to issue queue
	logic iq_enq_valid;
	logic iq_enq_is_alu_reg;
	logic iq_enq_is_mdu;
	logic [3:0] iq_enq_op;
	logic [LOG_PR_COUNT-1:0] iq_enq_A_PR;
	logic iq_enq_A_ready;
	logic iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] iq_enq_B_PR;
	logic iq_enq_B_ready;
	logic iq_enq_B_is_zero;
	logic [LOG_PR_COUNT-1:0] iq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] iq_enq_ROB_index;

    // issue queue enqueue feedback
	logic iq_enq_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // ALU reg pipeline issue
	logic alu_reg_issue_valid;
	logic [3:0] alu_reg_issue_op;
	logic alu_reg_issue_A_forward;
	logic alu_reg_issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] alu_reg_issue_A_bank;
	logic alu_reg_issue_B_forward;
	logic alu_reg_issue_B_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] alu_reg_issue_B_bank;
	logic [LOG_PR_COUNT-1:0] alu_reg_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] alu_reg_issue_ROB_index;

    // ALU reg pipeline feedback
	logic alu_reg_issue_ready;

    // ALU reg reg read req to PRF
	logic PRF_alu_reg_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_alu_reg_req_A_PR;
	logic PRF_alu_reg_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_alu_reg_req_B_PR;

    // MDU pipeline issue
	logic mdu_issue_valid;
	logic [3:0] mdu_issue_op;
	logic mdu_issue_A_forward;
	logic mdu_issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] mdu_issue_A_bank;
	logic mdu_issue_B_forward;
	logic mdu_issue_B_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] mdu_issue_B_bank;
	logic [LOG_PR_COUNT-1:0] mdu_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] mdu_issue_ROB_index;

    // MDU pipeline feedback
	logic mdu_issue_ready;

    // MDU reg read req to PRF
	logic PRF_mdu_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_mdu_req_A_PR;
	logic PRF_mdu_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_mdu_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_reg_mdu_iq #(.ALU_REG_MDU_IQ_ENTRIES(ALU_REG_MDU_IQ_ENTRIES)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to issue queue
			iq_enq_valid <= '0;
			iq_enq_is_alu_reg <= '0;
			iq_enq_is_mdu <= '0;
			iq_enq_op <= '0;
			iq_enq_A_PR <= '0;
			iq_enq_A_ready <= '0;
			iq_enq_A_is_zero <= '0;
			iq_enq_B_PR <= '0;
			iq_enq_B_ready <= '0;
			iq_enq_B_is_zero <= '0;
			iq_enq_dest_PR <= '0;
			iq_enq_ROB_index <= '0;

		    // issue queue enqueue feedback
			last_iq_enq_ready <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // ALU reg pipeline issue
			last_alu_reg_issue_valid <= '0;
			last_alu_reg_issue_op <= '0;
			last_alu_reg_issue_A_forward <= '0;
			last_alu_reg_issue_A_is_zero <= '0;
			last_alu_reg_issue_A_bank <= '0;
			last_alu_reg_issue_B_forward <= '0;
			last_alu_reg_issue_B_is_zero <= '0;
			last_alu_reg_issue_B_bank <= '0;
			last_alu_reg_issue_dest_PR <= '0;
			last_alu_reg_issue_ROB_index <= '0;

		    // ALU reg pipeline feedback
			alu_reg_issue_ready <= '0;

		    // ALU reg reg read req to PRF
			last_PRF_alu_reg_req_A_valid <= '0;
			last_PRF_alu_reg_req_A_PR <= '0;
			last_PRF_alu_reg_req_B_valid <= '0;
			last_PRF_alu_reg_req_B_PR <= '0;

		    // MDU pipeline issue
			last_mdu_issue_valid <= '0;
			last_mdu_issue_op <= '0;
			last_mdu_issue_A_forward <= '0;
			last_mdu_issue_A_is_zero <= '0;
			last_mdu_issue_A_bank <= '0;
			last_mdu_issue_B_forward <= '0;
			last_mdu_issue_B_is_zero <= '0;
			last_mdu_issue_B_bank <= '0;
			last_mdu_issue_dest_PR <= '0;
			last_mdu_issue_ROB_index <= '0;

		    // MDU pipeline feedback
			mdu_issue_ready <= '0;

		    // MDU reg read req to PRF
			last_PRF_mdu_req_A_valid <= '0;
			last_PRF_mdu_req_A_PR <= '0;
			last_PRF_mdu_req_B_valid <= '0;
			last_PRF_mdu_req_B_PR <= '0;
        end
        else begin

		    // op enqueue to issue queue
			iq_enq_valid <= next_iq_enq_valid;
			iq_enq_is_alu_reg <= next_iq_enq_is_alu_reg;
			iq_enq_is_mdu <= next_iq_enq_is_mdu;
			iq_enq_op <= next_iq_enq_op;
			iq_enq_A_PR <= next_iq_enq_A_PR;
			iq_enq_A_ready <= next_iq_enq_A_ready;
			iq_enq_A_is_zero <= next_iq_enq_A_is_zero;
			iq_enq_B_PR <= next_iq_enq_B_PR;
			iq_enq_B_ready <= next_iq_enq_B_ready;
			iq_enq_B_is_zero <= next_iq_enq_B_is_zero;
			iq_enq_dest_PR <= next_iq_enq_dest_PR;
			iq_enq_ROB_index <= next_iq_enq_ROB_index;

		    // issue queue enqueue feedback
			last_iq_enq_ready <= iq_enq_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // ALU reg pipeline issue
			last_alu_reg_issue_valid <= alu_reg_issue_valid;
			last_alu_reg_issue_op <= alu_reg_issue_op;
			last_alu_reg_issue_A_forward <= alu_reg_issue_A_forward;
			last_alu_reg_issue_A_is_zero <= alu_reg_issue_A_is_zero;
			last_alu_reg_issue_A_bank <= alu_reg_issue_A_bank;
			last_alu_reg_issue_B_forward <= alu_reg_issue_B_forward;
			last_alu_reg_issue_B_is_zero <= alu_reg_issue_B_is_zero;
			last_alu_reg_issue_B_bank <= alu_reg_issue_B_bank;
			last_alu_reg_issue_dest_PR <= alu_reg_issue_dest_PR;
			last_alu_reg_issue_ROB_index <= alu_reg_issue_ROB_index;

		    // ALU reg pipeline feedback
			alu_reg_issue_ready <= next_alu_reg_issue_ready;

		    // ALU reg reg read req to PRF
			last_PRF_alu_reg_req_A_valid <= PRF_alu_reg_req_A_valid;
			last_PRF_alu_reg_req_A_PR <= PRF_alu_reg_req_A_PR;
			last_PRF_alu_reg_req_B_valid <= PRF_alu_reg_req_B_valid;
			last_PRF_alu_reg_req_B_PR <= PRF_alu_reg_req_B_PR;

		    // MDU pipeline issue
			last_mdu_issue_valid <= mdu_issue_valid;
			last_mdu_issue_op <= mdu_issue_op;
			last_mdu_issue_A_forward <= mdu_issue_A_forward;
			last_mdu_issue_A_is_zero <= mdu_issue_A_is_zero;
			last_mdu_issue_A_bank <= mdu_issue_A_bank;
			last_mdu_issue_B_forward <= mdu_issue_B_forward;
			last_mdu_issue_B_is_zero <= mdu_issue_B_is_zero;
			last_mdu_issue_B_bank <= mdu_issue_B_bank;
			last_mdu_issue_dest_PR <= mdu_issue_dest_PR;
			last_mdu_issue_ROB_index <= mdu_issue_ROB_index;

		    // MDU pipeline feedback
			mdu_issue_ready <= next_mdu_issue_ready;

		    // MDU reg read req to PRF
			last_PRF_mdu_req_A_valid <= PRF_mdu_req_A_valid;
			last_PRF_mdu_req_A_PR <= PRF_mdu_req_A_PR;
			last_PRF_mdu_req_B_valid <= PRF_mdu_req_B_valid;
			last_PRF_mdu_req_B_PR <= PRF_mdu_req_B_PR;
        end
    end

endmodule