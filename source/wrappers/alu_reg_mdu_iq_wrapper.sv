/*
    Filename: alu_reg_mdu_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_reg_mdu_iq module. 
    Spec: LOROF/spec/design/alu_reg_mdu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module alu_reg_mdu_iq_wrapper #(
	parameter ALU_REG_MDU_IQ_ENTRIES = 12
) (

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

    // MDU pipeline issue
	output logic last_mdu_issue_valid,

    // shared issue info
	output logic [3:0] last_issue_op,
	output logic last_issue_A_forward,
	output logic last_issue_A_is_zero,
	output logic [LOG_PR_COUNT-1:0] last_issue_A_PR,
	output logic last_issue_B_forward,
	output logic last_issue_B_is_zero,
	output logic [LOG_PR_COUNT-1:0] last_issue_B_PR,
	output logic [LOG_PR_COUNT-1:0] last_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_ROB_index,

    // ALU reg pipeline feedback
	input logic next_alu_reg_issue_ready,

    // MDU pipeline feedback
	input logic next_mdu_issue_ready,

    // reg read req to PRF
	output logic last_PRF_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_A_PR,
	output logic last_PRF_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_B_PR
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

    // MDU pipeline issue
	logic mdu_issue_valid;

    // shared issue info
	logic [3:0] issue_op;
	logic issue_A_forward;
	logic issue_A_is_zero;
	logic [LOG_PR_COUNT-1:0] issue_A_PR;
	logic issue_B_forward;
	logic issue_B_is_zero;
	logic [LOG_PR_COUNT-1:0] issue_B_PR;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // ALU reg pipeline feedback
	logic alu_reg_issue_ready;

    // MDU pipeline feedback
	logic mdu_issue_ready;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;
	logic PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

	alu_reg_mdu_iq #(
		.ALU_REG_MDU_IQ_ENTRIES(ALU_REG_MDU_IQ_ENTRIES)
	) WRAPPED_MODULE (.*);

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

		    // MDU pipeline issue
			last_mdu_issue_valid <= '0;

		    // shared issue info
			last_issue_op <= '0;
			last_issue_A_forward <= '0;
			last_issue_A_is_zero <= '0;
			last_issue_A_PR <= '0;
			last_issue_B_forward <= '0;
			last_issue_B_is_zero <= '0;
			last_issue_B_PR <= '0;
			last_issue_dest_PR <= '0;
			last_issue_ROB_index <= '0;

		    // ALU reg pipeline feedback
			alu_reg_issue_ready <= '0;

		    // MDU pipeline feedback
			mdu_issue_ready <= '0;

		    // reg read req to PRF
			last_PRF_req_A_valid <= '0;
			last_PRF_req_A_PR <= '0;
			last_PRF_req_B_valid <= '0;
			last_PRF_req_B_PR <= '0;
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

		    // MDU pipeline issue
			last_mdu_issue_valid <= mdu_issue_valid;

		    // shared issue info
			last_issue_op <= issue_op;
			last_issue_A_forward <= issue_A_forward;
			last_issue_A_is_zero <= issue_A_is_zero;
			last_issue_A_PR <= issue_A_PR;
			last_issue_B_forward <= issue_B_forward;
			last_issue_B_is_zero <= issue_B_is_zero;
			last_issue_B_PR <= issue_B_PR;
			last_issue_dest_PR <= issue_dest_PR;
			last_issue_ROB_index <= issue_ROB_index;

		    // ALU reg pipeline feedback
			alu_reg_issue_ready <= next_alu_reg_issue_ready;

		    // MDU pipeline feedback
			mdu_issue_ready <= next_mdu_issue_ready;

		    // reg read req to PRF
			last_PRF_req_A_valid <= PRF_req_A_valid;
			last_PRF_req_A_PR <= PRF_req_A_PR;
			last_PRF_req_B_valid <= PRF_req_B_valid;
			last_PRF_req_B_PR <= PRF_req_B_PR;
        end
    end

endmodule