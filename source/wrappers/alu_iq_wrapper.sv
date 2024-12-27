/*
    Filename: alu_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_iq module. 
    Spec: LOROF/spec/design/alu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_iq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // ALU op dispatch by entry
	input logic [3:0] next_dispatch_valid_by_entry,
	input logic [3:0][3:0] next_dispatch_op_by_entry,
	input logic [3:0][31:0] next_dispatch_imm_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_entry,
	input logic [3:0] next_dispatch_A_unneeded_by_entry,
	input logic [3:0] next_dispatch_A_ready_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_B_PR_by_entry,
	input logic [3:0] next_dispatch_is_imm_by_entry,
	input logic [3:0] next_dispatch_B_ready_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_entry,

    // ALU op dispatch feedback by entry
	output logic [3:0] last_dispatch_open_by_entry,

    // ALU pipeline feedback
	input logic next_pipeline_ready,

    // writeback bus
	input logic [PRF_BANK_COUNT-1:0] next_WB_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_upper_PR_by_bank,

    // ALU op issue to ALU pipeline
	output logic last_issue_valid,
	output logic [3:0] last_issue_op,
	output logic last_issue_is_imm,
	output logic [31:0] last_issue_imm,
	output logic last_issue_A_unneeded,
	output logic last_issue_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_A_bank,
	output logic last_issue_B_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_B_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_dest_PR,

    // reg read req to PRF
	output logic last_PRF_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_A_PR,
	output logic last_PRF_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // ALU op dispatch by entry
	logic [3:0] dispatch_valid_by_entry;
	logic [3:0][3:0] dispatch_op_by_entry;
	logic [3:0][31:0] dispatch_imm_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_entry;
	logic [3:0] dispatch_A_unneeded_by_entry;
	logic [3:0] dispatch_A_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_B_PR_by_entry;
	logic [3:0] dispatch_is_imm_by_entry;
	logic [3:0] dispatch_B_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_entry;

    // ALU op dispatch feedback by entry
	logic [3:0] dispatch_open_by_entry;

    // ALU pipeline feedback
	logic pipeline_ready;

    // writeback bus
	logic [PRF_BANK_COUNT-1:0] WB_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_upper_PR_by_bank;

    // ALU op issue to ALU pipeline
	logic issue_valid;
	logic [3:0] issue_op;
	logic issue_is_imm;
	logic [31:0] issue_imm;
	logic issue_A_unneeded;
	logic issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_B_bank;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;
	logic PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_iq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // ALU op dispatch by entry
			dispatch_valid_by_entry <= 4'b0000;
			dispatch_op_by_entry <= '0;
			dispatch_imm_by_entry <= '0;
			dispatch_A_PR_by_entry <= '0;
			dispatch_A_unneeded_by_entry <= '0;
			dispatch_A_ready_by_entry <= '0;
			dispatch_B_PR_by_entry <= '0;
			dispatch_is_imm_by_entry <= '0;
			dispatch_B_ready_by_entry <= '0;
			dispatch_dest_PR_by_entry <= '0;

		    // ALU op dispatch feedback by entry
			last_dispatch_open_by_entry <= 4'b1111;

		    // ALU pipeline feedback
			pipeline_ready <= 1'b1;

		    // writeback bus
			WB_valid_by_bank <= 4'b0000;
			WB_upper_PR_by_bank <= '0;

		    // ALU op issue to ALU pipeline
			last_issue_valid <= 1'b0;
			last_issue_op <= '0;
			last_issue_is_imm <= '0;
			last_issue_imm <= '0;
			last_issue_A_unneeded <= '0;
			last_issue_A_forward <= '0;
			last_issue_A_bank <= '0;
			last_issue_B_forward <= '0;
			last_issue_B_bank <= '0;
			last_issue_dest_PR <= '0;

		    // reg read req to PRF
			last_PRF_req_A_valid <= 1'b0;
			last_PRF_req_A_PR <= '0;
			last_PRF_req_B_valid <= 1'b0;
			last_PRF_req_B_PR <= '0;
        end
        else begin


		    // ALU op dispatch by entry
			dispatch_valid_by_entry <= next_dispatch_valid_by_entry;
			dispatch_op_by_entry <= next_dispatch_op_by_entry;
			dispatch_imm_by_entry <= next_dispatch_imm_by_entry;
			dispatch_A_PR_by_entry <= next_dispatch_A_PR_by_entry;
			dispatch_A_unneeded_by_entry <= next_dispatch_A_unneeded_by_entry;
			dispatch_A_ready_by_entry <= next_dispatch_A_ready_by_entry;
			dispatch_B_PR_by_entry <= next_dispatch_B_PR_by_entry;
			dispatch_is_imm_by_entry <= next_dispatch_is_imm_by_entry;
			dispatch_B_ready_by_entry <= next_dispatch_B_ready_by_entry;
			dispatch_dest_PR_by_entry <= next_dispatch_dest_PR_by_entry;

		    // ALU op dispatch feedback by entry
			last_dispatch_open_by_entry <= dispatch_open_by_entry;

		    // ALU pipeline feedback
			pipeline_ready <= next_pipeline_ready;

		    // writeback bus
			WB_valid_by_bank <= next_WB_valid_by_bank;
			WB_upper_PR_by_bank <= next_WB_upper_PR_by_bank;

		    // ALU op issue to ALU pipeline
			last_issue_valid <= issue_valid;
			last_issue_op <= issue_op;
			last_issue_is_imm <= issue_is_imm;
			last_issue_imm <= issue_imm;
			last_issue_A_unneeded <= issue_A_unneeded;
			last_issue_A_forward <= issue_A_forward;
			last_issue_A_bank <= issue_A_bank;
			last_issue_B_forward <= issue_B_forward;
			last_issue_B_bank <= issue_B_bank;
			last_issue_dest_PR <= issue_dest_PR;

		    // reg read req to PRF
			last_PRF_req_A_valid <= PRF_req_A_valid;
			last_PRF_req_A_PR <= PRF_req_A_PR;
			last_PRF_req_B_valid <= PRF_req_B_valid;
			last_PRF_req_B_PR <= PRF_req_B_PR;
        end
    end

endmodule