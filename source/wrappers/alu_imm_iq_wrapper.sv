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


    // ALU op dispatch by entry
	input logic [3:0] next_dispatch_valid_by_entry,
	input logic [3:0][3:0] next_dispatch_op_by_entry,
	input logic [3:0][31:0] next_dispatch_imm_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_entry,
	input logic [3:0] next_dispatch_A_unneeded_by_entry,
	input logic [3:0] next_dispatch_A_ready_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_entry,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_entry,

    // ALU op dispatch feedback by entry
	output logic [3:0] last_dispatch_ready_by_entry,

    // ALU pipeline feedback
	input logic next_pipeline_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // ALU op issue to ALU pipeline
	output logic last_issue_valid,
	output logic [3:0] last_issue_op,
	output logic [31:0] last_issue_imm,
	output logic last_issue_A_unneeded,
	output logic last_issue_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_A_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_ROB_index,

    // reg read req to PRF
	output logic last_PRF_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_A_PR
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
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_entry;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_entry;

    // ALU op dispatch feedback by entry
	logic [3:0] dispatch_ready_by_entry;

    // ALU pipeline feedback
	logic pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // ALU op issue to ALU pipeline
	logic issue_valid;
	logic [3:0] issue_op;
	logic [31:0] issue_imm;
	logic issue_A_unneeded;
	logic issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_imm_iq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // ALU op dispatch by entry
			dispatch_valid_by_entry <= '0;
			dispatch_op_by_entry <= '0;
			dispatch_imm_by_entry <= '0;
			dispatch_A_PR_by_entry <= '0;
			dispatch_A_unneeded_by_entry <= '0;
			dispatch_A_ready_by_entry <= '0;
			dispatch_dest_PR_by_entry <= '0;
			dispatch_ROB_index_by_entry <= '0;

		    // ALU op dispatch feedback by entry
			last_dispatch_ready_by_entry <= '0;

		    // ALU pipeline feedback
			pipeline_ready <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // ALU op issue to ALU pipeline
			last_issue_valid <= '0;
			last_issue_op <= '0;
			last_issue_imm <= '0;
			last_issue_A_unneeded <= '0;
			last_issue_A_forward <= '0;
			last_issue_A_bank <= '0;
			last_issue_dest_PR <= '0;
			last_issue_ROB_index <= '0;

		    // reg read req to PRF
			last_PRF_req_A_valid <= '0;
			last_PRF_req_A_PR <= '0;
        end
        else begin


		    // ALU op dispatch by entry
			dispatch_valid_by_entry <= next_dispatch_valid_by_entry;
			dispatch_op_by_entry <= next_dispatch_op_by_entry;
			dispatch_imm_by_entry <= next_dispatch_imm_by_entry;
			dispatch_A_PR_by_entry <= next_dispatch_A_PR_by_entry;
			dispatch_A_unneeded_by_entry <= next_dispatch_A_unneeded_by_entry;
			dispatch_A_ready_by_entry <= next_dispatch_A_ready_by_entry;
			dispatch_dest_PR_by_entry <= next_dispatch_dest_PR_by_entry;
			dispatch_ROB_index_by_entry <= next_dispatch_ROB_index_by_entry;

		    // ALU op dispatch feedback by entry
			last_dispatch_ready_by_entry <= dispatch_ready_by_entry;

		    // ALU pipeline feedback
			pipeline_ready <= next_pipeline_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // ALU op issue to ALU pipeline
			last_issue_valid <= issue_valid;
			last_issue_op <= issue_op;
			last_issue_imm <= issue_imm;
			last_issue_A_unneeded <= issue_A_unneeded;
			last_issue_A_forward <= issue_A_forward;
			last_issue_A_bank <= issue_A_bank;
			last_issue_dest_PR <= issue_dest_PR;
			last_issue_ROB_index <= issue_ROB_index;

		    // reg read req to PRF
			last_PRF_req_A_valid <= PRF_req_A_valid;
			last_PRF_req_A_PR <= PRF_req_A_PR;
        end
    end

endmodule