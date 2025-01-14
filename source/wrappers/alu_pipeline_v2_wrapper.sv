/*
    Filename: alu_pipeline_v2_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_pipeline_v2 module. 
    Spec: LOROF/spec/design/alu_pipeline_v2.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_pipeline_v2_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // ALU op issue from ALU IQ
	input logic next_issue_valid,
	input logic [3:0] next_issue_op,
	input logic next_issue_is_imm,
	input logic [31:0] next_issue_imm,
	input logic next_issue_A_unneeded,
	input logic next_issue_A_forward,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_A_bank,
	input logic next_issue_B_forward,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_B_bank,
	input logic [LOG_PR_COUNT-1:0] next_issue_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_issue_ROB_index,

    // ready feedback to ALU IQ
	output logic last_issue_ready,

    // reg read info and data from PRF
	input logic next_A_reg_read_ack,
	input logic next_A_reg_read_port,
	input logic next_B_reg_read_ack,
	input logic next_B_reg_read_port,
	input logic [PRF_BANK_COUNT-1:0][1:0][31:0] next_reg_read_data_by_bank_by_port,

    // forward data from PRF
	input logic [PRF_BANK_COUNT-1:0][31:0] next_forward_data_by_bank,

    // writeback data to PRF
	output logic last_WB_valid,
	output logic [31:0] last_WB_data,
	output logic [LOG_PR_COUNT-1:0] last_WB_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_WB_ROB_index,

    // writeback backpressure from PRF
	input logic next_WB_ready
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // ALU op issue from ALU IQ
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
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // ready feedback to ALU IQ
	logic issue_ready;

    // reg read info and data from PRF
	logic A_reg_read_ack;
	logic A_reg_read_port;
	logic B_reg_read_ack;
	logic B_reg_read_port;
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank;

    // writeback data to PRF
	logic WB_valid;
	logic [31:0] WB_data;
	logic [LOG_PR_COUNT-1:0] WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index;

    // writeback backpressure from PRF
	logic WB_ready;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_pipeline_v2 WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // ALU op issue from ALU IQ
			issue_valid <= '0;
			issue_op <= '0;
			issue_is_imm <= '0;
			issue_imm <= '0;
			issue_A_unneeded <= '0;
			issue_A_forward <= '0;
			issue_A_bank <= '0;
			issue_B_forward <= '0;
			issue_B_bank <= '0;
			issue_dest_PR <= '0;
			issue_ROB_index <= '0;

		    // ready feedback to ALU IQ
			last_issue_ready <= '0;

		    // reg read info and data from PRF
			A_reg_read_ack <= '0;
			A_reg_read_port <= '0;
			B_reg_read_ack <= '0;
			B_reg_read_port <= '0;
			reg_read_data_by_bank_by_port <= '0;

		    // forward data from PRF
			forward_data_by_bank <= '0;

		    // writeback data to PRF
			last_WB_valid <= '0;
			last_WB_data <= '0;
			last_WB_PR <= '0;
			last_WB_ROB_index <= '0;

		    // writeback backpressure from PRF
			WB_ready <= '0;
        end
        else begin


		    // ALU op issue from ALU IQ
			issue_valid <= next_issue_valid;
			issue_op <= next_issue_op;
			issue_is_imm <= next_issue_is_imm;
			issue_imm <= next_issue_imm;
			issue_A_unneeded <= next_issue_A_unneeded;
			issue_A_forward <= next_issue_A_forward;
			issue_A_bank <= next_issue_A_bank;
			issue_B_forward <= next_issue_B_forward;
			issue_B_bank <= next_issue_B_bank;
			issue_dest_PR <= next_issue_dest_PR;
			issue_ROB_index <= next_issue_ROB_index;

		    // ready feedback to ALU IQ
			last_issue_ready <= issue_ready;

		    // reg read info and data from PRF
			A_reg_read_ack <= next_A_reg_read_ack;
			A_reg_read_port <= next_A_reg_read_port;
			B_reg_read_ack <= next_B_reg_read_ack;
			B_reg_read_port <= next_B_reg_read_port;
			reg_read_data_by_bank_by_port <= next_reg_read_data_by_bank_by_port;

		    // forward data from PRF
			forward_data_by_bank <= next_forward_data_by_bank;

		    // writeback data to PRF
			last_WB_valid <= WB_valid;
			last_WB_data <= WB_data;
			last_WB_PR <= WB_PR;
			last_WB_ROB_index <= WB_ROB_index;

		    // writeback backpressure from PRF
			WB_ready <= next_WB_ready;
        end
    end

endmodule