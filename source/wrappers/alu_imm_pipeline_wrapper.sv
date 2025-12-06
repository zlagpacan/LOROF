/*
    Filename: alu_imm_pipeline_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_imm_pipeline module. 
    Spec: LOROF/spec/design/alu_imm_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module alu_imm_pipeline_wrapper #(
	parameter IS_OC_BUFFER_SIZE = 2,
	parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3,
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,


    // ALU imm op issue from IQ
	input logic next_issue_valid,
	input logic [3:0] next_issue_op,
	input logic [11:0] next_issue_imm12,
	input logic next_issue_A_is_reg,
	input logic next_issue_A_is_bus_forward,
	input logic next_issue_A_is_fast_forward,
	input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] next_issue_A_fast_forward_pipe,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_A_bank,
	input logic [LOG_PR_COUNT-1:0] next_issue_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_issue_ROB_index,

    // ready feedback to IQ
	output logic last_issue_ready,

    // reg read data from PRF
	input logic next_A_reg_read_resp_valid,
	input logic [31:0] next_A_reg_read_resp_data,

    // bus forward data from PRF
	input logic [PRF_BANK_COUNT-1:0][31:0] next_bus_forward_data_by_bank,

    // fast forward data
	input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] next_fast_forward_data_by_pipe,

    // writeback data to PRF
	output logic last_WB_valid,
	output logic [31:0] last_WB_data,
	output logic [LOG_PR_COUNT-1:0] last_WB_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_WB_ROB_index,

    // writeback backpressure from PRF
	input logic next_WB_ready,

    // this pipe's fast forward notif
	output logic last_pipe_fast_forward_notif_valid,
	output logic [LOG_PR_COUNT-1:0] last_pipe_fast_forward_notif_PR,

	output logic last_pipe_fast_forward_data_valid,
	output logic [31:0] last_pipe_fast_forward_data
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // ALU imm op issue from IQ
	logic issue_valid;
	logic [3:0] issue_op;
	logic [11:0] issue_imm12;
	logic issue_A_is_reg;
	logic issue_A_is_bus_forward;
	logic issue_A_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] issue_A_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // ready feedback to IQ
	logic issue_ready;

    // reg read data from PRF
	logic A_reg_read_resp_valid;
	logic [31:0] A_reg_read_resp_data;

    // bus forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] bus_forward_data_by_bank;

    // fast forward data
	logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] fast_forward_data_by_pipe;

    // writeback data to PRF
	logic WB_valid;
	logic [31:0] WB_data;
	logic [LOG_PR_COUNT-1:0] WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index;

    // writeback backpressure from PRF
	logic WB_ready;

    // this pipe's fast forward notif
	logic pipe_fast_forward_notif_valid;
	logic [LOG_PR_COUNT-1:0] pipe_fast_forward_notif_PR;

	logic pipe_fast_forward_data_valid;
	logic [31:0] pipe_fast_forward_data;

    // ----------------------------------------------------------------
    // Module Instantiation:

	alu_imm_pipeline #(
		.IS_OC_BUFFER_SIZE(IS_OC_BUFFER_SIZE),
		.PRF_RR_OUTPUT_BUFFER_SIZE(PRF_RR_OUTPUT_BUFFER_SIZE),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // ALU imm op issue from IQ
			issue_valid <= '0;
			issue_op <= '0;
			issue_imm12 <= '0;
			issue_A_is_reg <= '0;
			issue_A_is_bus_forward <= '0;
			issue_A_is_fast_forward <= '0;
			issue_A_fast_forward_pipe <= '0;
			issue_A_bank <= '0;
			issue_dest_PR <= '0;
			issue_ROB_index <= '0;

		    // ready feedback to IQ
			last_issue_ready <= '0;

		    // reg read data from PRF
			A_reg_read_resp_valid <= '0;
			A_reg_read_resp_data <= '0;

		    // bus forward data from PRF
			bus_forward_data_by_bank <= '0;

		    // fast forward data
			fast_forward_data_by_pipe <= '0;

		    // writeback data to PRF
			last_WB_valid <= '0;
			last_WB_data <= '0;
			last_WB_PR <= '0;
			last_WB_ROB_index <= '0;

		    // writeback backpressure from PRF
			WB_ready <= '0;

		    // this pipe's fast forward notif
			last_pipe_fast_forward_notif_valid <= '0;
			last_pipe_fast_forward_notif_PR <= '0;

			last_pipe_fast_forward_data_valid <= '0;
			last_pipe_fast_forward_data <= '0;
        end
        else begin


		    // ALU imm op issue from IQ
			issue_valid <= next_issue_valid;
			issue_op <= next_issue_op;
			issue_imm12 <= next_issue_imm12;
			issue_A_is_reg <= next_issue_A_is_reg;
			issue_A_is_bus_forward <= next_issue_A_is_bus_forward;
			issue_A_is_fast_forward <= next_issue_A_is_fast_forward;
			issue_A_fast_forward_pipe <= next_issue_A_fast_forward_pipe;
			issue_A_bank <= next_issue_A_bank;
			issue_dest_PR <= next_issue_dest_PR;
			issue_ROB_index <= next_issue_ROB_index;

		    // ready feedback to IQ
			last_issue_ready <= issue_ready;

		    // reg read data from PRF
			A_reg_read_resp_valid <= next_A_reg_read_resp_valid;
			A_reg_read_resp_data <= next_A_reg_read_resp_data;

		    // bus forward data from PRF
			bus_forward_data_by_bank <= next_bus_forward_data_by_bank;

		    // fast forward data
			fast_forward_data_by_pipe <= next_fast_forward_data_by_pipe;

		    // writeback data to PRF
			last_WB_valid <= WB_valid;
			last_WB_data <= WB_data;
			last_WB_PR <= WB_PR;
			last_WB_ROB_index <= WB_ROB_index;

		    // writeback backpressure from PRF
			WB_ready <= next_WB_ready;

		    // this pipe's fast forward notif
			last_pipe_fast_forward_notif_valid <= pipe_fast_forward_notif_valid;
			last_pipe_fast_forward_notif_PR <= pipe_fast_forward_notif_PR;

			last_pipe_fast_forward_data_valid <= pipe_fast_forward_data_valid;
			last_pipe_fast_forward_data <= pipe_fast_forward_data;
        end
    end

endmodule