/*
    Filename: mdu_pipeline_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mdu_pipeline module. 
    Spec: LOROF/spec/design/mdu_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module mdu_pipeline_wrapper #(
	parameter IS_OC_BUFFER_SIZE = 2,
	parameter OC_ENTRIES = IS_OC_BUFFER_SIZE + 1,
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT),
	parameter MDU_RESULT_CACHE_ENTRIES = 4,
	parameter LOG_MDU_RESULT_CACHE_ENTRIES = $clog2(MDU_RESULT_CACHE_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,


    // MDU pipeline issue
	input logic next_issue_valid,
	input logic [2:0] next_issue_op,
	input logic next_issue_A_is_reg,
	input logic next_issue_A_is_bus_forward,
	input logic next_issue_A_is_fast_forward,
	input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] next_issue_A_fast_forward_pipe,
	input logic [LOG_PR_COUNT-1:0] next_issue_A_PR,
	input logic next_issue_B_is_reg,
	input logic next_issue_B_is_bus_forward,
	input logic next_issue_B_is_fast_forward,
	input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] next_issue_B_fast_forward_pipe,
	input logic [LOG_PR_COUNT-1:0] next_issue_B_PR,
	input logic [LOG_PR_COUNT-1:0] next_issue_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_issue_ROB_index,

    // MDU pipeline feedback to IQ
	output logic last_issue_ready,

    // reg read data from PRF
	input logic next_A_reg_read_resp_valid,
	input logic [31:0] next_A_reg_read_resp_data,
	input logic next_B_reg_read_resp_valid,
	input logic [31:0] next_B_reg_read_resp_data,

    // bus forward data from PRF
	input logic [PRF_BANK_COUNT-1:0][31:0] next_bus_forward_data_by_bank,

    // fast forward data
	input logic [FAST_FORWARD_PIPE_COUNT-1:0] next_fast_forward_data_valid_by_pipe,
	input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] next_fast_forward_data_by_pipe,

    // writeback data to PRF
	output logic last_WB_valid,
	output logic [31:0] last_WB_data,
	output logic [LOG_PR_COUNT-1:0] last_WB_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_WB_ROB_index,

    // writeback feedback from
	input logic next_WB_ready
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // MDU pipeline issue
	logic issue_valid;
	logic [2:0] issue_op;
	logic issue_A_is_reg;
	logic issue_A_is_bus_forward;
	logic issue_A_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] issue_A_fast_forward_pipe;
	logic [LOG_PR_COUNT-1:0] issue_A_PR;
	logic issue_B_is_reg;
	logic issue_B_is_bus_forward;
	logic issue_B_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] issue_B_fast_forward_pipe;
	logic [LOG_PR_COUNT-1:0] issue_B_PR;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // MDU pipeline feedback to IQ
	logic issue_ready;

    // reg read data from PRF
	logic A_reg_read_resp_valid;
	logic [31:0] A_reg_read_resp_data;
	logic B_reg_read_resp_valid;
	logic [31:0] B_reg_read_resp_data;

    // bus forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] bus_forward_data_by_bank;

    // fast forward data
	logic [FAST_FORWARD_PIPE_COUNT-1:0] fast_forward_data_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] fast_forward_data_by_pipe;

    // writeback data to PRF
	logic WB_valid;
	logic [31:0] WB_data;
	logic [LOG_PR_COUNT-1:0] WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index;

    // writeback feedback from
	logic WB_ready;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mdu_pipeline #(
		.IS_OC_BUFFER_SIZE(IS_OC_BUFFER_SIZE),
		.OC_ENTRIES(OC_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT),
		.MDU_RESULT_CACHE_ENTRIES(MDU_RESULT_CACHE_ENTRIES),
		.LOG_MDU_RESULT_CACHE_ENTRIES(LOG_MDU_RESULT_CACHE_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // MDU pipeline issue
			issue_valid <= '0;
			issue_op <= '0;
			issue_A_is_reg <= '0;
			issue_A_is_bus_forward <= '0;
			issue_A_is_fast_forward <= '0;
			issue_A_fast_forward_pipe <= '0;
			issue_A_PR <= '0;
			issue_B_is_reg <= '0;
			issue_B_is_bus_forward <= '0;
			issue_B_is_fast_forward <= '0;
			issue_B_fast_forward_pipe <= '0;
			issue_B_PR <= '0;
			issue_dest_PR <= '0;
			issue_ROB_index <= '0;

		    // MDU pipeline feedback to IQ
			last_issue_ready <= '0;

		    // reg read data from PRF
			A_reg_read_resp_valid <= '0;
			A_reg_read_resp_data <= '0;
			B_reg_read_resp_valid <= '0;
			B_reg_read_resp_data <= '0;

		    // bus forward data from PRF
			bus_forward_data_by_bank <= '0;

		    // fast forward data
			fast_forward_data_valid_by_pipe <= '0;
			fast_forward_data_by_pipe <= '0;

		    // writeback data to PRF
			last_WB_valid <= '0;
			last_WB_data <= '0;
			last_WB_PR <= '0;
			last_WB_ROB_index <= '0;

		    // writeback feedback from
			WB_ready <= '0;
        end
        else begin


		    // MDU pipeline issue
			issue_valid <= next_issue_valid;
			issue_op <= next_issue_op;
			issue_A_is_reg <= next_issue_A_is_reg;
			issue_A_is_bus_forward <= next_issue_A_is_bus_forward;
			issue_A_is_fast_forward <= next_issue_A_is_fast_forward;
			issue_A_fast_forward_pipe <= next_issue_A_fast_forward_pipe;
			issue_A_PR <= next_issue_A_PR;
			issue_B_is_reg <= next_issue_B_is_reg;
			issue_B_is_bus_forward <= next_issue_B_is_bus_forward;
			issue_B_is_fast_forward <= next_issue_B_is_fast_forward;
			issue_B_fast_forward_pipe <= next_issue_B_fast_forward_pipe;
			issue_B_PR <= next_issue_B_PR;
			issue_dest_PR <= next_issue_dest_PR;
			issue_ROB_index <= next_issue_ROB_index;

		    // MDU pipeline feedback to IQ
			last_issue_ready <= issue_ready;

		    // reg read data from PRF
			A_reg_read_resp_valid <= next_A_reg_read_resp_valid;
			A_reg_read_resp_data <= next_A_reg_read_resp_data;
			B_reg_read_resp_valid <= next_B_reg_read_resp_valid;
			B_reg_read_resp_data <= next_B_reg_read_resp_data;

		    // bus forward data from PRF
			bus_forward_data_by_bank <= next_bus_forward_data_by_bank;

		    // fast forward data
			fast_forward_data_valid_by_pipe <= next_fast_forward_data_valid_by_pipe;
			fast_forward_data_by_pipe <= next_fast_forward_data_by_pipe;

		    // writeback data to PRF
			last_WB_valid <= WB_valid;
			last_WB_data <= WB_data;
			last_WB_PR <= WB_PR;
			last_WB_ROB_index <= WB_ROB_index;

		    // writeback feedback from
			WB_ready <= next_WB_ready;
        end
    end

endmodule