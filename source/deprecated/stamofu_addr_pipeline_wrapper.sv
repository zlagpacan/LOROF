/*
    Filename: stamofu_addr_pipeline_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_addr_pipeline module. 
    Spec: LOROF/spec/design/stamofu_addr_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_addr_pipeline_wrapper #(
	parameter IS_OC_BUFFER_SIZE = 2,
	parameter OC_ENTRIES = IS_OC_BUFFER_SIZE + 1,
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,


    // op issue from IQ
	input logic next_issue_valid,
	input logic next_issue_is_store,
	input logic next_issue_is_amo,
	input logic next_issue_is_fence,
	input logic [3:0] next_issue_op,
	input logic [11:0] next_issue_imm12,
	input logic next_issue_A_is_reg,
	input logic next_issue_A_is_bus_forward,
	input logic next_issue_A_is_fast_forward,
	input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] next_issue_A_fast_forward_pipe,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_A_bank,
	input logic next_issue_B_is_reg,
	input logic next_issue_B_is_bus_forward,
	input logic next_issue_B_is_fast_forward,
	input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] next_issue_B_fast_forward_pipe,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_B_bank,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_issue_cq_index,

    // output feedback to IQ
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

    // REQ stage info
	output logic last_REQ_valid,
	output logic last_REQ_is_store,
	output logic last_REQ_is_amo,
	output logic last_REQ_is_fence,
	output logic [3:0] last_REQ_op,
	output logic last_REQ_is_mq,
	output logic last_REQ_misaligned,
	output logic last_REQ_misaligned_exception,
	output logic [VPN_WIDTH-1:0] last_REQ_VPN,
	output logic [PO_WIDTH-3:0] last_REQ_PO_word,
	output logic [3:0] last_REQ_byte_mask,
	output logic [31:0] last_REQ_write_data,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_REQ_cq_index,

    // REQ stage feedback
	input logic next_REQ_ack
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // op issue from IQ
	logic issue_valid;
	logic issue_is_store;
	logic issue_is_amo;
	logic issue_is_fence;
	logic [3:0] issue_op;
	logic [11:0] issue_imm12;
	logic issue_A_is_reg;
	logic issue_A_is_bus_forward;
	logic issue_A_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] issue_A_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic issue_B_is_reg;
	logic issue_B_is_bus_forward;
	logic issue_B_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] issue_B_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_B_bank;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] issue_cq_index;

    // output feedback to IQ
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

    // REQ stage info
	logic REQ_valid;
	logic REQ_is_store;
	logic REQ_is_amo;
	logic REQ_is_fence;
	logic [3:0] REQ_op;
	logic REQ_is_mq;
	logic REQ_misaligned;
	logic REQ_misaligned_exception;
	logic [VPN_WIDTH-1:0] REQ_VPN;
	logic [PO_WIDTH-3:0] REQ_PO_word;
	logic [3:0] REQ_byte_mask;
	logic [31:0] REQ_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] REQ_cq_index;

    // REQ stage feedback
	logic REQ_ack;

    // ----------------------------------------------------------------
    // Module Instantiation:

	stamofu_addr_pipeline #(
		.IS_OC_BUFFER_SIZE(IS_OC_BUFFER_SIZE),
		.OC_ENTRIES(OC_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // op issue from IQ
			issue_valid <= '0;
			issue_is_store <= '0;
			issue_is_amo <= '0;
			issue_is_fence <= '0;
			issue_op <= '0;
			issue_imm12 <= '0;
			issue_A_is_reg <= '0;
			issue_A_is_bus_forward <= '0;
			issue_A_is_fast_forward <= '0;
			issue_A_fast_forward_pipe <= '0;
			issue_A_bank <= '0;
			issue_B_is_reg <= '0;
			issue_B_is_bus_forward <= '0;
			issue_B_is_fast_forward <= '0;
			issue_B_fast_forward_pipe <= '0;
			issue_B_bank <= '0;
			issue_cq_index <= '0;

		    // output feedback to IQ
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

		    // REQ stage info
			last_REQ_valid <= '0;
			last_REQ_is_store <= '0;
			last_REQ_is_amo <= '0;
			last_REQ_is_fence <= '0;
			last_REQ_op <= '0;
			last_REQ_is_mq <= '0;
			last_REQ_misaligned <= '0;
			last_REQ_misaligned_exception <= '0;
			last_REQ_VPN <= '0;
			last_REQ_PO_word <= '0;
			last_REQ_byte_mask <= '0;
			last_REQ_write_data <= '0;
			last_REQ_cq_index <= '0;

		    // REQ stage feedback
			REQ_ack <= '0;
        end
        else begin


		    // op issue from IQ
			issue_valid <= next_issue_valid;
			issue_is_store <= next_issue_is_store;
			issue_is_amo <= next_issue_is_amo;
			issue_is_fence <= next_issue_is_fence;
			issue_op <= next_issue_op;
			issue_imm12 <= next_issue_imm12;
			issue_A_is_reg <= next_issue_A_is_reg;
			issue_A_is_bus_forward <= next_issue_A_is_bus_forward;
			issue_A_is_fast_forward <= next_issue_A_is_fast_forward;
			issue_A_fast_forward_pipe <= next_issue_A_fast_forward_pipe;
			issue_A_bank <= next_issue_A_bank;
			issue_B_is_reg <= next_issue_B_is_reg;
			issue_B_is_bus_forward <= next_issue_B_is_bus_forward;
			issue_B_is_fast_forward <= next_issue_B_is_fast_forward;
			issue_B_fast_forward_pipe <= next_issue_B_fast_forward_pipe;
			issue_B_bank <= next_issue_B_bank;
			issue_cq_index <= next_issue_cq_index;

		    // output feedback to IQ
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

		    // REQ stage info
			last_REQ_valid <= REQ_valid;
			last_REQ_is_store <= REQ_is_store;
			last_REQ_is_amo <= REQ_is_amo;
			last_REQ_is_fence <= REQ_is_fence;
			last_REQ_op <= REQ_op;
			last_REQ_is_mq <= REQ_is_mq;
			last_REQ_misaligned <= REQ_misaligned;
			last_REQ_misaligned_exception <= REQ_misaligned_exception;
			last_REQ_VPN <= REQ_VPN;
			last_REQ_PO_word <= REQ_PO_word;
			last_REQ_byte_mask <= REQ_byte_mask;
			last_REQ_write_data <= REQ_write_data;
			last_REQ_cq_index <= REQ_cq_index;

		    // REQ stage feedback
			REQ_ack <= next_REQ_ack;
        end
    end

endmodule