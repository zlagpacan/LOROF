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

module stamofu_addr_pipeline_wrapper (

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
	input logic next_issue_A_forward,
	input logic next_issue_A_is_zero,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_A_bank,
	input logic next_issue_B_forward,
	input logic next_issue_B_is_zero,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_B_bank,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_issue_cq_index,

    // output feedback to IQ
	output logic last_issue_ready,

    // reg read info and data from PRF
	input logic next_A_reg_read_ack,
	input logic next_A_reg_read_port,
	input logic next_B_reg_read_ack,
	input logic next_B_reg_read_port,
	input logic [PRF_BANK_COUNT-1:0][1:0][31:0] next_reg_read_data_by_bank_by_port,

    // forward data from PRF
	input logic [PRF_BANK_COUNT-1:0][31:0] next_forward_data_by_bank,

    // REQ stage info
	output logic last_REQ_valid,
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
	logic issue_A_forward;
	logic issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic issue_B_forward;
	logic issue_B_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_B_bank;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] issue_cq_index;

    // output feedback to IQ
	logic issue_ready;

    // reg read info and data from PRF
	logic A_reg_read_ack;
	logic A_reg_read_port;
	logic B_reg_read_ack;
	logic B_reg_read_port;
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank;

    // REQ stage info
	logic REQ_valid;
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

    stamofu_addr_pipeline WRAPPED_MODULE (.*);

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
			issue_A_forward <= '0;
			issue_A_is_zero <= '0;
			issue_A_bank <= '0;
			issue_B_forward <= '0;
			issue_B_is_zero <= '0;
			issue_B_bank <= '0;
			issue_cq_index <= '0;

		    // output feedback to IQ
			last_issue_ready <= '0;

		    // reg read info and data from PRF
			A_reg_read_ack <= '0;
			A_reg_read_port <= '0;
			B_reg_read_ack <= '0;
			B_reg_read_port <= '0;
			reg_read_data_by_bank_by_port <= '0;

		    // forward data from PRF
			forward_data_by_bank <= '0;

		    // REQ stage info
			last_REQ_valid <= '0;
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
			issue_A_forward <= next_issue_A_forward;
			issue_A_is_zero <= next_issue_A_is_zero;
			issue_A_bank <= next_issue_A_bank;
			issue_B_forward <= next_issue_B_forward;
			issue_B_is_zero <= next_issue_B_is_zero;
			issue_B_bank <= next_issue_B_bank;
			issue_cq_index <= next_issue_cq_index;

		    // output feedback to IQ
			last_issue_ready <= issue_ready;

		    // reg read info and data from PRF
			A_reg_read_ack <= next_A_reg_read_ack;
			A_reg_read_port <= next_A_reg_read_port;
			B_reg_read_ack <= next_B_reg_read_ack;
			B_reg_read_port <= next_B_reg_read_port;
			reg_read_data_by_bank_by_port <= next_reg_read_data_by_bank_by_port;

		    // forward data from PRF
			forward_data_by_bank <= next_forward_data_by_bank;

		    // REQ stage info
			last_REQ_valid <= REQ_valid;
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