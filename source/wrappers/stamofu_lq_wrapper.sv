/*
    Filename: stamofu_lq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_lq module. 
    Spec: LOROF/spec/design/stamofu_lq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_lq_wrapper #(
	parameter STAMOFU_LQ_ENTRIES_PER_BANK = 2
) (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage enq info
	input logic next_REQ_enq_valid,
	input logic next_REQ_enq_is_store,
	input logic next_REQ_enq_is_amo,
	input logic next_REQ_enq_is_fence,
	input logic [3:0] next_REQ_enq_op,
	input logic next_REQ_enq_is_mq,
	input logic next_REQ_enq_misaligned,
	input logic next_REQ_enq_misaligned_exception,
	input logic [VPN_WIDTH-1:0] next_REQ_enq_VPN,
	input logic [PO_WIDTH-3:0] next_REQ_enq_PO_word,
	input logic [3:0] next_REQ_enq_byte_mask,
	input logic [31:0] next_REQ_enq_write_data,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_REQ_enq_cq_index,

    // REQ stage enq feedback
	output logic last_REQ_enq_ack,

    // REQ stage deq info bank 0
	output logic last_REQ_deq_bank0_valid,

	output logic last_REQ_deq_bank0_is_store,
	output logic last_REQ_deq_bank0_is_amo,
	output logic last_REQ_deq_bank0_is_fence,
	output logic [3:0] last_REQ_deq_bank0_op,
	output logic last_REQ_deq_bank0_is_mq,
	output logic last_REQ_deq_bank0_misaligned,
	output logic last_REQ_deq_bank0_misaligned_exception,
	output logic [VPN_WIDTH-1:0] last_REQ_deq_bank0_VPN,
	output logic [PO_WIDTH-3:0] last_REQ_deq_bank0_PO_word,
	output logic [3:0] last_REQ_deq_bank0_byte_mask,
	output logic [31:0] last_REQ_deq_bank0_write_data,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_REQ_deq_bank0_cq_index,

    // REQ stage deq feedback bank 0
	input logic next_REQ_deq_bank0_ack,

    // REQ stage deq info bank 1
	output logic last_REQ_deq_bank1_valid,

	output logic last_REQ_deq_bank1_is_store,
	output logic last_REQ_deq_bank1_is_amo,
	output logic last_REQ_deq_bank1_is_fence,
	output logic [3:0] last_REQ_deq_bank1_op,
	output logic last_REQ_deq_bank1_is_mq,
	output logic last_REQ_deq_bank1_misaligned,
	output logic last_REQ_deq_bank1_misaligned_exception,
	output logic [VPN_WIDTH-1:0] last_REQ_deq_bank1_VPN,
	output logic [PO_WIDTH-3:0] last_REQ_deq_bank1_PO_word,
	output logic [3:0] last_REQ_deq_bank1_byte_mask,
	output logic [31:0] last_REQ_deq_bank1_write_data,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_REQ_deq_bank1_cq_index,

    // REQ stage deq feedback bank 1
	input logic next_REQ_deq_bank1_ack
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // REQ stage enq info
	logic REQ_enq_valid;
	logic REQ_enq_is_store;
	logic REQ_enq_is_amo;
	logic REQ_enq_is_fence;
	logic [3:0] REQ_enq_op;
	logic REQ_enq_is_mq;
	logic REQ_enq_misaligned;
	logic REQ_enq_misaligned_exception;
	logic [VPN_WIDTH-1:0] REQ_enq_VPN;
	logic [PO_WIDTH-3:0] REQ_enq_PO_word;
	logic [3:0] REQ_enq_byte_mask;
	logic [31:0] REQ_enq_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] REQ_enq_cq_index;

    // REQ stage enq feedback
	logic REQ_enq_ack;

    // REQ stage deq info bank 0
	logic REQ_deq_bank0_valid;

	logic REQ_deq_bank0_is_store;
	logic REQ_deq_bank0_is_amo;
	logic REQ_deq_bank0_is_fence;
	logic [3:0] REQ_deq_bank0_op;
	logic REQ_deq_bank0_is_mq;
	logic REQ_deq_bank0_misaligned;
	logic REQ_deq_bank0_misaligned_exception;
	logic [VPN_WIDTH-1:0] REQ_deq_bank0_VPN;
	logic [PO_WIDTH-3:0] REQ_deq_bank0_PO_word;
	logic [3:0] REQ_deq_bank0_byte_mask;
	logic [31:0] REQ_deq_bank0_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] REQ_deq_bank0_cq_index;

    // REQ stage deq feedback bank 0
	logic REQ_deq_bank0_ack;

    // REQ stage deq info bank 1
	logic REQ_deq_bank1_valid;

	logic REQ_deq_bank1_is_store;
	logic REQ_deq_bank1_is_amo;
	logic REQ_deq_bank1_is_fence;
	logic [3:0] REQ_deq_bank1_op;
	logic REQ_deq_bank1_is_mq;
	logic REQ_deq_bank1_misaligned;
	logic REQ_deq_bank1_misaligned_exception;
	logic [VPN_WIDTH-1:0] REQ_deq_bank1_VPN;
	logic [PO_WIDTH-3:0] REQ_deq_bank1_PO_word;
	logic [3:0] REQ_deq_bank1_byte_mask;
	logic [31:0] REQ_deq_bank1_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] REQ_deq_bank1_cq_index;

    // REQ stage deq feedback bank 1
	logic REQ_deq_bank1_ack;

    // ----------------------------------------------------------------
    // Module Instantiation:

	stamofu_lq #(
		.STAMOFU_LQ_ENTRIES_PER_BANK(STAMOFU_LQ_ENTRIES_PER_BANK)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // REQ stage enq info
			REQ_enq_valid <= '0;
			REQ_enq_is_store <= '0;
			REQ_enq_is_amo <= '0;
			REQ_enq_is_fence <= '0;
			REQ_enq_op <= '0;
			REQ_enq_is_mq <= '0;
			REQ_enq_misaligned <= '0;
			REQ_enq_misaligned_exception <= '0;
			REQ_enq_VPN <= '0;
			REQ_enq_PO_word <= '0;
			REQ_enq_byte_mask <= '0;
			REQ_enq_write_data <= '0;
			REQ_enq_cq_index <= '0;

		    // REQ stage enq feedback
			last_REQ_enq_ack <= '0;

		    // REQ stage deq info bank 0
			last_REQ_deq_bank0_valid <= '0;

			last_REQ_deq_bank0_is_store <= '0;
			last_REQ_deq_bank0_is_amo <= '0;
			last_REQ_deq_bank0_is_fence <= '0;
			last_REQ_deq_bank0_op <= '0;
			last_REQ_deq_bank0_is_mq <= '0;
			last_REQ_deq_bank0_misaligned <= '0;
			last_REQ_deq_bank0_misaligned_exception <= '0;
			last_REQ_deq_bank0_VPN <= '0;
			last_REQ_deq_bank0_PO_word <= '0;
			last_REQ_deq_bank0_byte_mask <= '0;
			last_REQ_deq_bank0_write_data <= '0;
			last_REQ_deq_bank0_cq_index <= '0;

		    // REQ stage deq feedback bank 0
			REQ_deq_bank0_ack <= '0;

		    // REQ stage deq info bank 1
			last_REQ_deq_bank1_valid <= '0;

			last_REQ_deq_bank1_is_store <= '0;
			last_REQ_deq_bank1_is_amo <= '0;
			last_REQ_deq_bank1_is_fence <= '0;
			last_REQ_deq_bank1_op <= '0;
			last_REQ_deq_bank1_is_mq <= '0;
			last_REQ_deq_bank1_misaligned <= '0;
			last_REQ_deq_bank1_misaligned_exception <= '0;
			last_REQ_deq_bank1_VPN <= '0;
			last_REQ_deq_bank1_PO_word <= '0;
			last_REQ_deq_bank1_byte_mask <= '0;
			last_REQ_deq_bank1_write_data <= '0;
			last_REQ_deq_bank1_cq_index <= '0;

		    // REQ stage deq feedback bank 1
			REQ_deq_bank1_ack <= '0;
        end
        else begin

		    // REQ stage enq info
			REQ_enq_valid <= next_REQ_enq_valid;
			REQ_enq_is_store <= next_REQ_enq_is_store;
			REQ_enq_is_amo <= next_REQ_enq_is_amo;
			REQ_enq_is_fence <= next_REQ_enq_is_fence;
			REQ_enq_op <= next_REQ_enq_op;
			REQ_enq_is_mq <= next_REQ_enq_is_mq;
			REQ_enq_misaligned <= next_REQ_enq_misaligned;
			REQ_enq_misaligned_exception <= next_REQ_enq_misaligned_exception;
			REQ_enq_VPN <= next_REQ_enq_VPN;
			REQ_enq_PO_word <= next_REQ_enq_PO_word;
			REQ_enq_byte_mask <= next_REQ_enq_byte_mask;
			REQ_enq_write_data <= next_REQ_enq_write_data;
			REQ_enq_cq_index <= next_REQ_enq_cq_index;

		    // REQ stage enq feedback
			last_REQ_enq_ack <= REQ_enq_ack;

		    // REQ stage deq info bank 0
			last_REQ_deq_bank0_valid <= REQ_deq_bank0_valid;

			last_REQ_deq_bank0_is_store <= REQ_deq_bank0_is_store;
			last_REQ_deq_bank0_is_amo <= REQ_deq_bank0_is_amo;
			last_REQ_deq_bank0_is_fence <= REQ_deq_bank0_is_fence;
			last_REQ_deq_bank0_op <= REQ_deq_bank0_op;
			last_REQ_deq_bank0_is_mq <= REQ_deq_bank0_is_mq;
			last_REQ_deq_bank0_misaligned <= REQ_deq_bank0_misaligned;
			last_REQ_deq_bank0_misaligned_exception <= REQ_deq_bank0_misaligned_exception;
			last_REQ_deq_bank0_VPN <= REQ_deq_bank0_VPN;
			last_REQ_deq_bank0_PO_word <= REQ_deq_bank0_PO_word;
			last_REQ_deq_bank0_byte_mask <= REQ_deq_bank0_byte_mask;
			last_REQ_deq_bank0_write_data <= REQ_deq_bank0_write_data;
			last_REQ_deq_bank0_cq_index <= REQ_deq_bank0_cq_index;

		    // REQ stage deq feedback bank 0
			REQ_deq_bank0_ack <= next_REQ_deq_bank0_ack;

		    // REQ stage deq info bank 1
			last_REQ_deq_bank1_valid <= REQ_deq_bank1_valid;

			last_REQ_deq_bank1_is_store <= REQ_deq_bank1_is_store;
			last_REQ_deq_bank1_is_amo <= REQ_deq_bank1_is_amo;
			last_REQ_deq_bank1_is_fence <= REQ_deq_bank1_is_fence;
			last_REQ_deq_bank1_op <= REQ_deq_bank1_op;
			last_REQ_deq_bank1_is_mq <= REQ_deq_bank1_is_mq;
			last_REQ_deq_bank1_misaligned <= REQ_deq_bank1_misaligned;
			last_REQ_deq_bank1_misaligned_exception <= REQ_deq_bank1_misaligned_exception;
			last_REQ_deq_bank1_VPN <= REQ_deq_bank1_VPN;
			last_REQ_deq_bank1_PO_word <= REQ_deq_bank1_PO_word;
			last_REQ_deq_bank1_byte_mask <= REQ_deq_bank1_byte_mask;
			last_REQ_deq_bank1_write_data <= REQ_deq_bank1_write_data;
			last_REQ_deq_bank1_cq_index <= REQ_deq_bank1_cq_index;

		    // REQ stage deq feedback bank 1
			REQ_deq_bank1_ack <= next_REQ_deq_bank1_ack;
        end
    end

endmodule