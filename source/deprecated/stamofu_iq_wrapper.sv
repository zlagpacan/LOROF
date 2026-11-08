/*
    Filename: stamofu_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_iq module. 
    Spec: LOROF/spec/design/stamofu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_iq_wrapper #(
	parameter STAMOFU_IQ_ENTRIES = 8,
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
	input logic next_stamofu_iq_enq_valid,
	input logic next_stamofu_iq_enq_is_store,
	input logic next_stamofu_iq_enq_is_amo,
	input logic next_stamofu_iq_enq_is_fence,
	input logic [3:0] next_stamofu_iq_enq_op,
	input logic [11:0] next_stamofu_iq_enq_imm12,
	input logic [LOG_PR_COUNT-1:0] next_stamofu_iq_enq_A_PR,
	input logic next_stamofu_iq_enq_A_ready,
	input logic next_stamofu_iq_enq_A_is_zero,
	input logic [LOG_PR_COUNT-1:0] next_stamofu_iq_enq_B_PR,
	input logic next_stamofu_iq_enq_B_ready,
	input logic next_stamofu_iq_enq_B_is_zero,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_iq_enq_cq_index,

    // issue queue enqueue feedback
	output logic last_stamofu_iq_enq_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // fast forward notifs
	input logic [FAST_FORWARD_PIPE_COUNT-1:0] next_fast_forward_notif_valid_by_pipe,
	input logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0] next_fast_forward_notif_PR_by_pipe,

    // pipeline issue 
	output logic last_issue_valid,
	output logic last_issue_is_store,
	output logic last_issue_is_amo,
	output logic last_issue_is_fence,
	output logic [3:0] last_issue_op,
	output logic [11:0] last_issue_imm12,
	output logic last_issue_A_is_reg,
	output logic last_issue_A_is_bus_forward,
	output logic last_issue_A_is_fast_forward,
	output logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] last_issue_A_fast_forward_pipe,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_A_bank,
	output logic last_issue_B_is_reg,
	output logic last_issue_B_is_bus_forward,
	output logic last_issue_B_is_fast_forward,
	output logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] last_issue_B_fast_forward_pipe,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_B_bank,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_issue_cq_index,

    // pipeline feedback
	input logic next_issue_ready,

    // reg read req to PRF
	output logic last_PRF_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_A_PR,
	output logic last_PRF_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op enqueue to issue queue
	logic stamofu_iq_enq_valid;
	logic stamofu_iq_enq_is_store;
	logic stamofu_iq_enq_is_amo;
	logic stamofu_iq_enq_is_fence;
	logic [3:0] stamofu_iq_enq_op;
	logic [11:0] stamofu_iq_enq_imm12;
	logic [LOG_PR_COUNT-1:0] stamofu_iq_enq_A_PR;
	logic stamofu_iq_enq_A_ready;
	logic stamofu_iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] stamofu_iq_enq_B_PR;
	logic stamofu_iq_enq_B_ready;
	logic stamofu_iq_enq_B_is_zero;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic stamofu_iq_enq_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // fast forward notifs
	logic [FAST_FORWARD_PIPE_COUNT-1:0] fast_forward_notif_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0] fast_forward_notif_PR_by_pipe;

    // pipeline issue 
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

    // pipeline feedback
	logic issue_ready;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;
	logic PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

	stamofu_iq #(
		.STAMOFU_IQ_ENTRIES(STAMOFU_IQ_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to issue queue
			stamofu_iq_enq_valid <= '0;
			stamofu_iq_enq_is_store <= '0;
			stamofu_iq_enq_is_amo <= '0;
			stamofu_iq_enq_is_fence <= '0;
			stamofu_iq_enq_op <= '0;
			stamofu_iq_enq_imm12 <= '0;
			stamofu_iq_enq_A_PR <= '0;
			stamofu_iq_enq_A_ready <= '0;
			stamofu_iq_enq_A_is_zero <= '0;
			stamofu_iq_enq_B_PR <= '0;
			stamofu_iq_enq_B_ready <= '0;
			stamofu_iq_enq_B_is_zero <= '0;
			stamofu_iq_enq_cq_index <= '0;

		    // issue queue enqueue feedback
			last_stamofu_iq_enq_ready <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // fast forward notifs
			fast_forward_notif_valid_by_pipe <= '0;
			fast_forward_notif_PR_by_pipe <= '0;

		    // pipeline issue 
			last_issue_valid <= '0;
			last_issue_is_store <= '0;
			last_issue_is_amo <= '0;
			last_issue_is_fence <= '0;
			last_issue_op <= '0;
			last_issue_imm12 <= '0;
			last_issue_A_is_reg <= '0;
			last_issue_A_is_bus_forward <= '0;
			last_issue_A_is_fast_forward <= '0;
			last_issue_A_fast_forward_pipe <= '0;
			last_issue_A_bank <= '0;
			last_issue_B_is_reg <= '0;
			last_issue_B_is_bus_forward <= '0;
			last_issue_B_is_fast_forward <= '0;
			last_issue_B_fast_forward_pipe <= '0;
			last_issue_B_bank <= '0;
			last_issue_cq_index <= '0;

		    // pipeline feedback
			issue_ready <= '0;

		    // reg read req to PRF
			last_PRF_req_A_valid <= '0;
			last_PRF_req_A_PR <= '0;
			last_PRF_req_B_valid <= '0;
			last_PRF_req_B_PR <= '0;
        end
        else begin

		    // op enqueue to issue queue
			stamofu_iq_enq_valid <= next_stamofu_iq_enq_valid;
			stamofu_iq_enq_is_store <= next_stamofu_iq_enq_is_store;
			stamofu_iq_enq_is_amo <= next_stamofu_iq_enq_is_amo;
			stamofu_iq_enq_is_fence <= next_stamofu_iq_enq_is_fence;
			stamofu_iq_enq_op <= next_stamofu_iq_enq_op;
			stamofu_iq_enq_imm12 <= next_stamofu_iq_enq_imm12;
			stamofu_iq_enq_A_PR <= next_stamofu_iq_enq_A_PR;
			stamofu_iq_enq_A_ready <= next_stamofu_iq_enq_A_ready;
			stamofu_iq_enq_A_is_zero <= next_stamofu_iq_enq_A_is_zero;
			stamofu_iq_enq_B_PR <= next_stamofu_iq_enq_B_PR;
			stamofu_iq_enq_B_ready <= next_stamofu_iq_enq_B_ready;
			stamofu_iq_enq_B_is_zero <= next_stamofu_iq_enq_B_is_zero;
			stamofu_iq_enq_cq_index <= next_stamofu_iq_enq_cq_index;

		    // issue queue enqueue feedback
			last_stamofu_iq_enq_ready <= stamofu_iq_enq_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // fast forward notifs
			fast_forward_notif_valid_by_pipe <= next_fast_forward_notif_valid_by_pipe;
			fast_forward_notif_PR_by_pipe <= next_fast_forward_notif_PR_by_pipe;

		    // pipeline issue 
			last_issue_valid <= issue_valid;
			last_issue_is_store <= issue_is_store;
			last_issue_is_amo <= issue_is_amo;
			last_issue_is_fence <= issue_is_fence;
			last_issue_op <= issue_op;
			last_issue_imm12 <= issue_imm12;
			last_issue_A_is_reg <= issue_A_is_reg;
			last_issue_A_is_bus_forward <= issue_A_is_bus_forward;
			last_issue_A_is_fast_forward <= issue_A_is_fast_forward;
			last_issue_A_fast_forward_pipe <= issue_A_fast_forward_pipe;
			last_issue_A_bank <= issue_A_bank;
			last_issue_B_is_reg <= issue_B_is_reg;
			last_issue_B_is_bus_forward <= issue_B_is_bus_forward;
			last_issue_B_is_fast_forward <= issue_B_is_fast_forward;
			last_issue_B_fast_forward_pipe <= issue_B_fast_forward_pipe;
			last_issue_B_bank <= issue_B_bank;
			last_issue_cq_index <= issue_cq_index;

		    // pipeline feedback
			issue_ready <= next_issue_ready;

		    // reg read req to PRF
			last_PRF_req_A_valid <= PRF_req_A_valid;
			last_PRF_req_A_PR <= PRF_req_A_PR;
			last_PRF_req_B_valid <= PRF_req_B_valid;
			last_PRF_req_B_PR <= PRF_req_B_PR;
        end
    end

endmodule