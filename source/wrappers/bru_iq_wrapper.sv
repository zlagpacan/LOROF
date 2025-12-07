/*
    Filename: bru_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bru_iq module. 
    Spec: LOROF/spec/design/bru_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module bru_iq_wrapper #(
	parameter BRU_IQ_ENTRIES = 6,
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
	input logic next_iq_enq_valid,
	input logic [3:0] next_iq_enq_op,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_iq_enq_pred_info,
	input logic next_iq_enq_pred_lru,
	input logic next_iq_enq_is_link_ra,
	input logic next_iq_enq_is_ret_ra,
	input logic [31:0] next_iq_enq_PC,
	input logic [31:0] next_iq_enq_pred_PC,
	input logic [19:0] next_iq_enq_imm20,
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

    // fast forward notifs
	input logic [FAST_FORWARD_PIPE_COUNT-1:0] next_fast_forward_notif_valid_by_pipe,
	input logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0] next_fast_forward_notif_PR_by_pipe,

    // pipeline issue
	output logic last_issue_valid,
	output logic [3:0] last_issue_op,
	output logic [BTB_PRED_INFO_WIDTH-1:0] last_issue_pred_info,
	output logic last_issue_pred_lru,
	output logic last_issue_is_link_ra,
	output logic last_issue_is_ret_ra,
	output logic [31:0] last_issue_PC,
	output logic [31:0] last_issue_pred_PC,
	output logic [19:0] last_issue_imm20,
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
	output logic [LOG_PR_COUNT-1:0] last_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_ROB_index,

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
	logic iq_enq_valid;
	logic [3:0] iq_enq_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] iq_enq_pred_info;
	logic iq_enq_pred_lru;
	logic iq_enq_is_link_ra;
	logic iq_enq_is_ret_ra;
	logic [31:0] iq_enq_PC;
	logic [31:0] iq_enq_pred_PC;
	logic [19:0] iq_enq_imm20;
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

    // fast forward notifs
	logic [FAST_FORWARD_PIPE_COUNT-1:0] fast_forward_notif_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0] fast_forward_notif_PR_by_pipe;

    // pipeline issue
	logic issue_valid;
	logic [3:0] issue_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] issue_pred_info;
	logic issue_pred_lru;
	logic issue_is_link_ra;
	logic issue_is_ret_ra;
	logic [31:0] issue_PC;
	logic [31:0] issue_pred_PC;
	logic [19:0] issue_imm20;
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
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // pipeline feedback
	logic issue_ready;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;
	logic PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

	bru_iq #(
		.BRU_IQ_ENTRIES(BRU_IQ_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to issue queue
			iq_enq_valid <= '0;
			iq_enq_op <= '0;
			iq_enq_pred_info <= '0;
			iq_enq_pred_lru <= '0;
			iq_enq_is_link_ra <= '0;
			iq_enq_is_ret_ra <= '0;
			iq_enq_PC <= '0;
			iq_enq_pred_PC <= '0;
			iq_enq_imm20 <= '0;
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

		    // fast forward notifs
			fast_forward_notif_valid_by_pipe <= '0;
			fast_forward_notif_PR_by_pipe <= '0;

		    // pipeline issue
			last_issue_valid <= '0;
			last_issue_op <= '0;
			last_issue_pred_info <= '0;
			last_issue_pred_lru <= '0;
			last_issue_is_link_ra <= '0;
			last_issue_is_ret_ra <= '0;
			last_issue_PC <= '0;
			last_issue_pred_PC <= '0;
			last_issue_imm20 <= '0;
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
			last_issue_dest_PR <= '0;
			last_issue_ROB_index <= '0;

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
			iq_enq_valid <= next_iq_enq_valid;
			iq_enq_op <= next_iq_enq_op;
			iq_enq_pred_info <= next_iq_enq_pred_info;
			iq_enq_pred_lru <= next_iq_enq_pred_lru;
			iq_enq_is_link_ra <= next_iq_enq_is_link_ra;
			iq_enq_is_ret_ra <= next_iq_enq_is_ret_ra;
			iq_enq_PC <= next_iq_enq_PC;
			iq_enq_pred_PC <= next_iq_enq_pred_PC;
			iq_enq_imm20 <= next_iq_enq_imm20;
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

		    // fast forward notifs
			fast_forward_notif_valid_by_pipe <= next_fast_forward_notif_valid_by_pipe;
			fast_forward_notif_PR_by_pipe <= next_fast_forward_notif_PR_by_pipe;

		    // pipeline issue
			last_issue_valid <= issue_valid;
			last_issue_op <= issue_op;
			last_issue_pred_info <= issue_pred_info;
			last_issue_pred_lru <= issue_pred_lru;
			last_issue_is_link_ra <= issue_is_link_ra;
			last_issue_is_ret_ra <= issue_is_ret_ra;
			last_issue_PC <= issue_PC;
			last_issue_pred_PC <= issue_pred_PC;
			last_issue_imm20 <= issue_imm20;
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
			last_issue_dest_PR <= issue_dest_PR;
			last_issue_ROB_index <= issue_ROB_index;

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