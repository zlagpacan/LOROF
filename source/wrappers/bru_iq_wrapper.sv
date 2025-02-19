/*
    Filename: bru_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bru_iq module. 
    Spec: LOROF/spec/design/bru_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_iq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // op dispatch by way
	input logic [3:0] next_dispatch_attempt_by_way,
	input logic [3:0] next_dispatch_valid_by_way,
	input logic [3:0][3:0] next_dispatch_op_by_way,
	input logic [3:0][BTB_PRED_INFO_WIDTH-1:0] next_dispatch_pred_info_by_way,
	input logic [3:0] next_dispatch_pred_lru_by_way,
	input logic [3:0] next_dispatch_is_link_ra_by_way,
	input logic [3:0] next_dispatch_is_ret_ra_by_way,
	input logic [3:0][31:0] next_dispatch_PC_by_way,
	input logic [3:0][31:0] next_dispatch_pred_PC_by_way,
	input logic [3:0][19:0] next_dispatch_imm20_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_way,
	input logic [3:0] next_dispatch_A_unneeded_by_way,
	input logic [3:0] next_dispatch_A_ready_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_B_PR_by_way,
	input logic [3:0] next_dispatch_B_unneeded_by_way,
	input logic [3:0] next_dispatch_B_ready_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_way,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_way,

    // op dispatch feedback
	output logic [3:0] last_dispatch_ack_by_way,

    // BRU pipeline feedback
	input logic next_pipeline_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // BRU op issue to BRU pipeline
	output logic last_issue_valid,
	output logic [3:0] last_issue_op,
	output logic [BTB_PRED_INFO_WIDTH-1:0] last_issue_pred_info,
	output logic last_issue_pred_lru,
	output logic last_issue_is_link_ra,
	output logic last_issue_is_ret_ra,
	output logic [31:0] last_issue_PC,
	output logic [31:0] last_issue_pred_PC,
	output logic [19:0] last_issue_imm20,
	output logic last_issue_A_unneeded,
	output logic last_issue_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_A_bank,
	output logic last_issue_B_unneeded,
	output logic last_issue_B_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_B_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_ROB_index,

    // reg read req to PRF
	output logic last_PRF_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_A_PR,
	output logic last_PRF_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // op dispatch by way
	logic [3:0] dispatch_attempt_by_way;
	logic [3:0] dispatch_valid_by_way;
	logic [3:0][3:0] dispatch_op_by_way;
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0] dispatch_pred_info_by_way;
	logic [3:0] dispatch_pred_lru_by_way;
	logic [3:0] dispatch_is_link_ra_by_way;
	logic [3:0] dispatch_is_ret_ra_by_way;
	logic [3:0][31:0] dispatch_PC_by_way;
	logic [3:0][31:0] dispatch_pred_PC_by_way;
	logic [3:0][19:0] dispatch_imm20_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_way;
	logic [3:0] dispatch_A_unneeded_by_way;
	logic [3:0] dispatch_A_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_B_PR_by_way;
	logic [3:0] dispatch_B_unneeded_by_way;
	logic [3:0] dispatch_B_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] dispatch_ack_by_way;

    // BRU pipeline feedback
	logic pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // BRU op issue to BRU pipeline
	logic issue_valid;
	logic [3:0] issue_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] issue_pred_info;
	logic issue_pred_lru;
	logic issue_is_link_ra;
	logic issue_is_ret_ra;
	logic [31:0] issue_PC;
	logic [31:0] issue_pred_PC;
	logic [19:0] issue_imm20;
	logic issue_A_unneeded;
	logic issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic issue_B_unneeded;
	logic issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_B_bank;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;
	logic PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    bru_iq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // op dispatch by way
			dispatch_attempt_by_way <= '0;
			dispatch_valid_by_way <= '0;
			dispatch_op_by_way <= '0;
			dispatch_pred_info_by_way <= '0;
			dispatch_pred_lru_by_way <= '0;
			dispatch_is_link_ra_by_way <= '0;
			dispatch_is_ret_ra_by_way <= '0;
			dispatch_PC_by_way <= '0;
			dispatch_pred_PC_by_way <= '0;
			dispatch_imm20_by_way <= '0;
			dispatch_A_PR_by_way <= '0;
			dispatch_A_unneeded_by_way <= '0;
			dispatch_A_ready_by_way <= '0;
			dispatch_B_PR_by_way <= '0;
			dispatch_B_unneeded_by_way <= '0;
			dispatch_B_ready_by_way <= '0;
			dispatch_dest_PR_by_way <= '0;
			dispatch_ROB_index_by_way <= '0;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= '0;

		    // BRU pipeline feedback
			pipeline_ready <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // BRU op issue to BRU pipeline
			last_issue_valid <= '0;
			last_issue_op <= '0;
			last_issue_pred_info <= '0;
			last_issue_pred_lru <= '0;
			last_issue_is_link_ra <= '0;
			last_issue_is_ret_ra <= '0;
			last_issue_PC <= '0;
			last_issue_pred_PC <= '0;
			last_issue_imm20 <= '0;
			last_issue_A_unneeded <= '0;
			last_issue_A_forward <= '0;
			last_issue_A_bank <= '0;
			last_issue_B_unneeded <= '0;
			last_issue_B_forward <= '0;
			last_issue_B_bank <= '0;
			last_issue_dest_PR <= '0;
			last_issue_ROB_index <= '0;

		    // reg read req to PRF
			last_PRF_req_A_valid <= '0;
			last_PRF_req_A_PR <= '0;
			last_PRF_req_B_valid <= '0;
			last_PRF_req_B_PR <= '0;
        end
        else begin


		    // op dispatch by way
			dispatch_attempt_by_way <= next_dispatch_attempt_by_way;
			dispatch_valid_by_way <= next_dispatch_valid_by_way;
			dispatch_op_by_way <= next_dispatch_op_by_way;
			dispatch_pred_info_by_way <= next_dispatch_pred_info_by_way;
			dispatch_pred_lru_by_way <= next_dispatch_pred_lru_by_way;
			dispatch_is_link_ra_by_way <= next_dispatch_is_link_ra_by_way;
			dispatch_is_ret_ra_by_way <= next_dispatch_is_ret_ra_by_way;
			dispatch_PC_by_way <= next_dispatch_PC_by_way;
			dispatch_pred_PC_by_way <= next_dispatch_pred_PC_by_way;
			dispatch_imm20_by_way <= next_dispatch_imm20_by_way;
			dispatch_A_PR_by_way <= next_dispatch_A_PR_by_way;
			dispatch_A_unneeded_by_way <= next_dispatch_A_unneeded_by_way;
			dispatch_A_ready_by_way <= next_dispatch_A_ready_by_way;
			dispatch_B_PR_by_way <= next_dispatch_B_PR_by_way;
			dispatch_B_unneeded_by_way <= next_dispatch_B_unneeded_by_way;
			dispatch_B_ready_by_way <= next_dispatch_B_ready_by_way;
			dispatch_dest_PR_by_way <= next_dispatch_dest_PR_by_way;
			dispatch_ROB_index_by_way <= next_dispatch_ROB_index_by_way;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= dispatch_ack_by_way;

		    // BRU pipeline feedback
			pipeline_ready <= next_pipeline_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // BRU op issue to BRU pipeline
			last_issue_valid <= issue_valid;
			last_issue_op <= issue_op;
			last_issue_pred_info <= issue_pred_info;
			last_issue_pred_lru <= issue_pred_lru;
			last_issue_is_link_ra <= issue_is_link_ra;
			last_issue_is_ret_ra <= issue_is_ret_ra;
			last_issue_PC <= issue_PC;
			last_issue_pred_PC <= issue_pred_PC;
			last_issue_imm20 <= issue_imm20;
			last_issue_A_unneeded <= issue_A_unneeded;
			last_issue_A_forward <= issue_A_forward;
			last_issue_A_bank <= issue_A_bank;
			last_issue_B_unneeded <= issue_B_unneeded;
			last_issue_B_forward <= issue_B_forward;
			last_issue_B_bank <= issue_B_bank;
			last_issue_dest_PR <= issue_dest_PR;
			last_issue_ROB_index <= issue_ROB_index;

		    // reg read req to PRF
			last_PRF_req_A_valid <= PRF_req_A_valid;
			last_PRF_req_A_PR <= PRF_req_A_PR;
			last_PRF_req_B_valid <= PRF_req_B_valid;
			last_PRF_req_B_PR <= PRF_req_B_PR;
        end
    end

endmodule