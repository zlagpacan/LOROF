/*
    Filename: bru_pipeline_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bru_pipeline module. 
    Spec: LOROF/spec/design/bru_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module bru_pipeline_wrapper #(
	parameter IS_OC_BUFFER_SIZE = 2,
	parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3
) (

    // seq
    input logic CLK,
    input logic nRST,


    // BRU op issue from BRU IQ
	input logic next_issue_valid,
	input logic [3:0] next_issue_op,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_issue_pred_info,
	input logic next_issue_pred_lru,
	input logic next_issue_is_link_ra,
	input logic next_issue_is_ret_ra,
	input logic [31:0] next_issue_PC,
	input logic [31:0] next_issue_pred_PC,
	input logic [19:0] next_issue_imm20,
	input logic next_issue_A_unneeded_or_is_zero,
	input logic next_issue_A_forward,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_A_bank,
	input logic next_issue_B_unneeded_or_is_zero,
	input logic next_issue_B_forward,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_issue_B_bank,
	input logic [LOG_PR_COUNT-1:0] next_issue_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_issue_ROB_index,

    // output feedback to BRU IQ
	output logic last_issue_ready,

    // reg read data from PRF
	input logic next_A_reg_read_resp_valid,
	input logic [31:0] next_A_reg_read_resp_data,
	input logic next_B_reg_read_resp_valid,
	input logic [31:0] next_B_reg_read_resp_data,

    // forward data from PRF
	input logic [PRF_BANK_COUNT-1:0][31:0] next_forward_data_by_bank,

    // writeback data to PRF
	output logic last_WB_valid,
	output logic [31:0] last_WB_data,
	output logic [LOG_PR_COUNT-1:0] last_WB_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_WB_ROB_index,

    // writeback backpressure from PRF
	input logic next_WB_ready,

    // branch notification to ROB
	output logic last_branch_notif_valid,
	output logic [LOG_ROB_ENTRIES-1:0] last_branch_notif_ROB_index,
	output logic last_branch_notif_is_mispredict,
	output logic last_branch_notif_is_taken,
	output logic last_branch_notif_use_upct,
	output logic [BTB_PRED_INFO_WIDTH-1:0] last_branch_notif_updated_pred_info,
	output logic last_branch_notif_pred_lru,
	output logic [31:0] last_branch_notif_start_PC,
	output logic [31:0] last_branch_notif_target_PC,

    // branch notification backpressure from ROB
	input logic next_branch_notif_ready
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // BRU op issue from BRU IQ
	logic issue_valid;
	logic [3:0] issue_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] issue_pred_info;
	logic issue_pred_lru;
	logic issue_is_link_ra;
	logic issue_is_ret_ra;
	logic [31:0] issue_PC;
	logic [31:0] issue_pred_PC;
	logic [19:0] issue_imm20;
	logic issue_A_unneeded_or_is_zero;
	logic issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic issue_B_unneeded_or_is_zero;
	logic issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_B_bank;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // output feedback to BRU IQ
	logic issue_ready;

    // reg read data from PRF
	logic A_reg_read_resp_valid;
	logic [31:0] A_reg_read_resp_data;
	logic B_reg_read_resp_valid;
	logic [31:0] B_reg_read_resp_data;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank;

    // writeback data to PRF
	logic WB_valid;
	logic [31:0] WB_data;
	logic [LOG_PR_COUNT-1:0] WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index;

    // writeback backpressure from PRF
	logic WB_ready;

    // branch notification to ROB
	logic branch_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] branch_notif_ROB_index;
	logic branch_notif_is_mispredict;
	logic branch_notif_is_taken;
	logic branch_notif_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] branch_notif_updated_pred_info;
	logic branch_notif_pred_lru;
	logic [31:0] branch_notif_start_PC;
	logic [31:0] branch_notif_target_PC;

    // branch notification backpressure from ROB
	logic branch_notif_ready;

    // ----------------------------------------------------------------
    // Module Instantiation:

	bru_pipeline #(
		.IS_OC_BUFFER_SIZE(IS_OC_BUFFER_SIZE),
		.PRF_RR_OUTPUT_BUFFER_SIZE(PRF_RR_OUTPUT_BUFFER_SIZE)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // BRU op issue from BRU IQ
			issue_valid <= '0;
			issue_op <= '0;
			issue_pred_info <= '0;
			issue_pred_lru <= '0;
			issue_is_link_ra <= '0;
			issue_is_ret_ra <= '0;
			issue_PC <= '0;
			issue_pred_PC <= '0;
			issue_imm20 <= '0;
			issue_A_unneeded_or_is_zero <= '0;
			issue_A_forward <= '0;
			issue_A_bank <= '0;
			issue_B_unneeded_or_is_zero <= '0;
			issue_B_forward <= '0;
			issue_B_bank <= '0;
			issue_dest_PR <= '0;
			issue_ROB_index <= '0;

		    // output feedback to BRU IQ
			last_issue_ready <= '0;

		    // reg read data from PRF
			A_reg_read_resp_valid <= '0;
			A_reg_read_resp_data <= '0;
			B_reg_read_resp_valid <= '0;
			B_reg_read_resp_data <= '0;

		    // forward data from PRF
			forward_data_by_bank <= '0;

		    // writeback data to PRF
			last_WB_valid <= '0;
			last_WB_data <= '0;
			last_WB_PR <= '0;
			last_WB_ROB_index <= '0;

		    // writeback backpressure from PRF
			WB_ready <= '0;

		    // branch notification to ROB
			last_branch_notif_valid <= '0;
			last_branch_notif_ROB_index <= '0;
			last_branch_notif_is_mispredict <= '0;
			last_branch_notif_is_taken <= '0;
			last_branch_notif_use_upct <= '0;
			last_branch_notif_updated_pred_info <= '0;
			last_branch_notif_pred_lru <= '0;
			last_branch_notif_start_PC <= '0;
			last_branch_notif_target_PC <= '0;

		    // branch notification backpressure from ROB
			branch_notif_ready <= '0;
        end
        else begin


		    // BRU op issue from BRU IQ
			issue_valid <= next_issue_valid;
			issue_op <= next_issue_op;
			issue_pred_info <= next_issue_pred_info;
			issue_pred_lru <= next_issue_pred_lru;
			issue_is_link_ra <= next_issue_is_link_ra;
			issue_is_ret_ra <= next_issue_is_ret_ra;
			issue_PC <= next_issue_PC;
			issue_pred_PC <= next_issue_pred_PC;
			issue_imm20 <= next_issue_imm20;
			issue_A_unneeded_or_is_zero <= next_issue_A_unneeded_or_is_zero;
			issue_A_forward <= next_issue_A_forward;
			issue_A_bank <= next_issue_A_bank;
			issue_B_unneeded_or_is_zero <= next_issue_B_unneeded_or_is_zero;
			issue_B_forward <= next_issue_B_forward;
			issue_B_bank <= next_issue_B_bank;
			issue_dest_PR <= next_issue_dest_PR;
			issue_ROB_index <= next_issue_ROB_index;

		    // output feedback to BRU IQ
			last_issue_ready <= issue_ready;

		    // reg read data from PRF
			A_reg_read_resp_valid <= next_A_reg_read_resp_valid;
			A_reg_read_resp_data <= next_A_reg_read_resp_data;
			B_reg_read_resp_valid <= next_B_reg_read_resp_valid;
			B_reg_read_resp_data <= next_B_reg_read_resp_data;

		    // forward data from PRF
			forward_data_by_bank <= next_forward_data_by_bank;

		    // writeback data to PRF
			last_WB_valid <= WB_valid;
			last_WB_data <= WB_data;
			last_WB_PR <= WB_PR;
			last_WB_ROB_index <= WB_ROB_index;

		    // writeback backpressure from PRF
			WB_ready <= next_WB_ready;

		    // branch notification to ROB
			last_branch_notif_valid <= branch_notif_valid;
			last_branch_notif_ROB_index <= branch_notif_ROB_index;
			last_branch_notif_is_mispredict <= branch_notif_is_mispredict;
			last_branch_notif_is_taken <= branch_notif_is_taken;
			last_branch_notif_use_upct <= branch_notif_use_upct;
			last_branch_notif_updated_pred_info <= branch_notif_updated_pred_info;
			last_branch_notif_pred_lru <= branch_notif_pred_lru;
			last_branch_notif_start_PC <= branch_notif_start_PC;
			last_branch_notif_target_PC <= branch_notif_target_PC;

		    // branch notification backpressure from ROB
			branch_notif_ready <= next_branch_notif_ready;
        end
    end

endmodule