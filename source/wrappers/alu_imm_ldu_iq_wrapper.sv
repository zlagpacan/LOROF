/*
    Filename: alu_imm_ldu_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_imm_ldu_iq module. 
    Spec: LOROF/spec/design/alu_imm_ldu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_ldu_iq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
	input logic [3:0] next_dispatch_attempt_by_way,
	input logic [3:0] next_dispatch_valid_alu_imm_by_way,
	input logic [3:0] next_dispatch_valid_ldu_by_way,
	input logic [3:0][3:0] next_dispatch_op_by_way,
	input logic [3:0][11:0] next_dispatch_imm12_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_way,
	input logic [3:0] next_dispatch_A_ready_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_way,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_way,

    // op dispatch feedback
	output logic [3:0] last_dispatch_ack_by_way,

    // pipeline feedback
	input logic next_alu_imm_pipeline_ready,
	input logic next_ldu_pipeline_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // op issue to ALU Reg-Imm Pipeline
	output logic last_issue_alu_imm_valid,
	output logic [3:0] last_issue_alu_imm_op,
	output logic [11:0] last_issue_alu_imm_imm12,
	output logic last_issue_alu_imm_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_alu_imm_A_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_alu_imm_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_alu_imm_ROB_index,

    // ALU Reg-Imm Pipeline reg read req to PRF
	output logic last_PRF_alu_imm_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_alu_imm_req_A_PR,

    // op issue to LDU Pipeline
	output logic last_issue_ldu_valid,
	output logic [3:0] last_issue_ldu_op,
	output logic [11:0] last_issue_ldu_imm12,
	output logic last_issue_ldu_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_ldu_A_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_ldu_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_ldu_ROB_index,

    // LDU Pipeline reg read req to PRF
	output logic last_PRF_ldu_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_ldu_req_A_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op dispatch by way
	logic [3:0] dispatch_attempt_by_way;
	logic [3:0] dispatch_valid_alu_imm_by_way;
	logic [3:0] dispatch_valid_ldu_by_way;
	logic [3:0][3:0] dispatch_op_by_way;
	logic [3:0][11:0] dispatch_imm12_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_way;
	logic [3:0] dispatch_A_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] dispatch_ack_by_way;

    // pipeline feedback
	logic alu_imm_pipeline_ready;
	logic ldu_pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // op issue to ALU Reg-Imm Pipeline
	logic issue_alu_imm_valid;
	logic [3:0] issue_alu_imm_op;
	logic [11:0] issue_alu_imm_imm12;
	logic issue_alu_imm_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_alu_imm_A_bank;
	logic [LOG_PR_COUNT-1:0] issue_alu_imm_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_alu_imm_ROB_index;

    // ALU Reg-Imm Pipeline reg read req to PRF
	logic PRF_alu_imm_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_alu_imm_req_A_PR;

    // op issue to LDU Pipeline
	logic issue_ldu_valid;
	logic [3:0] issue_ldu_op;
	logic [11:0] issue_ldu_imm12;
	logic issue_ldu_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_ldu_A_bank;
	logic [LOG_PR_COUNT-1:0] issue_ldu_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ldu_ROB_index;

    // LDU Pipeline reg read req to PRF
	logic PRF_ldu_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_ldu_req_A_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_imm_ldu_iq #(.ALU_IMM_LDU_IQ_ENTRIES(ALU_IMM_LDU_IQ_ENTRIES)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op dispatch by way
			dispatch_attempt_by_way <= '0;
			dispatch_valid_alu_imm_by_way <= '0;
			dispatch_valid_ldu_by_way <= '0;
			dispatch_op_by_way <= '0;
			dispatch_imm12_by_way <= '0;
			dispatch_A_PR_by_way <= '0;
			dispatch_A_ready_by_way <= '0;
			dispatch_dest_PR_by_way <= '0;
			dispatch_ROB_index_by_way <= '0;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= '0;

		    // pipeline feedback
			alu_imm_pipeline_ready <= '0;
			ldu_pipeline_ready <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // op issue to ALU Reg-Imm Pipeline
			last_issue_alu_imm_valid <= '0;
			last_issue_alu_imm_op <= '0;
			last_issue_alu_imm_imm12 <= '0;
			last_issue_alu_imm_A_forward <= '0;
			last_issue_alu_imm_A_bank <= '0;
			last_issue_alu_imm_dest_PR <= '0;
			last_issue_alu_imm_ROB_index <= '0;

		    // ALU Reg-Imm Pipeline reg read req to PRF
			last_PRF_alu_imm_req_A_valid <= '0;
			last_PRF_alu_imm_req_A_PR <= '0;

		    // op issue to LDU Pipeline
			last_issue_ldu_valid <= '0;
			last_issue_ldu_op <= '0;
			last_issue_ldu_imm12 <= '0;
			last_issue_ldu_A_forward <= '0;
			last_issue_ldu_A_bank <= '0;
			last_issue_ldu_dest_PR <= '0;
			last_issue_ldu_ROB_index <= '0;

		    // LDU Pipeline reg read req to PRF
			last_PRF_ldu_req_A_valid <= '0;
			last_PRF_ldu_req_A_PR <= '0;
        end
        else begin

		    // op dispatch by way
			dispatch_attempt_by_way <= next_dispatch_attempt_by_way;
			dispatch_valid_alu_imm_by_way <= next_dispatch_valid_alu_imm_by_way;
			dispatch_valid_ldu_by_way <= next_dispatch_valid_ldu_by_way;
			dispatch_op_by_way <= next_dispatch_op_by_way;
			dispatch_imm12_by_way <= next_dispatch_imm12_by_way;
			dispatch_A_PR_by_way <= next_dispatch_A_PR_by_way;
			dispatch_A_ready_by_way <= next_dispatch_A_ready_by_way;
			dispatch_dest_PR_by_way <= next_dispatch_dest_PR_by_way;
			dispatch_ROB_index_by_way <= next_dispatch_ROB_index_by_way;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= dispatch_ack_by_way;

		    // pipeline feedback
			alu_imm_pipeline_ready <= next_alu_imm_pipeline_ready;
			ldu_pipeline_ready <= next_ldu_pipeline_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // op issue to ALU Reg-Imm Pipeline
			last_issue_alu_imm_valid <= issue_alu_imm_valid;
			last_issue_alu_imm_op <= issue_alu_imm_op;
			last_issue_alu_imm_imm12 <= issue_alu_imm_imm12;
			last_issue_alu_imm_A_forward <= issue_alu_imm_A_forward;
			last_issue_alu_imm_A_bank <= issue_alu_imm_A_bank;
			last_issue_alu_imm_dest_PR <= issue_alu_imm_dest_PR;
			last_issue_alu_imm_ROB_index <= issue_alu_imm_ROB_index;

		    // ALU Reg-Imm Pipeline reg read req to PRF
			last_PRF_alu_imm_req_A_valid <= PRF_alu_imm_req_A_valid;
			last_PRF_alu_imm_req_A_PR <= PRF_alu_imm_req_A_PR;

		    // op issue to LDU Pipeline
			last_issue_ldu_valid <= issue_ldu_valid;
			last_issue_ldu_op <= issue_ldu_op;
			last_issue_ldu_imm12 <= issue_ldu_imm12;
			last_issue_ldu_A_forward <= issue_ldu_A_forward;
			last_issue_ldu_A_bank <= issue_ldu_A_bank;
			last_issue_ldu_dest_PR <= issue_ldu_dest_PR;
			last_issue_ldu_ROB_index <= issue_ldu_ROB_index;

		    // LDU Pipeline reg read req to PRF
			last_PRF_ldu_req_A_valid <= PRF_ldu_req_A_valid;
			last_PRF_ldu_req_A_PR <= PRF_ldu_req_A_PR;
        end
    end

endmodule