/*
    Filename: alu_reg_mdu_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_reg_mdu_iq module. 
    Spec: LOROF/spec/design/alu_reg_mdu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_mdu_iq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
	input logic [3:0] next_dispatch_attempt_by_way,
	input logic [3:0] next_dispatch_valid_alu_reg_by_way,
	input logic [3:0] next_dispatch_valid_mdu_by_way,
	input logic [3:0][3:0] next_dispatch_op_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_way,
	input logic [3:0] next_dispatch_A_ready_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_B_PR_by_way,
	input logic [3:0] next_dispatch_B_ready_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_way,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_way,

    // op dispatch feedback
	output logic [3:0] last_dispatch_ack_by_way,

    // pipeline feedback
	input logic next_alu_reg_pipeline_ready,
	input logic next_mdu_pipeline_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // op issue to ALU Reg-Reg Pipeline
	output logic last_issue_alu_reg_valid,
	output logic [3:0] last_issue_alu_reg_op,
	output logic last_issue_alu_reg_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_alu_reg_A_bank,
	output logic last_issue_alu_reg_B_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_alu_reg_B_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_alu_reg_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_alu_reg_ROB_index,

    // ALU Reg-Reg Pipeline reg read req to PRF
	output logic last_PRF_alu_reg_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_alu_reg_req_A_PR,
	output logic last_PRF_alu_reg_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_alu_reg_req_B_PR,

    // op issue to MDU Pipeline
	output logic last_issue_mdu_valid,
	output logic [3:0] last_issue_mdu_op,
	output logic last_issue_mdu_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_mdu_A_bank,
	output logic last_issue_mdu_B_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_mdu_B_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_mdu_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_mdu_ROB_index,

    // MDU Pipeline reg read req to PRF
	output logic last_PRF_mdu_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_mdu_req_A_PR,
	output logic last_PRF_mdu_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_mdu_req_B_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op dispatch by way
	logic [3:0] dispatch_attempt_by_way;
	logic [3:0] dispatch_valid_alu_reg_by_way;
	logic [3:0] dispatch_valid_mdu_by_way;
	logic [3:0][3:0] dispatch_op_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_way;
	logic [3:0] dispatch_A_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_B_PR_by_way;
	logic [3:0] dispatch_B_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] dispatch_ack_by_way;

    // pipeline feedback
	logic alu_reg_pipeline_ready;
	logic mdu_pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // op issue to ALU Reg-Reg Pipeline
	logic issue_alu_reg_valid;
	logic [3:0] issue_alu_reg_op;
	logic issue_alu_reg_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_alu_reg_A_bank;
	logic issue_alu_reg_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_alu_reg_B_bank;
	logic [LOG_PR_COUNT-1:0] issue_alu_reg_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_alu_reg_ROB_index;

    // ALU Reg-Reg Pipeline reg read req to PRF
	logic PRF_alu_reg_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_alu_reg_req_A_PR;
	logic PRF_alu_reg_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_alu_reg_req_B_PR;

    // op issue to MDU Pipeline
	logic issue_mdu_valid;
	logic [3:0] issue_mdu_op;
	logic issue_mdu_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_mdu_A_bank;
	logic issue_mdu_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_mdu_B_bank;
	logic [LOG_PR_COUNT-1:0] issue_mdu_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_mdu_ROB_index;

    // MDU Pipeline reg read req to PRF
	logic PRF_mdu_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_mdu_req_A_PR;
	logic PRF_mdu_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_mdu_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_reg_mdu_iq #(.ALU_REG_MDU_IQ_ENTRIES(ALU_REG_MDU_IQ_ENTRIES)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op dispatch by way
			dispatch_attempt_by_way <= '0;
			dispatch_valid_alu_reg_by_way <= '0;
			dispatch_valid_mdu_by_way <= '0;
			dispatch_op_by_way <= '0;
			dispatch_A_PR_by_way <= '0;
			dispatch_A_ready_by_way <= '0;
			dispatch_B_PR_by_way <= '0;
			dispatch_B_ready_by_way <= '0;
			dispatch_dest_PR_by_way <= '0;
			dispatch_ROB_index_by_way <= '0;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= '0;

		    // pipeline feedback
			alu_reg_pipeline_ready <= '0;
			mdu_pipeline_ready <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // op issue to ALU Reg-Reg Pipeline
			last_issue_alu_reg_valid <= '0;
			last_issue_alu_reg_op <= '0;
			last_issue_alu_reg_A_forward <= '0;
			last_issue_alu_reg_A_bank <= '0;
			last_issue_alu_reg_B_forward <= '0;
			last_issue_alu_reg_B_bank <= '0;
			last_issue_alu_reg_dest_PR <= '0;
			last_issue_alu_reg_ROB_index <= '0;

		    // ALU Reg-Reg Pipeline reg read req to PRF
			last_PRF_alu_reg_req_A_valid <= '0;
			last_PRF_alu_reg_req_A_PR <= '0;
			last_PRF_alu_reg_req_B_valid <= '0;
			last_PRF_alu_reg_req_B_PR <= '0;

		    // op issue to MDU Pipeline
			last_issue_mdu_valid <= '0;
			last_issue_mdu_op <= '0;
			last_issue_mdu_A_forward <= '0;
			last_issue_mdu_A_bank <= '0;
			last_issue_mdu_B_forward <= '0;
			last_issue_mdu_B_bank <= '0;
			last_issue_mdu_dest_PR <= '0;
			last_issue_mdu_ROB_index <= '0;

		    // MDU Pipeline reg read req to PRF
			last_PRF_mdu_req_A_valid <= '0;
			last_PRF_mdu_req_A_PR <= '0;
			last_PRF_mdu_req_B_valid <= '0;
			last_PRF_mdu_req_B_PR <= '0;
        end
        else begin

		    // op dispatch by way
			dispatch_attempt_by_way <= next_dispatch_attempt_by_way;
			dispatch_valid_alu_reg_by_way <= next_dispatch_valid_alu_reg_by_way;
			dispatch_valid_mdu_by_way <= next_dispatch_valid_mdu_by_way;
			dispatch_op_by_way <= next_dispatch_op_by_way;
			dispatch_A_PR_by_way <= next_dispatch_A_PR_by_way;
			dispatch_A_ready_by_way <= next_dispatch_A_ready_by_way;
			dispatch_B_PR_by_way <= next_dispatch_B_PR_by_way;
			dispatch_B_ready_by_way <= next_dispatch_B_ready_by_way;
			dispatch_dest_PR_by_way <= next_dispatch_dest_PR_by_way;
			dispatch_ROB_index_by_way <= next_dispatch_ROB_index_by_way;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= dispatch_ack_by_way;

		    // pipeline feedback
			alu_reg_pipeline_ready <= next_alu_reg_pipeline_ready;
			mdu_pipeline_ready <= next_mdu_pipeline_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // op issue to ALU Reg-Reg Pipeline
			last_issue_alu_reg_valid <= issue_alu_reg_valid;
			last_issue_alu_reg_op <= issue_alu_reg_op;
			last_issue_alu_reg_A_forward <= issue_alu_reg_A_forward;
			last_issue_alu_reg_A_bank <= issue_alu_reg_A_bank;
			last_issue_alu_reg_B_forward <= issue_alu_reg_B_forward;
			last_issue_alu_reg_B_bank <= issue_alu_reg_B_bank;
			last_issue_alu_reg_dest_PR <= issue_alu_reg_dest_PR;
			last_issue_alu_reg_ROB_index <= issue_alu_reg_ROB_index;

		    // ALU Reg-Reg Pipeline reg read req to PRF
			last_PRF_alu_reg_req_A_valid <= PRF_alu_reg_req_A_valid;
			last_PRF_alu_reg_req_A_PR <= PRF_alu_reg_req_A_PR;
			last_PRF_alu_reg_req_B_valid <= PRF_alu_reg_req_B_valid;
			last_PRF_alu_reg_req_B_PR <= PRF_alu_reg_req_B_PR;

		    // op issue to MDU Pipeline
			last_issue_mdu_valid <= issue_mdu_valid;
			last_issue_mdu_op <= issue_mdu_op;
			last_issue_mdu_A_forward <= issue_mdu_A_forward;
			last_issue_mdu_A_bank <= issue_mdu_A_bank;
			last_issue_mdu_B_forward <= issue_mdu_B_forward;
			last_issue_mdu_B_bank <= issue_mdu_B_bank;
			last_issue_mdu_dest_PR <= issue_mdu_dest_PR;
			last_issue_mdu_ROB_index <= issue_mdu_ROB_index;

		    // MDU Pipeline reg read req to PRF
			last_PRF_mdu_req_A_valid <= PRF_mdu_req_A_valid;
			last_PRF_mdu_req_A_PR <= PRF_mdu_req_A_PR;
			last_PRF_mdu_req_B_valid <= PRF_mdu_req_B_valid;
			last_PRF_mdu_req_B_PR <= PRF_mdu_req_B_PR;
        end
    end

endmodule