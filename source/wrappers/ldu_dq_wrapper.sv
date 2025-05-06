/*
    Filename: ldu_dq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ldu_dq module. 
    Spec: LOROF/spec/design/ldu_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ldu_dq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
	input logic [3:0] next_dispatch_attempt_by_way,
	input logic [3:0] next_dispatch_valid_by_way,
	input logic [3:0][3:0] next_dispatch_op_by_way,
	input logic [3:0][11:0] next_dispatch_imm12_by_way,
	input logic [3:0][MDPT_INFO_WIDTH-1:0] next_dispatch_mdp_info_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_way,
	input logic [3:0] next_dispatch_A_ready_by_way,
	input logic [3:0] next_dispatch_A_is_zero_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_way,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_way,

    // op dispatch feedback
	output logic [3:0] last_dispatch_ack_by_way,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // op enqueue to central queue
	output logic last_ldu_cq_enq_valid,
	output logic [MDPT_INFO_WIDTH-1:0] last_ldu_cq_enq_mdp_info,
	output logic [LOG_PR_COUNT-1:0] last_ldu_cq_enq_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_ldu_cq_enq_ROB_index,

    // central queue enqueue feedback
	input logic next_ldu_cq_enq_ready,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_cq_enq_index,

    // op enqueue to issue queue
	output logic last_ldu_iq_enq_valid,
	output logic [3:0] last_ldu_iq_enq_op,
	output logic [11:0] last_ldu_iq_enq_imm12,
	output logic [LOG_PR_COUNT-1:0] last_ldu_iq_enq_A_PR,
	output logic last_ldu_iq_enq_A_ready,
	output logic last_ldu_iq_enq_A_is_zero,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_ldu_iq_enq_cq_index,

    // issue queue enqueue feedback
	input logic next_ldu_iq_enq_ready,

    // restart from ROB
	input logic next_rob_restart_valid
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op dispatch by way
	logic [3:0] dispatch_attempt_by_way;
	logic [3:0] dispatch_valid_by_way;
	logic [3:0][3:0] dispatch_op_by_way;
	logic [3:0][11:0] dispatch_imm12_by_way;
	logic [3:0][MDPT_INFO_WIDTH-1:0] dispatch_mdp_info_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_way;
	logic [3:0] dispatch_A_ready_by_way;
	logic [3:0] dispatch_A_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // op enqueue to central queue
	logic ldu_cq_enq_valid;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_enq_mdp_info;
	logic [LOG_PR_COUNT-1:0] ldu_cq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_enq_ROB_index;

    // central queue enqueue feedback
	logic ldu_cq_enq_ready;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_enq_index;

    // op enqueue to issue queue
	logic ldu_iq_enq_valid;
	logic [3:0] ldu_iq_enq_op;
	logic [11:0] ldu_iq_enq_imm12;
	logic [LOG_PR_COUNT-1:0] ldu_iq_enq_A_PR;
	logic ldu_iq_enq_A_ready;
	logic ldu_iq_enq_A_is_zero;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic ldu_iq_enq_ready;

    // restart from ROB
	logic rob_restart_valid;

    // ----------------------------------------------------------------
    // Module Instantiation:

    ldu_dq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op dispatch by way
			dispatch_attempt_by_way <= '0;
			dispatch_valid_by_way <= '0;
			dispatch_op_by_way <= '0;
			dispatch_imm12_by_way <= '0;
			dispatch_mdp_info_by_way <= '0;
			dispatch_A_PR_by_way <= '0;
			dispatch_A_ready_by_way <= '0;
			dispatch_A_is_zero_by_way <= '0;
			dispatch_dest_PR_by_way <= '0;
			dispatch_ROB_index_by_way <= '0;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // op enqueue to central queue
			last_ldu_cq_enq_valid <= '0;
			last_ldu_cq_enq_mdp_info <= '0;
			last_ldu_cq_enq_dest_PR <= '0;
			last_ldu_cq_enq_ROB_index <= '0;

		    // central queue enqueue feedback
			ldu_cq_enq_ready <= '0;
			ldu_cq_enq_index <= '0;

		    // op enqueue to issue queue
			last_ldu_iq_enq_valid <= '0;
			last_ldu_iq_enq_op <= '0;
			last_ldu_iq_enq_imm12 <= '0;
			last_ldu_iq_enq_A_PR <= '0;
			last_ldu_iq_enq_A_ready <= '0;
			last_ldu_iq_enq_A_is_zero <= '0;
			last_ldu_iq_enq_cq_index <= '0;

		    // issue queue enqueue feedback
			ldu_iq_enq_ready <= '0;

		    // restart from ROB
			rob_restart_valid <= '0;
        end
        else begin

		    // op dispatch by way
			dispatch_attempt_by_way <= next_dispatch_attempt_by_way;
			dispatch_valid_by_way <= next_dispatch_valid_by_way;
			dispatch_op_by_way <= next_dispatch_op_by_way;
			dispatch_imm12_by_way <= next_dispatch_imm12_by_way;
			dispatch_mdp_info_by_way <= next_dispatch_mdp_info_by_way;
			dispatch_A_PR_by_way <= next_dispatch_A_PR_by_way;
			dispatch_A_ready_by_way <= next_dispatch_A_ready_by_way;
			dispatch_A_is_zero_by_way <= next_dispatch_A_is_zero_by_way;
			dispatch_dest_PR_by_way <= next_dispatch_dest_PR_by_way;
			dispatch_ROB_index_by_way <= next_dispatch_ROB_index_by_way;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= dispatch_ack_by_way;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // op enqueue to central queue
			last_ldu_cq_enq_valid <= ldu_cq_enq_valid;
			last_ldu_cq_enq_mdp_info <= ldu_cq_enq_mdp_info;
			last_ldu_cq_enq_dest_PR <= ldu_cq_enq_dest_PR;
			last_ldu_cq_enq_ROB_index <= ldu_cq_enq_ROB_index;

		    // central queue enqueue feedback
			ldu_cq_enq_ready <= next_ldu_cq_enq_ready;
			ldu_cq_enq_index <= next_ldu_cq_enq_index;

		    // op enqueue to issue queue
			last_ldu_iq_enq_valid <= ldu_iq_enq_valid;
			last_ldu_iq_enq_op <= ldu_iq_enq_op;
			last_ldu_iq_enq_imm12 <= ldu_iq_enq_imm12;
			last_ldu_iq_enq_A_PR <= ldu_iq_enq_A_PR;
			last_ldu_iq_enq_A_ready <= ldu_iq_enq_A_ready;
			last_ldu_iq_enq_A_is_zero <= ldu_iq_enq_A_is_zero;
			last_ldu_iq_enq_cq_index <= ldu_iq_enq_cq_index;

		    // issue queue enqueue feedback
			ldu_iq_enq_ready <= next_ldu_iq_enq_ready;

		    // restart from ROB
			rob_restart_valid <= next_rob_restart_valid;
        end
    end

endmodule