/*
    Filename: stamofu_dq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_dq module. 
    Spec: LOROF/spec/design/stamofu_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stamofu_dq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
	input logic [3:0] next_dispatch_attempt_by_way,
	input logic [3:0] next_dispatch_valid_store_by_way,
	input logic [3:0] next_dispatch_valid_amo_by_way,
	input logic [3:0] next_dispatch_valid_fence_by_way,
	input logic [3:0][3:0] next_dispatch_op_by_way,
	input logic [3:0][11:0] next_dispatch_imm12_by_way,
	input logic [3:0][MDPT_INFO_WIDTH-1:0] next_dispatch_mdp_info_by_way,
	input logic [3:0] next_dispatch_mem_aq_by_way,
	input logic [3:0] next_dispatch_io_aq_by_way,
	input logic [3:0] next_dispatch_mem_rl_by_way,
	input logic [3:0] next_dispatch_io_rl_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_way,
	input logic [3:0] next_dispatch_A_ready_by_way,
	input logic [3:0] next_dispatch_A_is_zero_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_B_PR_by_way,
	input logic [3:0] next_dispatch_B_ready_by_way,
	input logic [3:0] next_dispatch_B_is_zero_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_way,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_way,

    // op dispatch feedback
	output logic [3:0] last_dispatch_ack_by_way,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // op enqueue to central queue
	output logic last_stamofu_cq_enq_valid,
	output logic last_stamofu_cq_enq_killed,
	output logic last_stamofu_cq_enq_is_store,
	output logic last_stamofu_cq_enq_is_amo,
	output logic last_stamofu_cq_enq_is_fence,
	output logic [3:0] last_stamofu_cq_enq_op,
	output logic [MDPT_INFO_WIDTH-1:0] last_stamofu_cq_enq_mdp_info,
	output logic last_stamofu_cq_enq_mem_aq,
	output logic last_stamofu_cq_enq_io_aq,
	output logic last_stamofu_cq_enq_mem_rl,
	output logic last_stamofu_cq_enq_io_rl,
	output logic [LOG_PR_COUNT-1:0] last_stamofu_cq_enq_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_cq_enq_ROB_index,

    // central queue enqueue feedback
	input logic next_stamofu_cq_enq_ready,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_cq_enq_index,

    // op enqueue to issue queue
	output logic last_stamofu_iq_enq_valid,
	output logic last_stamofu_iq_enq_is_store,
	output logic last_stamofu_iq_enq_is_amo,
	output logic last_stamofu_iq_enq_is_fence,
	output logic [3:0] last_stamofu_iq_enq_op,
	output logic [11:0] last_stamofu_iq_enq_imm12,
	output logic [MDPT_INFO_WIDTH-1:0] last_stamofu_iq_enq_mdp_info,
	output logic last_stamofu_iq_enq_mem_aq,
	output logic last_stamofu_iq_enq_io_aq,
	output logic [LOG_PR_COUNT-1:0] last_stamofu_iq_enq_A_PR,
	output logic last_stamofu_iq_enq_A_ready,
	output logic last_stamofu_iq_enq_A_is_zero,
	output logic [LOG_PR_COUNT-1:0] last_stamofu_iq_enq_B_PR,
	output logic last_stamofu_iq_enq_B_ready,
	output logic last_stamofu_iq_enq_B_is_zero,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_iq_enq_ROB_index,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_iq_enq_cq_index,

    // issue queue enqueue feedback
	input logic next_stamofu_iq_enq_ready,

    // op enqueue to acquire queue
	output logic last_stamofu_aq_enq_valid,
	output logic last_stamofu_aq_enq_mem_aq,
	output logic last_stamofu_aq_enq_io_aq,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_aq_enq_ROB_index,

    // acquire queue enqueue feedback
	input logic next_stamofu_aq_enq_ready,

    // ROB kill
	input logic next_rob_kill_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_abs_head_index,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_rel_kill_younger_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op dispatch by way
	logic [3:0] dispatch_attempt_by_way;
	logic [3:0] dispatch_valid_store_by_way;
	logic [3:0] dispatch_valid_amo_by_way;
	logic [3:0] dispatch_valid_fence_by_way;
	logic [3:0][3:0] dispatch_op_by_way;
	logic [3:0][11:0] dispatch_imm12_by_way;
	logic [3:0][MDPT_INFO_WIDTH-1:0] dispatch_mdp_info_by_way;
	logic [3:0] dispatch_mem_aq_by_way;
	logic [3:0] dispatch_io_aq_by_way;
	logic [3:0] dispatch_mem_rl_by_way;
	logic [3:0] dispatch_io_rl_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_way;
	logic [3:0] dispatch_A_ready_by_way;
	logic [3:0] dispatch_A_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_B_PR_by_way;
	logic [3:0] dispatch_B_ready_by_way;
	logic [3:0] dispatch_B_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // op enqueue to central queue
	logic stamofu_cq_enq_valid;
	logic stamofu_cq_enq_killed;
	logic stamofu_cq_enq_is_store;
	logic stamofu_cq_enq_is_amo;
	logic stamofu_cq_enq_is_fence;
	logic [3:0] stamofu_cq_enq_op;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_enq_mdp_info;
	logic stamofu_cq_enq_mem_aq;
	logic stamofu_cq_enq_io_aq;
	logic stamofu_cq_enq_mem_rl;
	logic stamofu_cq_enq_io_rl;
	logic [LOG_PR_COUNT-1:0] stamofu_cq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_enq_ROB_index;

    // central queue enqueue feedback
	logic stamofu_cq_enq_ready;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_enq_index;

    // op enqueue to issue queue
	logic stamofu_iq_enq_valid;
	logic stamofu_iq_enq_is_store;
	logic stamofu_iq_enq_is_amo;
	logic stamofu_iq_enq_is_fence;
	logic [3:0] stamofu_iq_enq_op;
	logic [11:0] stamofu_iq_enq_imm12;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_iq_enq_mdp_info;
	logic stamofu_iq_enq_mem_aq;
	logic stamofu_iq_enq_io_aq;
	logic [LOG_PR_COUNT-1:0] stamofu_iq_enq_A_PR;
	logic stamofu_iq_enq_A_ready;
	logic stamofu_iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] stamofu_iq_enq_B_PR;
	logic stamofu_iq_enq_B_ready;
	logic stamofu_iq_enq_B_is_zero;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_iq_enq_ROB_index;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic stamofu_iq_enq_ready;

    // op enqueue to acquire queue
	logic stamofu_aq_enq_valid;
	logic stamofu_aq_enq_mem_aq;
	logic stamofu_aq_enq_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_enq_ROB_index;

    // acquire queue enqueue feedback
	logic stamofu_aq_enq_ready;

    // ROB kill
	logic rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

    stamofu_dq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op dispatch by way
			dispatch_attempt_by_way <= '0;
			dispatch_valid_store_by_way <= '0;
			dispatch_valid_amo_by_way <= '0;
			dispatch_valid_fence_by_way <= '0;
			dispatch_op_by_way <= '0;
			dispatch_imm12_by_way <= '0;
			dispatch_mdp_info_by_way <= '0;
			dispatch_mem_aq_by_way <= '0;
			dispatch_io_aq_by_way <= '0;
			dispatch_mem_rl_by_way <= '0;
			dispatch_io_rl_by_way <= '0;
			dispatch_A_PR_by_way <= '0;
			dispatch_A_ready_by_way <= '0;
			dispatch_A_is_zero_by_way <= '0;
			dispatch_B_PR_by_way <= '0;
			dispatch_B_ready_by_way <= '0;
			dispatch_B_is_zero_by_way <= '0;
			dispatch_dest_PR_by_way <= '0;
			dispatch_ROB_index_by_way <= '0;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // op enqueue to central queue
			last_stamofu_cq_enq_valid <= '0;
			last_stamofu_cq_enq_killed <= '0;
			last_stamofu_cq_enq_is_store <= '0;
			last_stamofu_cq_enq_is_amo <= '0;
			last_stamofu_cq_enq_is_fence <= '0;
			last_stamofu_cq_enq_op <= '0;
			last_stamofu_cq_enq_mdp_info <= '0;
			last_stamofu_cq_enq_mem_aq <= '0;
			last_stamofu_cq_enq_io_aq <= '0;
			last_stamofu_cq_enq_mem_rl <= '0;
			last_stamofu_cq_enq_io_rl <= '0;
			last_stamofu_cq_enq_dest_PR <= '0;
			last_stamofu_cq_enq_ROB_index <= '0;

		    // central queue enqueue feedback
			stamofu_cq_enq_ready <= '0;
			stamofu_cq_enq_index <= '0;

		    // op enqueue to issue queue
			last_stamofu_iq_enq_valid <= '0;
			last_stamofu_iq_enq_is_store <= '0;
			last_stamofu_iq_enq_is_amo <= '0;
			last_stamofu_iq_enq_is_fence <= '0;
			last_stamofu_iq_enq_op <= '0;
			last_stamofu_iq_enq_imm12 <= '0;
			last_stamofu_iq_enq_mdp_info <= '0;
			last_stamofu_iq_enq_mem_aq <= '0;
			last_stamofu_iq_enq_io_aq <= '0;
			last_stamofu_iq_enq_A_PR <= '0;
			last_stamofu_iq_enq_A_ready <= '0;
			last_stamofu_iq_enq_A_is_zero <= '0;
			last_stamofu_iq_enq_B_PR <= '0;
			last_stamofu_iq_enq_B_ready <= '0;
			last_stamofu_iq_enq_B_is_zero <= '0;
			last_stamofu_iq_enq_ROB_index <= '0;
			last_stamofu_iq_enq_cq_index <= '0;

		    // issue queue enqueue feedback
			stamofu_iq_enq_ready <= '0;

		    // op enqueue to acquire queue
			last_stamofu_aq_enq_valid <= '0;
			last_stamofu_aq_enq_mem_aq <= '0;
			last_stamofu_aq_enq_io_aq <= '0;
			last_stamofu_aq_enq_ROB_index <= '0;

		    // acquire queue enqueue feedback
			stamofu_aq_enq_ready <= '0;

		    // ROB kill
			rob_kill_valid <= '0;
			rob_kill_abs_head_index <= '0;
			rob_kill_rel_kill_younger_index <= '0;
        end
        else begin

		    // op dispatch by way
			dispatch_attempt_by_way <= next_dispatch_attempt_by_way;
			dispatch_valid_store_by_way <= next_dispatch_valid_store_by_way;
			dispatch_valid_amo_by_way <= next_dispatch_valid_amo_by_way;
			dispatch_valid_fence_by_way <= next_dispatch_valid_fence_by_way;
			dispatch_op_by_way <= next_dispatch_op_by_way;
			dispatch_imm12_by_way <= next_dispatch_imm12_by_way;
			dispatch_mdp_info_by_way <= next_dispatch_mdp_info_by_way;
			dispatch_mem_aq_by_way <= next_dispatch_mem_aq_by_way;
			dispatch_io_aq_by_way <= next_dispatch_io_aq_by_way;
			dispatch_mem_rl_by_way <= next_dispatch_mem_rl_by_way;
			dispatch_io_rl_by_way <= next_dispatch_io_rl_by_way;
			dispatch_A_PR_by_way <= next_dispatch_A_PR_by_way;
			dispatch_A_ready_by_way <= next_dispatch_A_ready_by_way;
			dispatch_A_is_zero_by_way <= next_dispatch_A_is_zero_by_way;
			dispatch_B_PR_by_way <= next_dispatch_B_PR_by_way;
			dispatch_B_ready_by_way <= next_dispatch_B_ready_by_way;
			dispatch_B_is_zero_by_way <= next_dispatch_B_is_zero_by_way;
			dispatch_dest_PR_by_way <= next_dispatch_dest_PR_by_way;
			dispatch_ROB_index_by_way <= next_dispatch_ROB_index_by_way;

		    // op dispatch feedback
			last_dispatch_ack_by_way <= dispatch_ack_by_way;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // op enqueue to central queue
			last_stamofu_cq_enq_valid <= stamofu_cq_enq_valid;
			last_stamofu_cq_enq_killed <= stamofu_cq_enq_killed;
			last_stamofu_cq_enq_is_store <= stamofu_cq_enq_is_store;
			last_stamofu_cq_enq_is_amo <= stamofu_cq_enq_is_amo;
			last_stamofu_cq_enq_is_fence <= stamofu_cq_enq_is_fence;
			last_stamofu_cq_enq_op <= stamofu_cq_enq_op;
			last_stamofu_cq_enq_mdp_info <= stamofu_cq_enq_mdp_info;
			last_stamofu_cq_enq_mem_aq <= stamofu_cq_enq_mem_aq;
			last_stamofu_cq_enq_io_aq <= stamofu_cq_enq_io_aq;
			last_stamofu_cq_enq_mem_rl <= stamofu_cq_enq_mem_rl;
			last_stamofu_cq_enq_io_rl <= stamofu_cq_enq_io_rl;
			last_stamofu_cq_enq_dest_PR <= stamofu_cq_enq_dest_PR;
			last_stamofu_cq_enq_ROB_index <= stamofu_cq_enq_ROB_index;

		    // central queue enqueue feedback
			stamofu_cq_enq_ready <= next_stamofu_cq_enq_ready;
			stamofu_cq_enq_index <= next_stamofu_cq_enq_index;

		    // op enqueue to issue queue
			last_stamofu_iq_enq_valid <= stamofu_iq_enq_valid;
			last_stamofu_iq_enq_is_store <= stamofu_iq_enq_is_store;
			last_stamofu_iq_enq_is_amo <= stamofu_iq_enq_is_amo;
			last_stamofu_iq_enq_is_fence <= stamofu_iq_enq_is_fence;
			last_stamofu_iq_enq_op <= stamofu_iq_enq_op;
			last_stamofu_iq_enq_imm12 <= stamofu_iq_enq_imm12;
			last_stamofu_iq_enq_mdp_info <= stamofu_iq_enq_mdp_info;
			last_stamofu_iq_enq_mem_aq <= stamofu_iq_enq_mem_aq;
			last_stamofu_iq_enq_io_aq <= stamofu_iq_enq_io_aq;
			last_stamofu_iq_enq_A_PR <= stamofu_iq_enq_A_PR;
			last_stamofu_iq_enq_A_ready <= stamofu_iq_enq_A_ready;
			last_stamofu_iq_enq_A_is_zero <= stamofu_iq_enq_A_is_zero;
			last_stamofu_iq_enq_B_PR <= stamofu_iq_enq_B_PR;
			last_stamofu_iq_enq_B_ready <= stamofu_iq_enq_B_ready;
			last_stamofu_iq_enq_B_is_zero <= stamofu_iq_enq_B_is_zero;
			last_stamofu_iq_enq_ROB_index <= stamofu_iq_enq_ROB_index;
			last_stamofu_iq_enq_cq_index <= stamofu_iq_enq_cq_index;

		    // issue queue enqueue feedback
			stamofu_iq_enq_ready <= next_stamofu_iq_enq_ready;

		    // op enqueue to acquire queue
			last_stamofu_aq_enq_valid <= stamofu_aq_enq_valid;
			last_stamofu_aq_enq_mem_aq <= stamofu_aq_enq_mem_aq;
			last_stamofu_aq_enq_io_aq <= stamofu_aq_enq_io_aq;
			last_stamofu_aq_enq_ROB_index <= stamofu_aq_enq_ROB_index;

		    // acquire queue enqueue feedback
			stamofu_aq_enq_ready <= next_stamofu_aq_enq_ready;

		    // ROB kill
			rob_kill_valid <= next_rob_kill_valid;
			rob_kill_abs_head_index <= next_rob_kill_abs_head_index;
			rob_kill_rel_kill_younger_index <= next_rob_kill_rel_kill_younger_index;
        end
    end

endmodule