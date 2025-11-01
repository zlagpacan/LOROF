/*
    Filename: stamofu_mq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_mq module. 
    Spec: LOROF/spec/design/stamofu_mq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_mq_wrapper #(
	parameter STAMOFU_MQ_ENTRIES = 4,
	parameter LOG_STAMOFU_MQ_ENTRIES = $clog2(STAMOFU_MQ_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to misaligned queue
	input logic next_stamofu_mq_enq_valid,

    // misaligned queue enqueue feedback
	output logic last_stamofu_mq_enq_ready,
	output logic [LOG_STAMOFU_MQ_ENTRIES-1:0] last_stamofu_mq_enq_index,

    // misaligned queue info ret
	input logic next_stamofu_mq_info_ret_bank0_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank0_cq_index,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank0_mq_index,
	input logic next_stamofu_mq_info_ret_bank0_dtlb_hit,
	input logic next_stamofu_mq_info_ret_bank0_page_fault,
	input logic next_stamofu_mq_info_ret_bank0_access_fault,
	input logic next_stamofu_mq_info_ret_bank0_is_mem,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_mq_info_ret_bank0_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_mq_info_ret_bank0_ROB_index,
	input logic [PA_WIDTH-2-1:0] next_stamofu_mq_info_ret_bank0_PA_word,
	input logic [3:0] next_stamofu_mq_info_ret_bank0_byte_mask,
	input logic [31:0] next_stamofu_mq_info_ret_bank0_data,

	input logic next_stamofu_mq_info_ret_bank1_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank1_cq_index,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank1_mq_index,
	input logic next_stamofu_mq_info_ret_bank1_dtlb_hit,
	input logic next_stamofu_mq_info_ret_bank1_page_fault,
	input logic next_stamofu_mq_info_ret_bank1_access_fault,
	input logic next_stamofu_mq_info_ret_bank1_is_mem,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_mq_info_ret_bank1_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_mq_info_ret_bank1_ROB_index,
	input logic [PA_WIDTH-2-1:0] next_stamofu_mq_info_ret_bank1_PA_word,
	input logic [3:0] next_stamofu_mq_info_ret_bank1_byte_mask,
	input logic [31:0] next_stamofu_mq_info_ret_bank1_data,

    // dtlb miss resp
	input logic next_dtlb_miss_resp_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_dtlb_miss_resp_cq_index,
	input logic next_dtlb_miss_resp_is_mq,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_dtlb_miss_resp_mq_index,
	input logic [PPN_WIDTH-1:0] next_dtlb_miss_resp_PPN,
	input logic next_dtlb_miss_resp_is_mem,
	input logic next_dtlb_miss_resp_page_fault,
	input logic next_dtlb_miss_resp_access_fault,

    // ldu CAM launch from stamofu_mq
	output logic last_stamofu_mq_ldu_CAM_launch_valid,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_mq_ldu_CAM_launch_cq_index,
	output logic [LOG_STAMOFU_MQ_ENTRIES-1:0] last_stamofu_mq_ldu_CAM_launch_mq_index,
	output logic [PA_WIDTH-2-1:0] last_stamofu_mq_ldu_CAM_launch_PA_word,
	output logic [3:0] last_stamofu_mq_ldu_CAM_launch_byte_mask,
	output logic [31:0] last_stamofu_mq_ldu_CAM_launch_write_data,
	output logic [MDPT_INFO_WIDTH-1:0] last_stamofu_mq_ldu_CAM_launch_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_mq_ldu_CAM_launch_ROB_index,

    // ldu CAM return
	input logic next_ldu_CAM_return_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_ldu_CAM_return_cq_index,
	input logic next_ldu_CAM_return_is_mq,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_ldu_CAM_return_mq_index,
	input logic next_ldu_CAM_return_forward,

    // stamofu CAM launch
	input logic next_stamofu_CAM_launch_bank0_valid,
	input logic [PA_WIDTH-2-1:0] next_stamofu_CAM_launch_bank0_PA_word,
	input logic [3:0] next_stamofu_CAM_launch_bank0_byte_mask,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_CAM_launch_bank0_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_CAM_launch_bank0_mdp_info,

	input logic next_stamofu_CAM_launch_bank1_valid,
	input logic [PA_WIDTH-2-1:0] next_stamofu_CAM_launch_bank1_PA_word,
	input logic [3:0] next_stamofu_CAM_launch_bank1_byte_mask,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_CAM_launch_bank1_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_CAM_launch_bank1_mdp_info,

    // stamofu_mq CAM stage 2 info
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_mq_CAM_return_bank0_cq_index,
	output logic last_stamofu_mq_CAM_return_bank0_stall,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_mq_CAM_return_bank0_stall_count,
	output logic [3:0] last_stamofu_mq_CAM_return_bank0_forward,
	output logic last_stamofu_mq_CAM_return_bank0_nasty_forward,
	output logic last_stamofu_mq_CAM_return_bank0_forward_ROB_index,
	output logic [31:0] last_stamofu_mq_CAM_return_bank0_forward_data,

	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_mq_CAM_return_bank1_cq_index,
	output logic last_stamofu_mq_CAM_return_bank1_stall,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_mq_CAM_return_bank1_stall_count,
	output logic [3:0] last_stamofu_mq_CAM_return_bank1_forward,
	output logic last_stamofu_mq_CAM_return_bank1_nasty_forward,
	output logic last_stamofu_mq_CAM_return_bank1_forward_ROB_index,
	output logic [31:0] last_stamofu_mq_CAM_return_bank1_forward_data,

    // misaligned queue info grab
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_stamofu_mq_info_grab_mq_index,
	input logic next_stamofu_mq_info_grab_clear_entry,
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
	output logic last_stamofu_mq_info_grab_is_mem,
	output logic [PA_WIDTH-2-1:0] last_stamofu_mq_info_grab_PA_word,
	output logic [3:0] last_stamofu_mq_info_grab_byte_mask,
	output logic [31:0] last_stamofu_mq_info_grab_data,

    // stamofu mq complete notif
	output logic last_stamofu_mq_complete_valid,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_mq_complete_cq_index,

    // ROB kill
        // this doesn't affect behavior (for now), but track anyway
	input logic next_rob_kill_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_abs_head_index,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_rel_kill_younger_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op enqueue to misaligned queue
	logic stamofu_mq_enq_valid;

    // misaligned queue enqueue feedback
	logic stamofu_mq_enq_ready;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_enq_index;

    // misaligned queue info ret
	logic stamofu_mq_info_ret_bank0_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_info_ret_bank0_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_ret_bank0_mq_index;
	logic stamofu_mq_info_ret_bank0_dtlb_hit;
	logic stamofu_mq_info_ret_bank0_page_fault;
	logic stamofu_mq_info_ret_bank0_access_fault;
	logic stamofu_mq_info_ret_bank0_is_mem;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_mq_info_ret_bank0_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_mq_info_ret_bank0_ROB_index;
	logic [PA_WIDTH-2-1:0] stamofu_mq_info_ret_bank0_PA_word;
	logic [3:0] stamofu_mq_info_ret_bank0_byte_mask;
	logic [31:0] stamofu_mq_info_ret_bank0_data;

	logic stamofu_mq_info_ret_bank1_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_info_ret_bank1_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_ret_bank1_mq_index;
	logic stamofu_mq_info_ret_bank1_dtlb_hit;
	logic stamofu_mq_info_ret_bank1_page_fault;
	logic stamofu_mq_info_ret_bank1_access_fault;
	logic stamofu_mq_info_ret_bank1_is_mem;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_mq_info_ret_bank1_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_mq_info_ret_bank1_ROB_index;
	logic [PA_WIDTH-2-1:0] stamofu_mq_info_ret_bank1_PA_word;
	logic [3:0] stamofu_mq_info_ret_bank1_byte_mask;
	logic [31:0] stamofu_mq_info_ret_bank1_data;

    // dtlb miss resp
	logic dtlb_miss_resp_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] dtlb_miss_resp_cq_index;
	logic dtlb_miss_resp_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] dtlb_miss_resp_mq_index;
	logic [PPN_WIDTH-1:0] dtlb_miss_resp_PPN;
	logic dtlb_miss_resp_is_mem;
	logic dtlb_miss_resp_page_fault;
	logic dtlb_miss_resp_access_fault;

    // ldu CAM launch from stamofu_mq
	logic stamofu_mq_ldu_CAM_launch_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_ldu_CAM_launch_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_ldu_CAM_launch_mq_index;
	logic [PA_WIDTH-2-1:0] stamofu_mq_ldu_CAM_launch_PA_word;
	logic [3:0] stamofu_mq_ldu_CAM_launch_byte_mask;
	logic [31:0] stamofu_mq_ldu_CAM_launch_write_data;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_mq_ldu_CAM_launch_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_mq_ldu_CAM_launch_ROB_index;

    // ldu CAM return
	logic ldu_CAM_return_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_return_cq_index;
	logic ldu_CAM_return_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] ldu_CAM_return_mq_index;
	logic ldu_CAM_return_forward;

    // stamofu CAM launch
	logic stamofu_CAM_launch_bank0_valid;
	logic [PA_WIDTH-2-1:0] stamofu_CAM_launch_bank0_PA_word;
	logic [3:0] stamofu_CAM_launch_bank0_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_CAM_launch_bank0_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_CAM_launch_bank0_mdp_info;

	logic stamofu_CAM_launch_bank1_valid;
	logic [PA_WIDTH-2-1:0] stamofu_CAM_launch_bank1_PA_word;
	logic [3:0] stamofu_CAM_launch_bank1_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_CAM_launch_bank1_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_CAM_launch_bank1_mdp_info;

    // stamofu_mq CAM stage 2 info
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_CAM_return_bank0_cq_index;
	logic stamofu_mq_CAM_return_bank0_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_CAM_return_bank0_stall_count;
	logic [3:0] stamofu_mq_CAM_return_bank0_forward;
	logic stamofu_mq_CAM_return_bank0_nasty_forward;
	logic stamofu_mq_CAM_return_bank0_forward_ROB_index;
	logic [31:0] stamofu_mq_CAM_return_bank0_forward_data;

	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_CAM_return_bank1_cq_index;
	logic stamofu_mq_CAM_return_bank1_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_CAM_return_bank1_stall_count;
	logic [3:0] stamofu_mq_CAM_return_bank1_forward;
	logic stamofu_mq_CAM_return_bank1_nasty_forward;
	logic stamofu_mq_CAM_return_bank1_forward_ROB_index;
	logic [31:0] stamofu_mq_CAM_return_bank1_forward_data;

    // misaligned queue info grab
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_grab_mq_index;
	logic stamofu_mq_info_grab_clear_entry;
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
	logic stamofu_mq_info_grab_is_mem;
	logic [PA_WIDTH-2-1:0] stamofu_mq_info_grab_PA_word;
	logic [3:0] stamofu_mq_info_grab_byte_mask;
	logic [31:0] stamofu_mq_info_grab_data;

    // stamofu mq complete notif
	logic stamofu_mq_complete_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_complete_cq_index;

    // ROB kill
        // this doesn't affect behavior (for now), but track anyway
	logic rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	stamofu_mq #(
		.STAMOFU_MQ_ENTRIES(STAMOFU_MQ_ENTRIES),
		.LOG_STAMOFU_MQ_ENTRIES(LOG_STAMOFU_MQ_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to misaligned queue
			stamofu_mq_enq_valid <= '0;

		    // misaligned queue enqueue feedback
			last_stamofu_mq_enq_ready <= '0;
			last_stamofu_mq_enq_index <= '0;

		    // misaligned queue info ret
			stamofu_mq_info_ret_bank0_valid <= '0;
			stamofu_mq_info_ret_bank0_cq_index <= '0;
			stamofu_mq_info_ret_bank0_mq_index <= '0;
			stamofu_mq_info_ret_bank0_dtlb_hit <= '0;
			stamofu_mq_info_ret_bank0_page_fault <= '0;
			stamofu_mq_info_ret_bank0_access_fault <= '0;
			stamofu_mq_info_ret_bank0_is_mem <= '0;
			stamofu_mq_info_ret_bank0_mdp_info <= '0;
			stamofu_mq_info_ret_bank0_ROB_index <= '0;
			stamofu_mq_info_ret_bank0_PA_word <= '0;
			stamofu_mq_info_ret_bank0_byte_mask <= '0;
			stamofu_mq_info_ret_bank0_data <= '0;

			stamofu_mq_info_ret_bank1_valid <= '0;
			stamofu_mq_info_ret_bank1_cq_index <= '0;
			stamofu_mq_info_ret_bank1_mq_index <= '0;
			stamofu_mq_info_ret_bank1_dtlb_hit <= '0;
			stamofu_mq_info_ret_bank1_page_fault <= '0;
			stamofu_mq_info_ret_bank1_access_fault <= '0;
			stamofu_mq_info_ret_bank1_is_mem <= '0;
			stamofu_mq_info_ret_bank1_mdp_info <= '0;
			stamofu_mq_info_ret_bank1_ROB_index <= '0;
			stamofu_mq_info_ret_bank1_PA_word <= '0;
			stamofu_mq_info_ret_bank1_byte_mask <= '0;
			stamofu_mq_info_ret_bank1_data <= '0;

		    // dtlb miss resp
			dtlb_miss_resp_valid <= '0;
			dtlb_miss_resp_cq_index <= '0;
			dtlb_miss_resp_is_mq <= '0;
			dtlb_miss_resp_mq_index <= '0;
			dtlb_miss_resp_PPN <= '0;
			dtlb_miss_resp_is_mem <= '0;
			dtlb_miss_resp_page_fault <= '0;
			dtlb_miss_resp_access_fault <= '0;

		    // ldu CAM launch from stamofu_mq
			last_stamofu_mq_ldu_CAM_launch_valid <= '0;
			last_stamofu_mq_ldu_CAM_launch_cq_index <= '0;
			last_stamofu_mq_ldu_CAM_launch_mq_index <= '0;
			last_stamofu_mq_ldu_CAM_launch_PA_word <= '0;
			last_stamofu_mq_ldu_CAM_launch_byte_mask <= '0;
			last_stamofu_mq_ldu_CAM_launch_write_data <= '0;
			last_stamofu_mq_ldu_CAM_launch_mdp_info <= '0;
			last_stamofu_mq_ldu_CAM_launch_ROB_index <= '0;

		    // ldu CAM return
			ldu_CAM_return_valid <= '0;
			ldu_CAM_return_cq_index <= '0;
			ldu_CAM_return_is_mq <= '0;
			ldu_CAM_return_mq_index <= '0;
			ldu_CAM_return_forward <= '0;

		    // stamofu CAM launch
			stamofu_CAM_launch_bank0_valid <= '0;
			stamofu_CAM_launch_bank0_PA_word <= '0;
			stamofu_CAM_launch_bank0_byte_mask <= '0;
			stamofu_CAM_launch_bank0_ROB_index <= '0;
			stamofu_CAM_launch_bank0_mdp_info <= '0;

			stamofu_CAM_launch_bank1_valid <= '0;
			stamofu_CAM_launch_bank1_PA_word <= '0;
			stamofu_CAM_launch_bank1_byte_mask <= '0;
			stamofu_CAM_launch_bank1_ROB_index <= '0;
			stamofu_CAM_launch_bank1_mdp_info <= '0;

		    // stamofu_mq CAM stage 2 info
			last_stamofu_mq_CAM_return_bank0_cq_index <= '0;
			last_stamofu_mq_CAM_return_bank0_stall <= '0;
			last_stamofu_mq_CAM_return_bank0_stall_count <= '0;
			last_stamofu_mq_CAM_return_bank0_forward <= '0;
			last_stamofu_mq_CAM_return_bank0_nasty_forward <= '0;
			last_stamofu_mq_CAM_return_bank0_forward_ROB_index <= '0;
			last_stamofu_mq_CAM_return_bank0_forward_data <= '0;

			last_stamofu_mq_CAM_return_bank1_cq_index <= '0;
			last_stamofu_mq_CAM_return_bank1_stall <= '0;
			last_stamofu_mq_CAM_return_bank1_stall_count <= '0;
			last_stamofu_mq_CAM_return_bank1_forward <= '0;
			last_stamofu_mq_CAM_return_bank1_nasty_forward <= '0;
			last_stamofu_mq_CAM_return_bank1_forward_ROB_index <= '0;
			last_stamofu_mq_CAM_return_bank1_forward_data <= '0;

		    // misaligned queue info grab
			stamofu_mq_info_grab_mq_index <= '0;
			stamofu_mq_info_grab_clear_entry <= '0;
		        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
			last_stamofu_mq_info_grab_is_mem <= '0;
			last_stamofu_mq_info_grab_PA_word <= '0;
			last_stamofu_mq_info_grab_byte_mask <= '0;
			last_stamofu_mq_info_grab_data <= '0;

		    // stamofu mq complete notif
			last_stamofu_mq_complete_valid <= '0;
			last_stamofu_mq_complete_cq_index <= '0;

		    // ROB kill
		        // this doesn't affect behavior (for now), but track anyway
			rob_kill_valid <= '0;
			rob_kill_abs_head_index <= '0;
			rob_kill_rel_kill_younger_index <= '0;
        end
        else begin

		    // op enqueue to misaligned queue
			stamofu_mq_enq_valid <= next_stamofu_mq_enq_valid;

		    // misaligned queue enqueue feedback
			last_stamofu_mq_enq_ready <= stamofu_mq_enq_ready;
			last_stamofu_mq_enq_index <= stamofu_mq_enq_index;

		    // misaligned queue info ret
			stamofu_mq_info_ret_bank0_valid <= next_stamofu_mq_info_ret_bank0_valid;
			stamofu_mq_info_ret_bank0_cq_index <= next_stamofu_mq_info_ret_bank0_cq_index;
			stamofu_mq_info_ret_bank0_mq_index <= next_stamofu_mq_info_ret_bank0_mq_index;
			stamofu_mq_info_ret_bank0_dtlb_hit <= next_stamofu_mq_info_ret_bank0_dtlb_hit;
			stamofu_mq_info_ret_bank0_page_fault <= next_stamofu_mq_info_ret_bank0_page_fault;
			stamofu_mq_info_ret_bank0_access_fault <= next_stamofu_mq_info_ret_bank0_access_fault;
			stamofu_mq_info_ret_bank0_is_mem <= next_stamofu_mq_info_ret_bank0_is_mem;
			stamofu_mq_info_ret_bank0_mdp_info <= next_stamofu_mq_info_ret_bank0_mdp_info;
			stamofu_mq_info_ret_bank0_ROB_index <= next_stamofu_mq_info_ret_bank0_ROB_index;
			stamofu_mq_info_ret_bank0_PA_word <= next_stamofu_mq_info_ret_bank0_PA_word;
			stamofu_mq_info_ret_bank0_byte_mask <= next_stamofu_mq_info_ret_bank0_byte_mask;
			stamofu_mq_info_ret_bank0_data <= next_stamofu_mq_info_ret_bank0_data;

			stamofu_mq_info_ret_bank1_valid <= next_stamofu_mq_info_ret_bank1_valid;
			stamofu_mq_info_ret_bank1_cq_index <= next_stamofu_mq_info_ret_bank1_cq_index;
			stamofu_mq_info_ret_bank1_mq_index <= next_stamofu_mq_info_ret_bank1_mq_index;
			stamofu_mq_info_ret_bank1_dtlb_hit <= next_stamofu_mq_info_ret_bank1_dtlb_hit;
			stamofu_mq_info_ret_bank1_page_fault <= next_stamofu_mq_info_ret_bank1_page_fault;
			stamofu_mq_info_ret_bank1_access_fault <= next_stamofu_mq_info_ret_bank1_access_fault;
			stamofu_mq_info_ret_bank1_is_mem <= next_stamofu_mq_info_ret_bank1_is_mem;
			stamofu_mq_info_ret_bank1_mdp_info <= next_stamofu_mq_info_ret_bank1_mdp_info;
			stamofu_mq_info_ret_bank1_ROB_index <= next_stamofu_mq_info_ret_bank1_ROB_index;
			stamofu_mq_info_ret_bank1_PA_word <= next_stamofu_mq_info_ret_bank1_PA_word;
			stamofu_mq_info_ret_bank1_byte_mask <= next_stamofu_mq_info_ret_bank1_byte_mask;
			stamofu_mq_info_ret_bank1_data <= next_stamofu_mq_info_ret_bank1_data;

		    // dtlb miss resp
			dtlb_miss_resp_valid <= next_dtlb_miss_resp_valid;
			dtlb_miss_resp_cq_index <= next_dtlb_miss_resp_cq_index;
			dtlb_miss_resp_is_mq <= next_dtlb_miss_resp_is_mq;
			dtlb_miss_resp_mq_index <= next_dtlb_miss_resp_mq_index;
			dtlb_miss_resp_PPN <= next_dtlb_miss_resp_PPN;
			dtlb_miss_resp_is_mem <= next_dtlb_miss_resp_is_mem;
			dtlb_miss_resp_page_fault <= next_dtlb_miss_resp_page_fault;
			dtlb_miss_resp_access_fault <= next_dtlb_miss_resp_access_fault;

		    // ldu CAM launch from stamofu_mq
			last_stamofu_mq_ldu_CAM_launch_valid <= stamofu_mq_ldu_CAM_launch_valid;
			last_stamofu_mq_ldu_CAM_launch_cq_index <= stamofu_mq_ldu_CAM_launch_cq_index;
			last_stamofu_mq_ldu_CAM_launch_mq_index <= stamofu_mq_ldu_CAM_launch_mq_index;
			last_stamofu_mq_ldu_CAM_launch_PA_word <= stamofu_mq_ldu_CAM_launch_PA_word;
			last_stamofu_mq_ldu_CAM_launch_byte_mask <= stamofu_mq_ldu_CAM_launch_byte_mask;
			last_stamofu_mq_ldu_CAM_launch_write_data <= stamofu_mq_ldu_CAM_launch_write_data;
			last_stamofu_mq_ldu_CAM_launch_mdp_info <= stamofu_mq_ldu_CAM_launch_mdp_info;
			last_stamofu_mq_ldu_CAM_launch_ROB_index <= stamofu_mq_ldu_CAM_launch_ROB_index;

		    // ldu CAM return
			ldu_CAM_return_valid <= next_ldu_CAM_return_valid;
			ldu_CAM_return_cq_index <= next_ldu_CAM_return_cq_index;
			ldu_CAM_return_is_mq <= next_ldu_CAM_return_is_mq;
			ldu_CAM_return_mq_index <= next_ldu_CAM_return_mq_index;
			ldu_CAM_return_forward <= next_ldu_CAM_return_forward;

		    // stamofu CAM launch
			stamofu_CAM_launch_bank0_valid <= next_stamofu_CAM_launch_bank0_valid;
			stamofu_CAM_launch_bank0_PA_word <= next_stamofu_CAM_launch_bank0_PA_word;
			stamofu_CAM_launch_bank0_byte_mask <= next_stamofu_CAM_launch_bank0_byte_mask;
			stamofu_CAM_launch_bank0_ROB_index <= next_stamofu_CAM_launch_bank0_ROB_index;
			stamofu_CAM_launch_bank0_mdp_info <= next_stamofu_CAM_launch_bank0_mdp_info;

			stamofu_CAM_launch_bank1_valid <= next_stamofu_CAM_launch_bank1_valid;
			stamofu_CAM_launch_bank1_PA_word <= next_stamofu_CAM_launch_bank1_PA_word;
			stamofu_CAM_launch_bank1_byte_mask <= next_stamofu_CAM_launch_bank1_byte_mask;
			stamofu_CAM_launch_bank1_ROB_index <= next_stamofu_CAM_launch_bank1_ROB_index;
			stamofu_CAM_launch_bank1_mdp_info <= next_stamofu_CAM_launch_bank1_mdp_info;

		    // stamofu_mq CAM stage 2 info
			last_stamofu_mq_CAM_return_bank0_cq_index <= stamofu_mq_CAM_return_bank0_cq_index;
			last_stamofu_mq_CAM_return_bank0_stall <= stamofu_mq_CAM_return_bank0_stall;
			last_stamofu_mq_CAM_return_bank0_stall_count <= stamofu_mq_CAM_return_bank0_stall_count;
			last_stamofu_mq_CAM_return_bank0_forward <= stamofu_mq_CAM_return_bank0_forward;
			last_stamofu_mq_CAM_return_bank0_nasty_forward <= stamofu_mq_CAM_return_bank0_nasty_forward;
			last_stamofu_mq_CAM_return_bank0_forward_ROB_index <= stamofu_mq_CAM_return_bank0_forward_ROB_index;
			last_stamofu_mq_CAM_return_bank0_forward_data <= stamofu_mq_CAM_return_bank0_forward_data;

			last_stamofu_mq_CAM_return_bank1_cq_index <= stamofu_mq_CAM_return_bank1_cq_index;
			last_stamofu_mq_CAM_return_bank1_stall <= stamofu_mq_CAM_return_bank1_stall;
			last_stamofu_mq_CAM_return_bank1_stall_count <= stamofu_mq_CAM_return_bank1_stall_count;
			last_stamofu_mq_CAM_return_bank1_forward <= stamofu_mq_CAM_return_bank1_forward;
			last_stamofu_mq_CAM_return_bank1_nasty_forward <= stamofu_mq_CAM_return_bank1_nasty_forward;
			last_stamofu_mq_CAM_return_bank1_forward_ROB_index <= stamofu_mq_CAM_return_bank1_forward_ROB_index;
			last_stamofu_mq_CAM_return_bank1_forward_data <= stamofu_mq_CAM_return_bank1_forward_data;

		    // misaligned queue info grab
			stamofu_mq_info_grab_mq_index <= next_stamofu_mq_info_grab_mq_index;
			stamofu_mq_info_grab_clear_entry <= next_stamofu_mq_info_grab_clear_entry;
		        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
			last_stamofu_mq_info_grab_is_mem <= stamofu_mq_info_grab_is_mem;
			last_stamofu_mq_info_grab_PA_word <= stamofu_mq_info_grab_PA_word;
			last_stamofu_mq_info_grab_byte_mask <= stamofu_mq_info_grab_byte_mask;
			last_stamofu_mq_info_grab_data <= stamofu_mq_info_grab_data;

		    // stamofu mq complete notif
			last_stamofu_mq_complete_valid <= stamofu_mq_complete_valid;
			last_stamofu_mq_complete_cq_index <= stamofu_mq_complete_cq_index;

		    // ROB kill
		        // this doesn't affect behavior (for now), but track anyway
			rob_kill_valid <= next_rob_kill_valid;
			rob_kill_abs_head_index <= next_rob_kill_abs_head_index;
			rob_kill_rel_kill_younger_index <= next_rob_kill_rel_kill_younger_index;
        end
    end

endmodule