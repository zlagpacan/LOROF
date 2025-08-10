/*
    Filename: ldu_cq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ldu_cq module. 
    Spec: LOROF/spec/design/ldu_cq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter LDU_CQ_ENTRIES = core_types_pkg::LDU_CQ_ENTRIES;
parameter LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES);

module ldu_cq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to central queue
	input logic next_ldu_cq_enq_valid,
	input logic next_ldu_cq_enq_killed,
	input logic [3:0] next_ldu_cq_enq_op,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_cq_enq_mdp_info,
	input logic [LOG_PR_COUNT-1:0] next_ldu_cq_enq_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_cq_enq_ROB_index,

    // central queue enqueue feedback
	output logic last_ldu_cq_enq_ready,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_ldu_cq_enq_index,

    // second try
	output logic last_second_try_bank0_valid,
	output logic last_second_try_bank1_valid,

	output logic last_second_try_do_mispred,
	output logic last_second_try_is_mq,
	output logic last_second_try_misaligned,
	output logic last_second_try_page_fault,
	output logic last_second_try_access_fault,
	output logic last_second_try_is_mem,
	output logic [PPN_WIDTH-1:0] last_second_try_PPN,
	output logic [PO_WIDTH-3:0] last_second_try_PO_word,
	output logic [3:0] last_second_try_byte_mask,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_second_try_cq_index,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_second_try_mq_index,

    // second try feedback
	input logic next_second_try_bank0_ack,
	input logic next_second_try_bank1_ack,

    // data try
	output logic last_data_try_bank0_valid,
	output logic last_data_try_bank1_valid,

	output logic last_data_try_do_mispred,
	output logic [31:0] last_data_try_data,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_data_try_cq_index,

    // data try feedback
	input logic next_data_try_bank0_ack,
	input logic next_data_try_bank1_ack,

    // misaligned queue data try req
	input logic next_ldu_mq_data_try_req_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_mq_data_try_cq_index,

    // misaligned queue info grab
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_ldu_mq_info_grab_mq_index,
	output logic last_ldu_mq_info_grab_data_try_ack,
	input logic next_ldu_mq_info_grab_data_try_req,
	input logic [31:0] next_ldu_mq_info_grab_data,

    // central queue info grab
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_cq_info_grab_bank0_cq_index,
	output logic [3:0] last_ldu_cq_info_grab_bank0_op,
	output logic [MDPT_INFO_WIDTH-1:0] last_ldu_cq_info_grab_bank0_mdp_info,
	output logic [LOG_PR_COUNT-1:0] last_ldu_cq_info_grab_bank0_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_ldu_cq_info_grab_bank0_ROB_index,

	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_cq_info_grab_bank1_cq_index,
	output logic [3:0] last_ldu_cq_info_grab_bank1_op,
	output logic [MDPT_INFO_WIDTH-1:0] last_ldu_cq_info_grab_bank1_mdp_info,
	output logic [LOG_PR_COUNT-1:0] last_ldu_cq_info_grab_bank1_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_ldu_cq_info_grab_bank1_ROB_index,

    // central queue info ret
	input logic next_ldu_cq_info_ret_bank0_valid,
	input logic next_ldu_cq_info_ret_bank0_WB_sent,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_cq_info_ret_bank0_cq_index,
	input logic next_ldu_cq_info_ret_bank0_misaligned,
	input logic next_ldu_cq_info_ret_bank0_dtlb_hit,
	input logic next_ldu_cq_info_ret_bank0_page_fault,
	input logic next_ldu_cq_info_ret_bank0_access_fault,
	input logic next_ldu_cq_info_ret_bank0_dcache_hit,
	input logic next_ldu_cq_info_ret_bank0_is_mem,
	input logic next_ldu_cq_info_ret_bank0_aq_blocking,
	input logic [PA_WIDTH-2-1:0] next_ldu_cq_info_ret_bank0_PA_word,
	input logic [3:0] next_ldu_cq_info_ret_bank0_byte_mask,
	input logic [31:0] next_ldu_cq_info_ret_bank0_data,

	input logic next_ldu_cq_info_ret_bank1_valid,
	input logic next_ldu_cq_info_ret_bank1_WB_sent,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_cq_info_ret_bank1_cq_index,
	input logic next_ldu_cq_info_ret_bank1_misaligned,
	input logic next_ldu_cq_info_ret_bank1_dtlb_hit,
	input logic next_ldu_cq_info_ret_bank1_page_fault,
	input logic next_ldu_cq_info_ret_bank1_access_fault,
	input logic next_ldu_cq_info_ret_bank1_dcache_hit,
	input logic next_ldu_cq_info_ret_bank1_is_mem,
	input logic next_ldu_cq_info_ret_bank1_aq_blocking,
	input logic [PA_WIDTH-2-1:0] next_ldu_cq_info_ret_bank1_PA_word,
	input logic [3:0] next_ldu_cq_info_ret_bank1_byte_mask,
	input logic [31:0] next_ldu_cq_info_ret_bank1_data,

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
	input logic next_ldu_mq_info_ret_bank0_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_mq_info_ret_bank0_cq_index,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_ldu_mq_info_ret_bank0_mq_index,

	input logic next_ldu_mq_info_ret_bank1_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_ldu_mq_info_ret_bank1_cq_index,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_ldu_mq_info_ret_bank1_mq_index,

    // dtlb miss resp
	input logic next_dtlb_miss_resp_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_dtlb_miss_resp_cq_index,
	input logic next_dtlb_miss_resp_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_dtlb_miss_resp_mq_index,
	input logic [PPN_WIDTH-1:0] next_dtlb_miss_resp_PPN,
	input logic next_dtlb_miss_resp_is_mem,
	input logic next_dtlb_miss_resp_page_fault,
	input logic next_dtlb_miss_resp_access_fault,

    // dcache miss resp
	input logic next_dcache_miss_resp_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_dcache_miss_resp_cq_index,
	input logic next_dcache_miss_resp_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_dcache_miss_resp_mq_index,
	input logic [31:0] next_dcache_miss_resp_data,

    // stamofu CAM return
	input logic next_stamofu_CAM_return_bank0_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_stamofu_CAM_return_bank0_cq_index,
	input logic next_stamofu_CAM_return_bank0_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_stamofu_CAM_return_bank0_mq_index,
	input logic next_stamofu_CAM_return_bank0_stall,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_CAM_return_bank0_stall_count,
	input logic [3:0] next_stamofu_CAM_return_bank0_forward,
	input logic next_stamofu_CAM_return_bank0_nasty_forward,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_CAM_return_bank0_forward_ROB_index,
	input logic [31:0] next_stamofu_CAM_return_bank0_forward_data,

	input logic next_stamofu_CAM_return_bank1_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_stamofu_CAM_return_bank1_cq_index,
	input logic next_stamofu_CAM_return_bank1_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_stamofu_CAM_return_bank1_mq_index,
	input logic next_stamofu_CAM_return_bank1_stall,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_CAM_return_bank1_stall_count,
	input logic [3:0] next_stamofu_CAM_return_bank1_forward,
	input logic next_stamofu_CAM_return_bank1_nasty_forward,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_CAM_return_bank1_forward_ROB_index,
	input logic [31:0] next_stamofu_CAM_return_bank1_forward_data,

    // ldu CAM launch
	input logic next_ldu_CAM_launch_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_ldu_CAM_launch_cq_index,
	input logic next_ldu_CAM_launch_is_mq,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_ldu_CAM_launch_mq_index,
	input logic next_ldu_CAM_launch_is_amo,
	input logic [PA_WIDTH-2-1:0] next_ldu_CAM_launch_PA_word,
	input logic [3:0] next_ldu_CAM_launch_byte_mask,
	input logic [31:0] next_ldu_CAM_launch_write_data,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_CAM_launch_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_CAM_launch_ROB_index,

    // ldu CAM return
	output logic last_ldu_CAM_return_valid,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_ldu_CAM_return_cq_index,
	output logic last_ldu_CAM_return_is_mq,
	output logic [LOG_STAMOFU_MQ_ENTRIES-1:0] last_ldu_CAM_return_mq_index,
	output logic last_ldu_CAM_return_forward,

    // ldu_mq commit
	output logic last_ldu_cq_commit_mq_valid,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_ldu_cq_commit_mq_index,
	input logic next_ldu_cq_commit_mq_has_forward,

    // store set CAM update
        // implied dep
	output logic last_ssu_CAM_update_valid,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_CAM_update_ld_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_CAM_update_ld_ROB_index,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_CAM_update_stamo_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_CAM_update_stamo_ROB_index,

    // store set commit update
        // implied no dep
	output logic last_ssu_commit_update_valid,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_commit_update_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_commit_update_ROB_index,

    // acquire advertisement
	input logic next_stamofu_aq_mem_aq_active,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_aq_mem_aq_oldest_abs_ROB_index,
	input logic next_stamofu_aq_io_aq_active,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_aq_io_aq_oldest_abs_ROB_index,

    // oldest stamofu advertisement
	input logic next_stamofu_incomplete_active,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_oldest_incomplete_ROB_index,

    // ROB complete notif
	output logic last_ldu_complete_valid,
	output logic [LOG_ROB_ENTRIES-1:0] last_ldu_complete_ROB_index,

    // ROB commit
	input logic [LOG_ROB_ENTRIES-3:0] next_rob_commit_upper_index,
	input logic [3:0] next_rob_commit_lower_index_valid_mask,

    // ROB kill
	input logic next_rob_kill_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_abs_head_index,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_rel_kill_younger_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op enqueue to central queue
	logic ldu_cq_enq_valid;
	logic ldu_cq_enq_killed;
	logic [3:0] ldu_cq_enq_op;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_enq_mdp_info;
	logic [LOG_PR_COUNT-1:0] ldu_cq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_enq_ROB_index;

    // central queue enqueue feedback
	logic ldu_cq_enq_ready;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_enq_index;

    // second try
	logic second_try_bank0_valid;
	logic second_try_bank1_valid;

	logic second_try_do_mispred;
	logic second_try_is_mq;
	logic second_try_misaligned;
	logic second_try_page_fault;
	logic second_try_access_fault;
	logic second_try_is_mem;
	logic [PPN_WIDTH-1:0] second_try_PPN;
	logic [PO_WIDTH-3:0] second_try_PO_word;
	logic [3:0] second_try_byte_mask;
	logic [LOG_LDU_CQ_ENTRIES-1:0] second_try_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] second_try_mq_index;

    // second try feedback
	logic second_try_bank0_ack;
	logic second_try_bank1_ack;

    // data try
	logic data_try_bank0_valid;
	logic data_try_bank1_valid;

	logic data_try_do_mispred;
	logic [31:0] data_try_data;
	logic [LOG_LDU_CQ_ENTRIES-1:0] data_try_cq_index;

    // data try feedback
	logic data_try_bank0_ack;
	logic data_try_bank1_ack;

    // misaligned queue data try req
	logic ldu_mq_data_try_req_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_mq_data_try_cq_index;

    // misaligned queue info grab
	logic [LOG_LDU_MQ_ENTRIES-1:0] ldu_mq_info_grab_mq_index;
	logic ldu_mq_info_grab_data_try_ack;
	logic ldu_mq_info_grab_data_try_req;
	logic [31:0] ldu_mq_info_grab_data;

    // central queue info grab
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_info_grab_bank0_cq_index;
	logic [3:0] ldu_cq_info_grab_bank0_op;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_info_grab_bank0_mdp_info;
	logic [LOG_PR_COUNT-1:0] ldu_cq_info_grab_bank0_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_info_grab_bank0_ROB_index;

	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_info_grab_bank1_cq_index;
	logic [3:0] ldu_cq_info_grab_bank1_op;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_info_grab_bank1_mdp_info;
	logic [LOG_PR_COUNT-1:0] ldu_cq_info_grab_bank1_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_info_grab_bank1_ROB_index;

    // central queue info ret
	logic ldu_cq_info_ret_bank0_valid;
	logic ldu_cq_info_ret_bank0_WB_sent;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_info_ret_bank0_cq_index;
	logic ldu_cq_info_ret_bank0_misaligned;
	logic ldu_cq_info_ret_bank0_dtlb_hit;
	logic ldu_cq_info_ret_bank0_page_fault;
	logic ldu_cq_info_ret_bank0_access_fault;
	logic ldu_cq_info_ret_bank0_dcache_hit;
	logic ldu_cq_info_ret_bank0_is_mem;
	logic ldu_cq_info_ret_bank0_aq_blocking;
	logic [PA_WIDTH-2-1:0] ldu_cq_info_ret_bank0_PA_word;
	logic [3:0] ldu_cq_info_ret_bank0_byte_mask;
	logic [31:0] ldu_cq_info_ret_bank0_data;

	logic ldu_cq_info_ret_bank1_valid;
	logic ldu_cq_info_ret_bank1_WB_sent;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_info_ret_bank1_cq_index;
	logic ldu_cq_info_ret_bank1_misaligned;
	logic ldu_cq_info_ret_bank1_dtlb_hit;
	logic ldu_cq_info_ret_bank1_page_fault;
	logic ldu_cq_info_ret_bank1_access_fault;
	logic ldu_cq_info_ret_bank1_dcache_hit;
	logic ldu_cq_info_ret_bank1_is_mem;
	logic ldu_cq_info_ret_bank1_aq_blocking;
	logic [PA_WIDTH-2-1:0] ldu_cq_info_ret_bank1_PA_word;
	logic [3:0] ldu_cq_info_ret_bank1_byte_mask;
	logic [31:0] ldu_cq_info_ret_bank1_data;

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
	logic ldu_mq_info_ret_bank0_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_mq_info_ret_bank0_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] ldu_mq_info_ret_bank0_mq_index;

	logic ldu_mq_info_ret_bank1_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_mq_info_ret_bank1_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] ldu_mq_info_ret_bank1_mq_index;

    // dtlb miss resp
	logic dtlb_miss_resp_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dtlb_miss_resp_cq_index;
	logic dtlb_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dtlb_miss_resp_mq_index;
	logic [PPN_WIDTH-1:0] dtlb_miss_resp_PPN;
	logic dtlb_miss_resp_is_mem;
	logic dtlb_miss_resp_page_fault;
	logic dtlb_miss_resp_access_fault;

    // dcache miss resp
	logic dcache_miss_resp_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dcache_miss_resp_cq_index;
	logic dcache_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dcache_miss_resp_mq_index;
	logic [31:0] dcache_miss_resp_data;

    // stamofu CAM return
	logic stamofu_CAM_return_bank0_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] stamofu_CAM_return_bank0_cq_index;
	logic stamofu_CAM_return_bank0_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] stamofu_CAM_return_bank0_mq_index;
	logic stamofu_CAM_return_bank0_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_CAM_return_bank0_stall_count;
	logic [3:0] stamofu_CAM_return_bank0_forward;
	logic stamofu_CAM_return_bank0_nasty_forward;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_CAM_return_bank0_forward_ROB_index;
	logic [31:0] stamofu_CAM_return_bank0_forward_data;

	logic stamofu_CAM_return_bank1_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] stamofu_CAM_return_bank1_cq_index;
	logic stamofu_CAM_return_bank1_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] stamofu_CAM_return_bank1_mq_index;
	logic stamofu_CAM_return_bank1_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_CAM_return_bank1_stall_count;
	logic [3:0] stamofu_CAM_return_bank1_forward;
	logic stamofu_CAM_return_bank1_nasty_forward;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_CAM_return_bank1_forward_ROB_index;
	logic [31:0] stamofu_CAM_return_bank1_forward_data;

    // ldu CAM launch
	logic ldu_CAM_launch_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_launch_cq_index;
	logic ldu_CAM_launch_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] ldu_CAM_launch_mq_index;
	logic ldu_CAM_launch_is_amo;
	logic [PA_WIDTH-2-1:0] ldu_CAM_launch_PA_word;
	logic [3:0] ldu_CAM_launch_byte_mask;
	logic [31:0] ldu_CAM_launch_write_data;
	logic [MDPT_INFO_WIDTH-1:0] ldu_CAM_launch_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ldu_CAM_launch_ROB_index;

    // ldu CAM return
	logic ldu_CAM_return_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_return_cq_index;
	logic ldu_CAM_return_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] ldu_CAM_return_mq_index;
	logic ldu_CAM_return_forward;

    // ldu_mq commit
	logic ldu_cq_commit_mq_valid;
	logic [LOG_LDU_MQ_ENTRIES-1:0] ldu_cq_commit_mq_index;
	logic ldu_cq_commit_mq_has_forward;

    // store set CAM update
        // implied dep
	logic ssu_CAM_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] ssu_CAM_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_CAM_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] ssu_CAM_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_CAM_update_stamo_ROB_index;

    // store set commit update
        // implied no dep
	logic ssu_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] ssu_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_commit_update_ROB_index;

    // acquire advertisement
	logic stamofu_aq_mem_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_mem_aq_oldest_abs_ROB_index;
	logic stamofu_aq_io_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_io_aq_oldest_abs_ROB_index;

    // oldest stamofu advertisement
	logic stamofu_incomplete_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_oldest_incomplete_ROB_index;

    // ROB complete notif
	logic ldu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] ldu_complete_ROB_index;

    // ROB commit
	logic [LOG_ROB_ENTRIES-3:0] rob_commit_upper_index;
	logic [3:0] rob_commit_lower_index_valid_mask;

    // ROB kill
	logic rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ldu_cq #(
		.LDU_CQ_ENTRIES(LDU_CQ_ENTRIES),
		.LOG_LDU_CQ_ENTRIES(LOG_LDU_CQ_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to central queue
			ldu_cq_enq_valid <= '0;
			ldu_cq_enq_killed <= '0;
			ldu_cq_enq_op <= '0;
			ldu_cq_enq_mdp_info <= '0;
			ldu_cq_enq_dest_PR <= '0;
			ldu_cq_enq_ROB_index <= '0;

		    // central queue enqueue feedback
			last_ldu_cq_enq_ready <= '0;
			last_ldu_cq_enq_index <= '0;

		    // second try
			last_second_try_bank0_valid <= '0;
			last_second_try_bank1_valid <= '0;

			last_second_try_do_mispred <= '0;
			last_second_try_is_mq <= '0;
			last_second_try_misaligned <= '0;
			last_second_try_page_fault <= '0;
			last_second_try_access_fault <= '0;
			last_second_try_is_mem <= '0;
			last_second_try_PPN <= '0;
			last_second_try_PO_word <= '0;
			last_second_try_byte_mask <= '0;
			last_second_try_cq_index <= '0;
			last_second_try_mq_index <= '0;

		    // second try feedback
			second_try_bank0_ack <= '0;
			second_try_bank1_ack <= '0;

		    // data try
			last_data_try_bank0_valid <= '0;
			last_data_try_bank1_valid <= '0;

			last_data_try_do_mispred <= '0;
			last_data_try_data <= '0;
			last_data_try_cq_index <= '0;

		    // data try feedback
			data_try_bank0_ack <= '0;
			data_try_bank1_ack <= '0;

		    // misaligned queue data try req
			ldu_mq_data_try_req_valid <= '0;
			ldu_mq_data_try_cq_index <= '0;

		    // misaligned queue info grab
			last_ldu_mq_info_grab_mq_index <= '0;
			last_ldu_mq_info_grab_data_try_ack <= '0;
			ldu_mq_info_grab_data_try_req <= '0;
			ldu_mq_info_grab_data <= '0;

		    // central queue info grab
			ldu_cq_info_grab_bank0_cq_index <= '0;
			last_ldu_cq_info_grab_bank0_op <= '0;
			last_ldu_cq_info_grab_bank0_mdp_info <= '0;
			last_ldu_cq_info_grab_bank0_dest_PR <= '0;
			last_ldu_cq_info_grab_bank0_ROB_index <= '0;

			ldu_cq_info_grab_bank1_cq_index <= '0;
			last_ldu_cq_info_grab_bank1_op <= '0;
			last_ldu_cq_info_grab_bank1_mdp_info <= '0;
			last_ldu_cq_info_grab_bank1_dest_PR <= '0;
			last_ldu_cq_info_grab_bank1_ROB_index <= '0;

		    // central queue info ret
			ldu_cq_info_ret_bank0_valid <= '0;
			ldu_cq_info_ret_bank0_WB_sent <= '0;
			ldu_cq_info_ret_bank0_cq_index <= '0;
			ldu_cq_info_ret_bank0_misaligned <= '0;
			ldu_cq_info_ret_bank0_dtlb_hit <= '0;
			ldu_cq_info_ret_bank0_page_fault <= '0;
			ldu_cq_info_ret_bank0_access_fault <= '0;
			ldu_cq_info_ret_bank0_dcache_hit <= '0;
			ldu_cq_info_ret_bank0_is_mem <= '0;
			ldu_cq_info_ret_bank0_aq_blocking <= '0;
			ldu_cq_info_ret_bank0_PA_word <= '0;
			ldu_cq_info_ret_bank0_byte_mask <= '0;
			ldu_cq_info_ret_bank0_data <= '0;

			ldu_cq_info_ret_bank1_valid <= '0;
			ldu_cq_info_ret_bank1_WB_sent <= '0;
			ldu_cq_info_ret_bank1_cq_index <= '0;
			ldu_cq_info_ret_bank1_misaligned <= '0;
			ldu_cq_info_ret_bank1_dtlb_hit <= '0;
			ldu_cq_info_ret_bank1_page_fault <= '0;
			ldu_cq_info_ret_bank1_access_fault <= '0;
			ldu_cq_info_ret_bank1_dcache_hit <= '0;
			ldu_cq_info_ret_bank1_is_mem <= '0;
			ldu_cq_info_ret_bank1_aq_blocking <= '0;
			ldu_cq_info_ret_bank1_PA_word <= '0;
			ldu_cq_info_ret_bank1_byte_mask <= '0;
			ldu_cq_info_ret_bank1_data <= '0;

		    // misaligned queue info ret
		        // need in order to tie cq entry to mq if misaligned
			ldu_mq_info_ret_bank0_valid <= '0;
			ldu_mq_info_ret_bank0_cq_index <= '0;
			ldu_mq_info_ret_bank0_mq_index <= '0;

			ldu_mq_info_ret_bank1_valid <= '0;
			ldu_mq_info_ret_bank1_cq_index <= '0;
			ldu_mq_info_ret_bank1_mq_index <= '0;

		    // dtlb miss resp
			dtlb_miss_resp_valid <= '0;
			dtlb_miss_resp_cq_index <= '0;
			dtlb_miss_resp_is_mq <= '0;
			dtlb_miss_resp_mq_index <= '0;
			dtlb_miss_resp_PPN <= '0;
			dtlb_miss_resp_is_mem <= '0;
			dtlb_miss_resp_page_fault <= '0;
			dtlb_miss_resp_access_fault <= '0;

		    // dcache miss resp
			dcache_miss_resp_valid <= '0;
			dcache_miss_resp_cq_index <= '0;
			dcache_miss_resp_is_mq <= '0;
			dcache_miss_resp_mq_index <= '0;
			dcache_miss_resp_data <= '0;

		    // stamofu CAM return
			stamofu_CAM_return_bank0_valid <= '0;
			stamofu_CAM_return_bank0_cq_index <= '0;
			stamofu_CAM_return_bank0_is_mq <= '0;
			stamofu_CAM_return_bank0_mq_index <= '0;
			stamofu_CAM_return_bank0_stall <= '0;
			stamofu_CAM_return_bank0_stall_count <= '0;
			stamofu_CAM_return_bank0_forward <= '0;
			stamofu_CAM_return_bank0_nasty_forward <= '0;
			stamofu_CAM_return_bank0_forward_ROB_index <= '0;
			stamofu_CAM_return_bank0_forward_data <= '0;

			stamofu_CAM_return_bank1_valid <= '0;
			stamofu_CAM_return_bank1_cq_index <= '0;
			stamofu_CAM_return_bank1_is_mq <= '0;
			stamofu_CAM_return_bank1_mq_index <= '0;
			stamofu_CAM_return_bank1_stall <= '0;
			stamofu_CAM_return_bank1_stall_count <= '0;
			stamofu_CAM_return_bank1_forward <= '0;
			stamofu_CAM_return_bank1_nasty_forward <= '0;
			stamofu_CAM_return_bank1_forward_ROB_index <= '0;
			stamofu_CAM_return_bank1_forward_data <= '0;

		    // ldu CAM launch
			ldu_CAM_launch_valid <= '0;
			ldu_CAM_launch_cq_index <= '0;
			ldu_CAM_launch_is_mq <= '0;
			ldu_CAM_launch_mq_index <= '0;
			ldu_CAM_launch_is_amo <= '0;
			ldu_CAM_launch_PA_word <= '0;
			ldu_CAM_launch_byte_mask <= '0;
			ldu_CAM_launch_write_data <= '0;
			ldu_CAM_launch_mdp_info <= '0;
			ldu_CAM_launch_ROB_index <= '0;

		    // ldu CAM return
			last_ldu_CAM_return_valid <= '0;
			last_ldu_CAM_return_cq_index <= '0;
			last_ldu_CAM_return_is_mq <= '0;
			last_ldu_CAM_return_mq_index <= '0;
			last_ldu_CAM_return_forward <= '0;

		    // ldu_mq commit
			last_ldu_cq_commit_mq_valid <= '0;
			last_ldu_cq_commit_mq_index <= '0;
			ldu_cq_commit_mq_has_forward <= '0;

		    // store set CAM update
		        // implied dep
			last_ssu_CAM_update_valid <= '0;
			last_ssu_CAM_update_ld_mdp_info <= '0;
			last_ssu_CAM_update_ld_ROB_index <= '0;
			last_ssu_CAM_update_stamo_mdp_info <= '0;
			last_ssu_CAM_update_stamo_ROB_index <= '0;

		    // store set commit update
		        // implied no dep
			last_ssu_commit_update_valid <= '0;
			last_ssu_commit_update_mdp_info <= '0;
			last_ssu_commit_update_ROB_index <= '0;

		    // acquire advertisement
			stamofu_aq_mem_aq_active <= '0;
			stamofu_aq_mem_aq_oldest_abs_ROB_index <= '0;
			stamofu_aq_io_aq_active <= '0;
			stamofu_aq_io_aq_oldest_abs_ROB_index <= '0;

		    // oldest stamofu advertisement
			stamofu_incomplete_active <= '0;
			stamofu_oldest_incomplete_ROB_index <= '0;

		    // ROB complete notif
			last_ldu_complete_valid <= '0;
			last_ldu_complete_ROB_index <= '0;

		    // ROB commit
			rob_commit_upper_index <= '0;
			rob_commit_lower_index_valid_mask <= '0;

		    // ROB kill
			rob_kill_valid <= '0;
			rob_kill_abs_head_index <= '0;
			rob_kill_rel_kill_younger_index <= '0;
        end
        else begin

		    // op enqueue to central queue
			ldu_cq_enq_valid <= next_ldu_cq_enq_valid;
			ldu_cq_enq_killed <= next_ldu_cq_enq_killed;
			ldu_cq_enq_op <= next_ldu_cq_enq_op;
			ldu_cq_enq_mdp_info <= next_ldu_cq_enq_mdp_info;
			ldu_cq_enq_dest_PR <= next_ldu_cq_enq_dest_PR;
			ldu_cq_enq_ROB_index <= next_ldu_cq_enq_ROB_index;

		    // central queue enqueue feedback
			last_ldu_cq_enq_ready <= ldu_cq_enq_ready;
			last_ldu_cq_enq_index <= ldu_cq_enq_index;

		    // second try
			last_second_try_bank0_valid <= second_try_bank0_valid;
			last_second_try_bank1_valid <= second_try_bank1_valid;

			last_second_try_do_mispred <= second_try_do_mispred;
			last_second_try_is_mq <= second_try_is_mq;
			last_second_try_misaligned <= second_try_misaligned;
			last_second_try_page_fault <= second_try_page_fault;
			last_second_try_access_fault <= second_try_access_fault;
			last_second_try_is_mem <= second_try_is_mem;
			last_second_try_PPN <= second_try_PPN;
			last_second_try_PO_word <= second_try_PO_word;
			last_second_try_byte_mask <= second_try_byte_mask;
			last_second_try_cq_index <= second_try_cq_index;
			last_second_try_mq_index <= second_try_mq_index;

		    // second try feedback
			second_try_bank0_ack <= next_second_try_bank0_ack;
			second_try_bank1_ack <= next_second_try_bank1_ack;

		    // data try
			last_data_try_bank0_valid <= data_try_bank0_valid;
			last_data_try_bank1_valid <= data_try_bank1_valid;

			last_data_try_do_mispred <= data_try_do_mispred;
			last_data_try_data <= data_try_data;
			last_data_try_cq_index <= data_try_cq_index;

		    // data try feedback
			data_try_bank0_ack <= next_data_try_bank0_ack;
			data_try_bank1_ack <= next_data_try_bank1_ack;

		    // misaligned queue data try req
			ldu_mq_data_try_req_valid <= next_ldu_mq_data_try_req_valid;
			ldu_mq_data_try_cq_index <= next_ldu_mq_data_try_cq_index;

		    // misaligned queue info grab
			last_ldu_mq_info_grab_mq_index <= ldu_mq_info_grab_mq_index;
			last_ldu_mq_info_grab_data_try_ack <= ldu_mq_info_grab_data_try_ack;
			ldu_mq_info_grab_data_try_req <= next_ldu_mq_info_grab_data_try_req;
			ldu_mq_info_grab_data <= next_ldu_mq_info_grab_data;

		    // central queue info grab
			ldu_cq_info_grab_bank0_cq_index <= next_ldu_cq_info_grab_bank0_cq_index;
			last_ldu_cq_info_grab_bank0_op <= ldu_cq_info_grab_bank0_op;
			last_ldu_cq_info_grab_bank0_mdp_info <= ldu_cq_info_grab_bank0_mdp_info;
			last_ldu_cq_info_grab_bank0_dest_PR <= ldu_cq_info_grab_bank0_dest_PR;
			last_ldu_cq_info_grab_bank0_ROB_index <= ldu_cq_info_grab_bank0_ROB_index;

			ldu_cq_info_grab_bank1_cq_index <= next_ldu_cq_info_grab_bank1_cq_index;
			last_ldu_cq_info_grab_bank1_op <= ldu_cq_info_grab_bank1_op;
			last_ldu_cq_info_grab_bank1_mdp_info <= ldu_cq_info_grab_bank1_mdp_info;
			last_ldu_cq_info_grab_bank1_dest_PR <= ldu_cq_info_grab_bank1_dest_PR;
			last_ldu_cq_info_grab_bank1_ROB_index <= ldu_cq_info_grab_bank1_ROB_index;

		    // central queue info ret
			ldu_cq_info_ret_bank0_valid <= next_ldu_cq_info_ret_bank0_valid;
			ldu_cq_info_ret_bank0_WB_sent <= next_ldu_cq_info_ret_bank0_WB_sent;
			ldu_cq_info_ret_bank0_cq_index <= next_ldu_cq_info_ret_bank0_cq_index;
			ldu_cq_info_ret_bank0_misaligned <= next_ldu_cq_info_ret_bank0_misaligned;
			ldu_cq_info_ret_bank0_dtlb_hit <= next_ldu_cq_info_ret_bank0_dtlb_hit;
			ldu_cq_info_ret_bank0_page_fault <= next_ldu_cq_info_ret_bank0_page_fault;
			ldu_cq_info_ret_bank0_access_fault <= next_ldu_cq_info_ret_bank0_access_fault;
			ldu_cq_info_ret_bank0_dcache_hit <= next_ldu_cq_info_ret_bank0_dcache_hit;
			ldu_cq_info_ret_bank0_is_mem <= next_ldu_cq_info_ret_bank0_is_mem;
			ldu_cq_info_ret_bank0_aq_blocking <= next_ldu_cq_info_ret_bank0_aq_blocking;
			ldu_cq_info_ret_bank0_PA_word <= next_ldu_cq_info_ret_bank0_PA_word;
			ldu_cq_info_ret_bank0_byte_mask <= next_ldu_cq_info_ret_bank0_byte_mask;
			ldu_cq_info_ret_bank0_data <= next_ldu_cq_info_ret_bank0_data;

			ldu_cq_info_ret_bank1_valid <= next_ldu_cq_info_ret_bank1_valid;
			ldu_cq_info_ret_bank1_WB_sent <= next_ldu_cq_info_ret_bank1_WB_sent;
			ldu_cq_info_ret_bank1_cq_index <= next_ldu_cq_info_ret_bank1_cq_index;
			ldu_cq_info_ret_bank1_misaligned <= next_ldu_cq_info_ret_bank1_misaligned;
			ldu_cq_info_ret_bank1_dtlb_hit <= next_ldu_cq_info_ret_bank1_dtlb_hit;
			ldu_cq_info_ret_bank1_page_fault <= next_ldu_cq_info_ret_bank1_page_fault;
			ldu_cq_info_ret_bank1_access_fault <= next_ldu_cq_info_ret_bank1_access_fault;
			ldu_cq_info_ret_bank1_dcache_hit <= next_ldu_cq_info_ret_bank1_dcache_hit;
			ldu_cq_info_ret_bank1_is_mem <= next_ldu_cq_info_ret_bank1_is_mem;
			ldu_cq_info_ret_bank1_aq_blocking <= next_ldu_cq_info_ret_bank1_aq_blocking;
			ldu_cq_info_ret_bank1_PA_word <= next_ldu_cq_info_ret_bank1_PA_word;
			ldu_cq_info_ret_bank1_byte_mask <= next_ldu_cq_info_ret_bank1_byte_mask;
			ldu_cq_info_ret_bank1_data <= next_ldu_cq_info_ret_bank1_data;

		    // misaligned queue info ret
		        // need in order to tie cq entry to mq if misaligned
			ldu_mq_info_ret_bank0_valid <= next_ldu_mq_info_ret_bank0_valid;
			ldu_mq_info_ret_bank0_cq_index <= next_ldu_mq_info_ret_bank0_cq_index;
			ldu_mq_info_ret_bank0_mq_index <= next_ldu_mq_info_ret_bank0_mq_index;

			ldu_mq_info_ret_bank1_valid <= next_ldu_mq_info_ret_bank1_valid;
			ldu_mq_info_ret_bank1_cq_index <= next_ldu_mq_info_ret_bank1_cq_index;
			ldu_mq_info_ret_bank1_mq_index <= next_ldu_mq_info_ret_bank1_mq_index;

		    // dtlb miss resp
			dtlb_miss_resp_valid <= next_dtlb_miss_resp_valid;
			dtlb_miss_resp_cq_index <= next_dtlb_miss_resp_cq_index;
			dtlb_miss_resp_is_mq <= next_dtlb_miss_resp_is_mq;
			dtlb_miss_resp_mq_index <= next_dtlb_miss_resp_mq_index;
			dtlb_miss_resp_PPN <= next_dtlb_miss_resp_PPN;
			dtlb_miss_resp_is_mem <= next_dtlb_miss_resp_is_mem;
			dtlb_miss_resp_page_fault <= next_dtlb_miss_resp_page_fault;
			dtlb_miss_resp_access_fault <= next_dtlb_miss_resp_access_fault;

		    // dcache miss resp
			dcache_miss_resp_valid <= next_dcache_miss_resp_valid;
			dcache_miss_resp_cq_index <= next_dcache_miss_resp_cq_index;
			dcache_miss_resp_is_mq <= next_dcache_miss_resp_is_mq;
			dcache_miss_resp_mq_index <= next_dcache_miss_resp_mq_index;
			dcache_miss_resp_data <= next_dcache_miss_resp_data;

		    // stamofu CAM return
			stamofu_CAM_return_bank0_valid <= next_stamofu_CAM_return_bank0_valid;
			stamofu_CAM_return_bank0_cq_index <= next_stamofu_CAM_return_bank0_cq_index;
			stamofu_CAM_return_bank0_is_mq <= next_stamofu_CAM_return_bank0_is_mq;
			stamofu_CAM_return_bank0_mq_index <= next_stamofu_CAM_return_bank0_mq_index;
			stamofu_CAM_return_bank0_stall <= next_stamofu_CAM_return_bank0_stall;
			stamofu_CAM_return_bank0_stall_count <= next_stamofu_CAM_return_bank0_stall_count;
			stamofu_CAM_return_bank0_forward <= next_stamofu_CAM_return_bank0_forward;
			stamofu_CAM_return_bank0_nasty_forward <= next_stamofu_CAM_return_bank0_nasty_forward;
			stamofu_CAM_return_bank0_forward_ROB_index <= next_stamofu_CAM_return_bank0_forward_ROB_index;
			stamofu_CAM_return_bank0_forward_data <= next_stamofu_CAM_return_bank0_forward_data;

			stamofu_CAM_return_bank1_valid <= next_stamofu_CAM_return_bank1_valid;
			stamofu_CAM_return_bank1_cq_index <= next_stamofu_CAM_return_bank1_cq_index;
			stamofu_CAM_return_bank1_is_mq <= next_stamofu_CAM_return_bank1_is_mq;
			stamofu_CAM_return_bank1_mq_index <= next_stamofu_CAM_return_bank1_mq_index;
			stamofu_CAM_return_bank1_stall <= next_stamofu_CAM_return_bank1_stall;
			stamofu_CAM_return_bank1_stall_count <= next_stamofu_CAM_return_bank1_stall_count;
			stamofu_CAM_return_bank1_forward <= next_stamofu_CAM_return_bank1_forward;
			stamofu_CAM_return_bank1_nasty_forward <= next_stamofu_CAM_return_bank1_nasty_forward;
			stamofu_CAM_return_bank1_forward_ROB_index <= next_stamofu_CAM_return_bank1_forward_ROB_index;
			stamofu_CAM_return_bank1_forward_data <= next_stamofu_CAM_return_bank1_forward_data;

		    // ldu CAM launch
			ldu_CAM_launch_valid <= next_ldu_CAM_launch_valid;
			ldu_CAM_launch_cq_index <= next_ldu_CAM_launch_cq_index;
			ldu_CAM_launch_is_mq <= next_ldu_CAM_launch_is_mq;
			ldu_CAM_launch_mq_index <= next_ldu_CAM_launch_mq_index;
			ldu_CAM_launch_is_amo <= next_ldu_CAM_launch_is_amo;
			ldu_CAM_launch_PA_word <= next_ldu_CAM_launch_PA_word;
			ldu_CAM_launch_byte_mask <= next_ldu_CAM_launch_byte_mask;
			ldu_CAM_launch_write_data <= next_ldu_CAM_launch_write_data;
			ldu_CAM_launch_mdp_info <= next_ldu_CAM_launch_mdp_info;
			ldu_CAM_launch_ROB_index <= next_ldu_CAM_launch_ROB_index;

		    // ldu CAM return
			last_ldu_CAM_return_valid <= ldu_CAM_return_valid;
			last_ldu_CAM_return_cq_index <= ldu_CAM_return_cq_index;
			last_ldu_CAM_return_is_mq <= ldu_CAM_return_is_mq;
			last_ldu_CAM_return_mq_index <= ldu_CAM_return_mq_index;
			last_ldu_CAM_return_forward <= ldu_CAM_return_forward;

		    // ldu_mq commit
			last_ldu_cq_commit_mq_valid <= ldu_cq_commit_mq_valid;
			last_ldu_cq_commit_mq_index <= ldu_cq_commit_mq_index;
			ldu_cq_commit_mq_has_forward <= next_ldu_cq_commit_mq_has_forward;

		    // store set CAM update
		        // implied dep
			last_ssu_CAM_update_valid <= ssu_CAM_update_valid;
			last_ssu_CAM_update_ld_mdp_info <= ssu_CAM_update_ld_mdp_info;
			last_ssu_CAM_update_ld_ROB_index <= ssu_CAM_update_ld_ROB_index;
			last_ssu_CAM_update_stamo_mdp_info <= ssu_CAM_update_stamo_mdp_info;
			last_ssu_CAM_update_stamo_ROB_index <= ssu_CAM_update_stamo_ROB_index;

		    // store set commit update
		        // implied no dep
			last_ssu_commit_update_valid <= ssu_commit_update_valid;
			last_ssu_commit_update_mdp_info <= ssu_commit_update_mdp_info;
			last_ssu_commit_update_ROB_index <= ssu_commit_update_ROB_index;

		    // acquire advertisement
			stamofu_aq_mem_aq_active <= next_stamofu_aq_mem_aq_active;
			stamofu_aq_mem_aq_oldest_abs_ROB_index <= next_stamofu_aq_mem_aq_oldest_abs_ROB_index;
			stamofu_aq_io_aq_active <= next_stamofu_aq_io_aq_active;
			stamofu_aq_io_aq_oldest_abs_ROB_index <= next_stamofu_aq_io_aq_oldest_abs_ROB_index;

		    // oldest stamofu advertisement
			stamofu_incomplete_active <= next_stamofu_incomplete_active;
			stamofu_oldest_incomplete_ROB_index <= next_stamofu_oldest_incomplete_ROB_index;

		    // ROB complete notif
			last_ldu_complete_valid <= ldu_complete_valid;
			last_ldu_complete_ROB_index <= ldu_complete_ROB_index;

		    // ROB commit
			rob_commit_upper_index <= next_rob_commit_upper_index;
			rob_commit_lower_index_valid_mask <= next_rob_commit_lower_index_valid_mask;

		    // ROB kill
			rob_kill_valid <= next_rob_kill_valid;
			rob_kill_abs_head_index <= next_rob_kill_abs_head_index;
			rob_kill_rel_kill_younger_index <= next_rob_kill_rel_kill_younger_index;
        end
    end

endmodule