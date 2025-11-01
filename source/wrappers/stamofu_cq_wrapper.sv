/*
    Filename: stamofu_cq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_cq module. 
    Spec: LOROF/spec/design/stamofu_cq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_cq_wrapper #(
	parameter STAMOFU_CQ_ENTRIES = 24,
	parameter LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to central queue
	input logic next_stamofu_cq_enq_valid,
	input logic next_stamofu_cq_enq_killed,
	input logic next_stamofu_cq_enq_is_store,
	input logic next_stamofu_cq_enq_is_amo,
	input logic next_stamofu_cq_enq_is_fence,
	input logic [3:0] next_stamofu_cq_enq_op,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_cq_enq_mdp_info,
	input logic next_stamofu_cq_enq_mem_aq,
	input logic next_stamofu_cq_enq_io_aq,
	input logic next_stamofu_cq_enq_mem_rl,
	input logic next_stamofu_cq_enq_io_rl,
	input logic [LOG_PR_COUNT-1:0] next_stamofu_cq_enq_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_cq_enq_ROB_index,

    // central queue enqueue feedback
	output logic last_stamofu_cq_enq_ready,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_cq_enq_index,

    // central queue info grab
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_cq_info_grab_bank0_cq_index,
	output logic [MDPT_INFO_WIDTH-1:0] last_stamofu_cq_info_grab_bank0_mdp_info,
	output logic last_stamofu_cq_info_grab_bank0_mem_aq,
	output logic last_stamofu_cq_info_grab_bank0_io_aq,
	output logic last_stamofu_cq_info_grab_bank0_mem_rl,
	output logic last_stamofu_cq_info_grab_bank0_io_rl,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_cq_info_grab_bank0_ROB_index,

	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_cq_info_grab_bank1_cq_index,
	output logic [MDPT_INFO_WIDTH-1:0] last_stamofu_cq_info_grab_bank1_mdp_info,
	output logic last_stamofu_cq_info_grab_bank1_mem_aq,
	output logic last_stamofu_cq_info_grab_bank1_io_aq,
	output logic last_stamofu_cq_info_grab_bank1_mem_rl,
	output logic last_stamofu_cq_info_grab_bank1_io_rl,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_cq_info_grab_bank1_ROB_index,

    // central queue info ret
	input logic next_stamofu_cq_info_ret_bank0_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_cq_info_ret_bank0_cq_index,
	input logic next_stamofu_cq_info_ret_bank0_dtlb_hit,
	input logic next_stamofu_cq_info_ret_bank0_page_fault,
	input logic next_stamofu_cq_info_ret_bank0_access_fault,
	input logic next_stamofu_cq_info_ret_bank0_is_mem,
	input logic next_stamofu_cq_info_ret_bank0_mem_aq,
	input logic next_stamofu_cq_info_ret_bank0_io_aq,
	input logic next_stamofu_cq_info_ret_bank0_mem_rl,
	input logic next_stamofu_cq_info_ret_bank0_io_rl,
	input logic next_stamofu_cq_info_ret_bank0_misaligned,
	input logic next_stamofu_cq_info_ret_bank0_misaligned_exception,
	input logic [PA_WIDTH-2-1:0] next_stamofu_cq_info_ret_bank0_PA_word,
	input logic [3:0] next_stamofu_cq_info_ret_bank0_byte_mask,
	input logic [31:0] next_stamofu_cq_info_ret_bank0_data,

	input logic next_stamofu_cq_info_ret_bank1_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_cq_info_ret_bank1_cq_index,
	input logic next_stamofu_cq_info_ret_bank1_dtlb_hit,
	input logic next_stamofu_cq_info_ret_bank1_page_fault,
	input logic next_stamofu_cq_info_ret_bank1_access_fault,
	input logic next_stamofu_cq_info_ret_bank1_is_mem,
	input logic next_stamofu_cq_info_ret_bank1_mem_aq,
	input logic next_stamofu_cq_info_ret_bank1_io_aq,
	input logic next_stamofu_cq_info_ret_bank1_mem_rl,
	input logic next_stamofu_cq_info_ret_bank1_io_rl,
	input logic next_stamofu_cq_info_ret_bank1_misaligned,
	input logic next_stamofu_cq_info_ret_bank1_misaligned_exception,
	input logic [PA_WIDTH-2-1:0] next_stamofu_cq_info_ret_bank1_PA_word,
	input logic [3:0] next_stamofu_cq_info_ret_bank1_byte_mask,
	input logic [31:0] next_stamofu_cq_info_ret_bank1_data,

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
        // also interested in exceptions
	input logic next_stamofu_mq_info_ret_bank0_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank0_cq_index,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank0_mq_index,
	input logic next_stamofu_mq_info_ret_bank0_dtlb_hit,
	input logic next_stamofu_mq_info_ret_bank0_page_fault,
	input logic next_stamofu_mq_info_ret_bank0_access_fault,

	input logic next_stamofu_mq_info_ret_bank1_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank1_cq_index,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_stamofu_mq_info_ret_bank1_mq_index,
	input logic next_stamofu_mq_info_ret_bank1_dtlb_hit,
	input logic next_stamofu_mq_info_ret_bank1_page_fault,
	input logic next_stamofu_mq_info_ret_bank1_access_fault,

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
	input logic next_stamofu_mq_ldu_CAM_launch_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_ldu_CAM_launch_cq_index,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_stamofu_mq_ldu_CAM_launch_mq_index,
	input logic [PA_WIDTH-2-1:0] next_stamofu_mq_ldu_CAM_launch_PA_word,
	input logic [3:0] next_stamofu_mq_ldu_CAM_launch_byte_mask,
	input logic [31:0] next_stamofu_mq_ldu_CAM_launch_write_data,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_mq_ldu_CAM_launch_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_mq_ldu_CAM_launch_ROB_index,

    // ldu CAM launch
	output logic last_ldu_CAM_launch_valid,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_ldu_CAM_launch_cq_index,
	output logic last_ldu_CAM_launch_is_mq,
	output logic [LOG_STAMOFU_MQ_ENTRIES-1:0] last_ldu_CAM_launch_mq_index,
	output logic last_ldu_CAM_launch_is_amo,
	output logic [PA_WIDTH-2-1:0] last_ldu_CAM_launch_PA_word,
	output logic [3:0] last_ldu_CAM_launch_byte_mask,
	output logic [31:0] last_ldu_CAM_launch_write_data,
	output logic [MDPT_INFO_WIDTH-1:0] last_ldu_CAM_launch_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ldu_CAM_launch_ROB_index,

    // ldu CAM return
	input logic next_ldu_CAM_return_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_ldu_CAM_return_cq_index,
	input logic next_ldu_CAM_return_is_mq,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_ldu_CAM_return_mq_index,
	input logic next_ldu_CAM_return_forward,

    // stamofu CAM launch
	input logic next_stamofu_CAM_launch_bank0_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_stamofu_CAM_launch_bank0_cq_index,
	input logic next_stamofu_CAM_launch_bank0_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_stamofu_CAM_launch_bank0_mq_index,
	input logic [PA_WIDTH-2-1:0] next_stamofu_CAM_launch_bank0_PA_word,
	input logic [3:0] next_stamofu_CAM_launch_bank0_byte_mask,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_CAM_launch_bank0_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_CAM_launch_bank0_mdp_info,

	input logic next_stamofu_CAM_launch_bank1_valid,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_stamofu_CAM_launch_bank1_cq_index,
	input logic next_stamofu_CAM_launch_bank1_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_stamofu_CAM_launch_bank1_mq_index,
	input logic [PA_WIDTH-2-1:0] next_stamofu_CAM_launch_bank1_PA_word,
	input logic [3:0] next_stamofu_CAM_launch_bank1_byte_mask,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_CAM_launch_bank1_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_CAM_launch_bank1_mdp_info,

    // stamofu_mq CAM stage 2 info
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_CAM_return_bank0_cq_index,
	input logic next_stamofu_mq_CAM_return_bank0_stall,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_CAM_return_bank0_stall_count,
	input logic [3:0] next_stamofu_mq_CAM_return_bank0_forward,
	input logic next_stamofu_mq_CAM_return_bank0_nasty_forward,
	input logic next_stamofu_mq_CAM_return_bank0_forward_ROB_index,
	input logic [31:0] next_stamofu_mq_CAM_return_bank0_forward_data,

	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_CAM_return_bank1_cq_index,
	input logic next_stamofu_mq_CAM_return_bank1_stall,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_CAM_return_bank1_stall_count,
	input logic [3:0] next_stamofu_mq_CAM_return_bank1_forward,
	input logic next_stamofu_mq_CAM_return_bank1_nasty_forward,
	input logic next_stamofu_mq_CAM_return_bank1_forward_ROB_index,
	input logic [31:0] next_stamofu_mq_CAM_return_bank1_forward_data,

    // stamofu CAM return
	output logic last_stamofu_CAM_return_bank0_valid,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_stamofu_CAM_return_bank0_cq_index,
	output logic last_stamofu_CAM_return_bank0_is_mq,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_stamofu_CAM_return_bank0_mq_index,
	output logic last_stamofu_CAM_return_bank0_stall,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_CAM_return_bank0_stall_count,
	output logic [3:0] last_stamofu_CAM_return_bank0_forward,
	output logic last_stamofu_CAM_return_bank0_nasty_forward,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_CAM_return_bank0_forward_ROB_index,
	output logic [31:0] last_stamofu_CAM_return_bank0_forward_data,

	output logic last_stamofu_CAM_return_bank1_valid,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_stamofu_CAM_return_bank1_cq_index,
	output logic last_stamofu_CAM_return_bank1_is_mq,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_stamofu_CAM_return_bank1_mq_index,
	output logic last_stamofu_CAM_return_bank1_stall,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_CAM_return_bank1_stall_count,
	output logic [3:0] last_stamofu_CAM_return_bank1_forward,
	output logic last_stamofu_CAM_return_bank1_nasty_forward,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_CAM_return_bank1_forward_ROB_index,
	output logic [31:0] last_stamofu_CAM_return_bank1_forward_data,

    // misaligned queue info grab
	output logic [LOG_STAMOFU_MQ_ENTRIES-1:0] last_stamofu_mq_info_grab_mq_index,
	output logic last_stamofu_mq_info_grab_clear_entry,
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
	input logic next_stamofu_mq_info_grab_is_mem,
	input logic [PA_WIDTH-2-1:0] next_stamofu_mq_info_grab_PA_word,
	input logic [3:0] next_stamofu_mq_info_grab_byte_mask,
	input logic [31:0] next_stamofu_mq_info_grab_data,

    // write buffer enq bank 0
	output logic last_wr_buf_enq_bank0_valid,
	output logic last_wr_buf_enq_bank0_is_amo,
	output logic [3:0] last_wr_buf_enq_bank0_op,
	output logic [LOG_PR_COUNT-1:0] last_wr_buf_enq_bank0_dest_PR,
	output logic last_wr_buf_enq_bank0_is_mem,
	output logic [PA_WIDTH-2-1:0] last_wr_buf_enq_bank0_PA_word,
	output logic [3:0] last_wr_buf_enq_bank0_byte_mask,
	output logic [31:0] last_wr_buf_enq_bank0_data,

    // write buffer enq feedback bank 0
	input logic next_wr_buf_enq_bank0_ready,
	input logic next_wr_buf_enq_bank0_mem_present,
	input logic next_wr_buf_enq_bank0_io_present,

    // write buffer enq bank 1
	output logic last_wr_buf_enq_bank1_valid,
	output logic last_wr_buf_enq_bank1_is_amo,
	output logic [3:0] last_wr_buf_enq_bank1_op,
	output logic [LOG_PR_COUNT-1:0] last_wr_buf_enq_bank1_dest_PR,
	output logic last_wr_buf_enq_bank1_is_mem,
	output logic [PA_WIDTH-2-1:0] last_wr_buf_enq_bank1_PA_word,
	output logic [3:0] last_wr_buf_enq_bank1_byte_mask,
	output logic [31:0] last_wr_buf_enq_bank1_data,

    // write buffer enq feedback bank 1
	input logic next_wr_buf_enq_bank1_ready,
	input logic next_wr_buf_enq_bank1_mem_present,
	input logic next_wr_buf_enq_bank1_io_present,

    // fence restart notification to ROB
	output logic last_fence_restart_notif_valid,
	output logic [LOG_ROB_ENTRIES-1:0] last_fence_restart_notif_ROB_index,

    // fence restart notification backpressure from ROB
	input logic next_fence_restart_notif_ready,

    // sfence invalidation to MMU
	output logic last_sfence_inv_valid,
	output logic [VA_WIDTH-1:0] last_sfence_inv_VA,
	output logic [ASID_WIDTH-1:0] last_sfence_inv_ASID,

    // sfence invalidation backpressure from MMU
	input logic next_sfence_inv_ready,

    // exception to ROB
	output logic last_rob_exception_valid,
	output logic [VA_WIDTH-1:0] last_rob_exception_VA,
	output logic last_rob_exception_is_lr,
	output logic last_rob_exception_page_fault,
	output logic last_rob_exception_access_fault,
	output logic last_rob_exception_misaligned_exception,
	output logic [LOG_ROB_ENTRIES-1:0] last_rob_exception_ROB_index,

    // exception backpressure from ROB
	input logic next_rob_exception_ready,

    // store set CAM update bank 0
        // implied dep
	output logic last_ssu_CAM_update_bank0_valid,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_CAM_update_bank0_ld_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_CAM_update_bank0_ld_ROB_index,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_CAM_update_bank0_stamo_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_CAM_update_bank0_stamo_ROB_index,

    // store set CAM update bank 1
        // implied dep
	output logic last_ssu_CAM_update_bank1_valid,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_CAM_update_bank1_ld_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_CAM_update_bank1_ld_ROB_index,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_CAM_update_bank1_stamo_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_CAM_update_bank1_stamo_ROB_index,

    // store set commit update
        // implied no dep
	output logic last_ssu_commit_update_valid,
	output logic [MDPT_INFO_WIDTH-1:0] last_ssu_commit_update_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_ssu_commit_update_ROB_index,

    // oldest stamofu advertisement
	output logic last_stamofu_incomplete_active,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_oldest_incomplete_ROB_index,

    // stamofu mq complete notif
	input logic next_stamofu_mq_complete_valid,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_stamofu_mq_complete_cq_index,

    // ROB complete notif
	output logic last_stamofu_complete_valid,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_complete_ROB_index,

    // op dequeue from acquire queue
	output logic last_stamofu_aq_deq_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_aq_deq_ROB_index,

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

    // central queue info grab
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_grab_bank0_cq_index;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_info_grab_bank0_mdp_info;
	logic stamofu_cq_info_grab_bank0_mem_aq;
	logic stamofu_cq_info_grab_bank0_io_aq;
	logic stamofu_cq_info_grab_bank0_mem_rl;
	logic stamofu_cq_info_grab_bank0_io_rl;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_info_grab_bank0_ROB_index;

	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_grab_bank1_cq_index;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_info_grab_bank1_mdp_info;
	logic stamofu_cq_info_grab_bank1_mem_aq;
	logic stamofu_cq_info_grab_bank1_io_aq;
	logic stamofu_cq_info_grab_bank1_mem_rl;
	logic stamofu_cq_info_grab_bank1_io_rl;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_info_grab_bank1_ROB_index;

    // central queue info ret
	logic stamofu_cq_info_ret_bank0_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_ret_bank0_cq_index;
	logic stamofu_cq_info_ret_bank0_dtlb_hit;
	logic stamofu_cq_info_ret_bank0_page_fault;
	logic stamofu_cq_info_ret_bank0_access_fault;
	logic stamofu_cq_info_ret_bank0_is_mem;
	logic stamofu_cq_info_ret_bank0_mem_aq;
	logic stamofu_cq_info_ret_bank0_io_aq;
	logic stamofu_cq_info_ret_bank0_mem_rl;
	logic stamofu_cq_info_ret_bank0_io_rl;
	logic stamofu_cq_info_ret_bank0_misaligned;
	logic stamofu_cq_info_ret_bank0_misaligned_exception;
	logic [PA_WIDTH-2-1:0] stamofu_cq_info_ret_bank0_PA_word;
	logic [3:0] stamofu_cq_info_ret_bank0_byte_mask;
	logic [31:0] stamofu_cq_info_ret_bank0_data;

	logic stamofu_cq_info_ret_bank1_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_ret_bank1_cq_index;
	logic stamofu_cq_info_ret_bank1_dtlb_hit;
	logic stamofu_cq_info_ret_bank1_page_fault;
	logic stamofu_cq_info_ret_bank1_access_fault;
	logic stamofu_cq_info_ret_bank1_is_mem;
	logic stamofu_cq_info_ret_bank1_mem_aq;
	logic stamofu_cq_info_ret_bank1_io_aq;
	logic stamofu_cq_info_ret_bank1_mem_rl;
	logic stamofu_cq_info_ret_bank1_io_rl;
	logic stamofu_cq_info_ret_bank1_misaligned;
	logic stamofu_cq_info_ret_bank1_misaligned_exception;
	logic [PA_WIDTH-2-1:0] stamofu_cq_info_ret_bank1_PA_word;
	logic [3:0] stamofu_cq_info_ret_bank1_byte_mask;
	logic [31:0] stamofu_cq_info_ret_bank1_data;

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
        // also interested in exceptions
	logic stamofu_mq_info_ret_bank0_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_info_ret_bank0_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_ret_bank0_mq_index;
	logic stamofu_mq_info_ret_bank0_dtlb_hit;
	logic stamofu_mq_info_ret_bank0_page_fault;
	logic stamofu_mq_info_ret_bank0_access_fault;

	logic stamofu_mq_info_ret_bank1_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_info_ret_bank1_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_ret_bank1_mq_index;
	logic stamofu_mq_info_ret_bank1_dtlb_hit;
	logic stamofu_mq_info_ret_bank1_page_fault;
	logic stamofu_mq_info_ret_bank1_access_fault;

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

    // stamofu CAM launch
	logic stamofu_CAM_launch_bank0_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] stamofu_CAM_launch_bank0_cq_index;
	logic stamofu_CAM_launch_bank0_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] stamofu_CAM_launch_bank0_mq_index;
	logic [PA_WIDTH-2-1:0] stamofu_CAM_launch_bank0_PA_word;
	logic [3:0] stamofu_CAM_launch_bank0_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_CAM_launch_bank0_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_CAM_launch_bank0_mdp_info;

	logic stamofu_CAM_launch_bank1_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] stamofu_CAM_launch_bank1_cq_index;
	logic stamofu_CAM_launch_bank1_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] stamofu_CAM_launch_bank1_mq_index;
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

    // misaligned queue info grab
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_grab_mq_index;
	logic stamofu_mq_info_grab_clear_entry;
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
	logic stamofu_mq_info_grab_is_mem;
	logic [PA_WIDTH-2-1:0] stamofu_mq_info_grab_PA_word;
	logic [3:0] stamofu_mq_info_grab_byte_mask;
	logic [31:0] stamofu_mq_info_grab_data;

    // write buffer enq bank 0
	logic wr_buf_enq_bank0_valid;
	logic wr_buf_enq_bank0_is_amo;
	logic [3:0] wr_buf_enq_bank0_op;
	logic [LOG_PR_COUNT-1:0] wr_buf_enq_bank0_dest_PR;
	logic wr_buf_enq_bank0_is_mem;
	logic [PA_WIDTH-2-1:0] wr_buf_enq_bank0_PA_word;
	logic [3:0] wr_buf_enq_bank0_byte_mask;
	logic [31:0] wr_buf_enq_bank0_data;

    // write buffer enq feedback bank 0
	logic wr_buf_enq_bank0_ready;
	logic wr_buf_enq_bank0_mem_present;
	logic wr_buf_enq_bank0_io_present;

    // write buffer enq bank 1
	logic wr_buf_enq_bank1_valid;
	logic wr_buf_enq_bank1_is_amo;
	logic [3:0] wr_buf_enq_bank1_op;
	logic [LOG_PR_COUNT-1:0] wr_buf_enq_bank1_dest_PR;
	logic wr_buf_enq_bank1_is_mem;
	logic [PA_WIDTH-2-1:0] wr_buf_enq_bank1_PA_word;
	logic [3:0] wr_buf_enq_bank1_byte_mask;
	logic [31:0] wr_buf_enq_bank1_data;

    // write buffer enq feedback bank 1
	logic wr_buf_enq_bank1_ready;
	logic wr_buf_enq_bank1_mem_present;
	logic wr_buf_enq_bank1_io_present;

    // fence restart notification to ROB
	logic fence_restart_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] fence_restart_notif_ROB_index;

    // fence restart notification backpressure from ROB
	logic fence_restart_notif_ready;

    // sfence invalidation to MMU
	logic sfence_inv_valid;
	logic [VA_WIDTH-1:0] sfence_inv_VA;
	logic [ASID_WIDTH-1:0] sfence_inv_ASID;

    // sfence invalidation backpressure from MMU
	logic sfence_inv_ready;

    // exception to ROB
	logic rob_exception_valid;
	logic [VA_WIDTH-1:0] rob_exception_VA;
	logic rob_exception_is_lr;
	logic rob_exception_page_fault;
	logic rob_exception_access_fault;
	logic rob_exception_misaligned_exception;
	logic [LOG_ROB_ENTRIES-1:0] rob_exception_ROB_index;

    // exception backpressure from ROB
	logic rob_exception_ready;

    // store set CAM update bank 0
        // implied dep
	logic ssu_CAM_update_bank0_valid;
	logic [MDPT_INFO_WIDTH-1:0] ssu_CAM_update_bank0_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_CAM_update_bank0_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] ssu_CAM_update_bank0_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_CAM_update_bank0_stamo_ROB_index;

    // store set CAM update bank 1
        // implied dep
	logic ssu_CAM_update_bank1_valid;
	logic [MDPT_INFO_WIDTH-1:0] ssu_CAM_update_bank1_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_CAM_update_bank1_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] ssu_CAM_update_bank1_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_CAM_update_bank1_stamo_ROB_index;

    // store set commit update
        // implied no dep
	logic ssu_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] ssu_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_commit_update_ROB_index;

    // oldest stamofu advertisement
	logic stamofu_incomplete_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_oldest_incomplete_ROB_index;

    // stamofu mq complete notif
	logic stamofu_mq_complete_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_complete_cq_index;

    // ROB complete notif
	logic stamofu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_complete_ROB_index;

    // op dequeue from acquire queue
	logic stamofu_aq_deq_valid;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_deq_ROB_index;

    // ROB commit
	logic [LOG_ROB_ENTRIES-3:0] rob_commit_upper_index;
	logic [3:0] rob_commit_lower_index_valid_mask;

    // ROB kill
	logic rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	stamofu_cq #(
		.STAMOFU_CQ_ENTRIES(STAMOFU_CQ_ENTRIES),
		.LOG_STAMOFU_CQ_ENTRIES(LOG_STAMOFU_CQ_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to central queue
			stamofu_cq_enq_valid <= '0;
			stamofu_cq_enq_killed <= '0;
			stamofu_cq_enq_is_store <= '0;
			stamofu_cq_enq_is_amo <= '0;
			stamofu_cq_enq_is_fence <= '0;
			stamofu_cq_enq_op <= '0;
			stamofu_cq_enq_mdp_info <= '0;
			stamofu_cq_enq_mem_aq <= '0;
			stamofu_cq_enq_io_aq <= '0;
			stamofu_cq_enq_mem_rl <= '0;
			stamofu_cq_enq_io_rl <= '0;
			stamofu_cq_enq_dest_PR <= '0;
			stamofu_cq_enq_ROB_index <= '0;

		    // central queue enqueue feedback
			last_stamofu_cq_enq_ready <= '0;
			last_stamofu_cq_enq_index <= '0;

		    // central queue info grab
			stamofu_cq_info_grab_bank0_cq_index <= '0;
			last_stamofu_cq_info_grab_bank0_mdp_info <= '0;
			last_stamofu_cq_info_grab_bank0_mem_aq <= '0;
			last_stamofu_cq_info_grab_bank0_io_aq <= '0;
			last_stamofu_cq_info_grab_bank0_mem_rl <= '0;
			last_stamofu_cq_info_grab_bank0_io_rl <= '0;
			last_stamofu_cq_info_grab_bank0_ROB_index <= '0;

			stamofu_cq_info_grab_bank1_cq_index <= '0;
			last_stamofu_cq_info_grab_bank1_mdp_info <= '0;
			last_stamofu_cq_info_grab_bank1_mem_aq <= '0;
			last_stamofu_cq_info_grab_bank1_io_aq <= '0;
			last_stamofu_cq_info_grab_bank1_mem_rl <= '0;
			last_stamofu_cq_info_grab_bank1_io_rl <= '0;
			last_stamofu_cq_info_grab_bank1_ROB_index <= '0;

		    // central queue info ret
			stamofu_cq_info_ret_bank0_valid <= '0;
			stamofu_cq_info_ret_bank0_cq_index <= '0;
			stamofu_cq_info_ret_bank0_dtlb_hit <= '0;
			stamofu_cq_info_ret_bank0_page_fault <= '0;
			stamofu_cq_info_ret_bank0_access_fault <= '0;
			stamofu_cq_info_ret_bank0_is_mem <= '0;
			stamofu_cq_info_ret_bank0_mem_aq <= '0;
			stamofu_cq_info_ret_bank0_io_aq <= '0;
			stamofu_cq_info_ret_bank0_mem_rl <= '0;
			stamofu_cq_info_ret_bank0_io_rl <= '0;
			stamofu_cq_info_ret_bank0_misaligned <= '0;
			stamofu_cq_info_ret_bank0_misaligned_exception <= '0;
			stamofu_cq_info_ret_bank0_PA_word <= '0;
			stamofu_cq_info_ret_bank0_byte_mask <= '0;
			stamofu_cq_info_ret_bank0_data <= '0;

			stamofu_cq_info_ret_bank1_valid <= '0;
			stamofu_cq_info_ret_bank1_cq_index <= '0;
			stamofu_cq_info_ret_bank1_dtlb_hit <= '0;
			stamofu_cq_info_ret_bank1_page_fault <= '0;
			stamofu_cq_info_ret_bank1_access_fault <= '0;
			stamofu_cq_info_ret_bank1_is_mem <= '0;
			stamofu_cq_info_ret_bank1_mem_aq <= '0;
			stamofu_cq_info_ret_bank1_io_aq <= '0;
			stamofu_cq_info_ret_bank1_mem_rl <= '0;
			stamofu_cq_info_ret_bank1_io_rl <= '0;
			stamofu_cq_info_ret_bank1_misaligned <= '0;
			stamofu_cq_info_ret_bank1_misaligned_exception <= '0;
			stamofu_cq_info_ret_bank1_PA_word <= '0;
			stamofu_cq_info_ret_bank1_byte_mask <= '0;
			stamofu_cq_info_ret_bank1_data <= '0;

		    // misaligned queue info ret
		        // need in order to tie cq entry to mq if misaligned
		        // also interested in exceptions
			stamofu_mq_info_ret_bank0_valid <= '0;
			stamofu_mq_info_ret_bank0_cq_index <= '0;
			stamofu_mq_info_ret_bank0_mq_index <= '0;
			stamofu_mq_info_ret_bank0_dtlb_hit <= '0;
			stamofu_mq_info_ret_bank0_page_fault <= '0;
			stamofu_mq_info_ret_bank0_access_fault <= '0;

			stamofu_mq_info_ret_bank1_valid <= '0;
			stamofu_mq_info_ret_bank1_cq_index <= '0;
			stamofu_mq_info_ret_bank1_mq_index <= '0;
			stamofu_mq_info_ret_bank1_dtlb_hit <= '0;
			stamofu_mq_info_ret_bank1_page_fault <= '0;
			stamofu_mq_info_ret_bank1_access_fault <= '0;

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
			stamofu_mq_ldu_CAM_launch_valid <= '0;
			stamofu_mq_ldu_CAM_launch_cq_index <= '0;
			stamofu_mq_ldu_CAM_launch_mq_index <= '0;
			stamofu_mq_ldu_CAM_launch_PA_word <= '0;
			stamofu_mq_ldu_CAM_launch_byte_mask <= '0;
			stamofu_mq_ldu_CAM_launch_write_data <= '0;
			stamofu_mq_ldu_CAM_launch_mdp_info <= '0;
			stamofu_mq_ldu_CAM_launch_ROB_index <= '0;

		    // ldu CAM launch
			last_ldu_CAM_launch_valid <= '0;
			last_ldu_CAM_launch_cq_index <= '0;
			last_ldu_CAM_launch_is_mq <= '0;
			last_ldu_CAM_launch_mq_index <= '0;
			last_ldu_CAM_launch_is_amo <= '0;
			last_ldu_CAM_launch_PA_word <= '0;
			last_ldu_CAM_launch_byte_mask <= '0;
			last_ldu_CAM_launch_write_data <= '0;
			last_ldu_CAM_launch_mdp_info <= '0;
			last_ldu_CAM_launch_ROB_index <= '0;

		    // ldu CAM return
			ldu_CAM_return_valid <= '0;
			ldu_CAM_return_cq_index <= '0;
			ldu_CAM_return_is_mq <= '0;
			ldu_CAM_return_mq_index <= '0;
			ldu_CAM_return_forward <= '0;

		    // stamofu CAM launch
			stamofu_CAM_launch_bank0_valid <= '0;
			stamofu_CAM_launch_bank0_cq_index <= '0;
			stamofu_CAM_launch_bank0_is_mq <= '0;
			stamofu_CAM_launch_bank0_mq_index <= '0;
			stamofu_CAM_launch_bank0_PA_word <= '0;
			stamofu_CAM_launch_bank0_byte_mask <= '0;
			stamofu_CAM_launch_bank0_ROB_index <= '0;
			stamofu_CAM_launch_bank0_mdp_info <= '0;

			stamofu_CAM_launch_bank1_valid <= '0;
			stamofu_CAM_launch_bank1_cq_index <= '0;
			stamofu_CAM_launch_bank1_is_mq <= '0;
			stamofu_CAM_launch_bank1_mq_index <= '0;
			stamofu_CAM_launch_bank1_PA_word <= '0;
			stamofu_CAM_launch_bank1_byte_mask <= '0;
			stamofu_CAM_launch_bank1_ROB_index <= '0;
			stamofu_CAM_launch_bank1_mdp_info <= '0;

		    // stamofu_mq CAM stage 2 info
			stamofu_mq_CAM_return_bank0_cq_index <= '0;
			stamofu_mq_CAM_return_bank0_stall <= '0;
			stamofu_mq_CAM_return_bank0_stall_count <= '0;
			stamofu_mq_CAM_return_bank0_forward <= '0;
			stamofu_mq_CAM_return_bank0_nasty_forward <= '0;
			stamofu_mq_CAM_return_bank0_forward_ROB_index <= '0;
			stamofu_mq_CAM_return_bank0_forward_data <= '0;

			stamofu_mq_CAM_return_bank1_cq_index <= '0;
			stamofu_mq_CAM_return_bank1_stall <= '0;
			stamofu_mq_CAM_return_bank1_stall_count <= '0;
			stamofu_mq_CAM_return_bank1_forward <= '0;
			stamofu_mq_CAM_return_bank1_nasty_forward <= '0;
			stamofu_mq_CAM_return_bank1_forward_ROB_index <= '0;
			stamofu_mq_CAM_return_bank1_forward_data <= '0;

		    // stamofu CAM return
			last_stamofu_CAM_return_bank0_valid <= '0;
			last_stamofu_CAM_return_bank0_cq_index <= '0;
			last_stamofu_CAM_return_bank0_is_mq <= '0;
			last_stamofu_CAM_return_bank0_mq_index <= '0;
			last_stamofu_CAM_return_bank0_stall <= '0;
			last_stamofu_CAM_return_bank0_stall_count <= '0;
			last_stamofu_CAM_return_bank0_forward <= '0;
			last_stamofu_CAM_return_bank0_nasty_forward <= '0;
			last_stamofu_CAM_return_bank0_forward_ROB_index <= '0;
			last_stamofu_CAM_return_bank0_forward_data <= '0;

			last_stamofu_CAM_return_bank1_valid <= '0;
			last_stamofu_CAM_return_bank1_cq_index <= '0;
			last_stamofu_CAM_return_bank1_is_mq <= '0;
			last_stamofu_CAM_return_bank1_mq_index <= '0;
			last_stamofu_CAM_return_bank1_stall <= '0;
			last_stamofu_CAM_return_bank1_stall_count <= '0;
			last_stamofu_CAM_return_bank1_forward <= '0;
			last_stamofu_CAM_return_bank1_nasty_forward <= '0;
			last_stamofu_CAM_return_bank1_forward_ROB_index <= '0;
			last_stamofu_CAM_return_bank1_forward_data <= '0;

		    // misaligned queue info grab
			last_stamofu_mq_info_grab_mq_index <= '0;
			last_stamofu_mq_info_grab_clear_entry <= '0;
		        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
			stamofu_mq_info_grab_is_mem <= '0;
			stamofu_mq_info_grab_PA_word <= '0;
			stamofu_mq_info_grab_byte_mask <= '0;
			stamofu_mq_info_grab_data <= '0;

		    // write buffer enq bank 0
			last_wr_buf_enq_bank0_valid <= '0;
			last_wr_buf_enq_bank0_is_amo <= '0;
			last_wr_buf_enq_bank0_op <= '0;
			last_wr_buf_enq_bank0_dest_PR <= '0;
			last_wr_buf_enq_bank0_is_mem <= '0;
			last_wr_buf_enq_bank0_PA_word <= '0;
			last_wr_buf_enq_bank0_byte_mask <= '0;
			last_wr_buf_enq_bank0_data <= '0;

		    // write buffer enq feedback bank 0
			wr_buf_enq_bank0_ready <= '0;
			wr_buf_enq_bank0_mem_present <= '0;
			wr_buf_enq_bank0_io_present <= '0;

		    // write buffer enq bank 1
			last_wr_buf_enq_bank1_valid <= '0;
			last_wr_buf_enq_bank1_is_amo <= '0;
			last_wr_buf_enq_bank1_op <= '0;
			last_wr_buf_enq_bank1_dest_PR <= '0;
			last_wr_buf_enq_bank1_is_mem <= '0;
			last_wr_buf_enq_bank1_PA_word <= '0;
			last_wr_buf_enq_bank1_byte_mask <= '0;
			last_wr_buf_enq_bank1_data <= '0;

		    // write buffer enq feedback bank 1
			wr_buf_enq_bank1_ready <= '0;
			wr_buf_enq_bank1_mem_present <= '0;
			wr_buf_enq_bank1_io_present <= '0;

		    // fence restart notification to ROB
			last_fence_restart_notif_valid <= '0;
			last_fence_restart_notif_ROB_index <= '0;

		    // fence restart notification backpressure from ROB
			fence_restart_notif_ready <= '0;

		    // sfence invalidation to MMU
			last_sfence_inv_valid <= '0;
			last_sfence_inv_VA <= '0;
			last_sfence_inv_ASID <= '0;

		    // sfence invalidation backpressure from MMU
			sfence_inv_ready <= '0;

		    // exception to ROB
			last_rob_exception_valid <= '0;
			last_rob_exception_VA <= '0;
			last_rob_exception_is_lr <= '0;
			last_rob_exception_page_fault <= '0;
			last_rob_exception_access_fault <= '0;
			last_rob_exception_misaligned_exception <= '0;
			last_rob_exception_ROB_index <= '0;

		    // exception backpressure from ROB
			rob_exception_ready <= '0;

		    // store set CAM update bank 0
		        // implied dep
			last_ssu_CAM_update_bank0_valid <= '0;
			last_ssu_CAM_update_bank0_ld_mdp_info <= '0;
			last_ssu_CAM_update_bank0_ld_ROB_index <= '0;
			last_ssu_CAM_update_bank0_stamo_mdp_info <= '0;
			last_ssu_CAM_update_bank0_stamo_ROB_index <= '0;

		    // store set CAM update bank 1
		        // implied dep
			last_ssu_CAM_update_bank1_valid <= '0;
			last_ssu_CAM_update_bank1_ld_mdp_info <= '0;
			last_ssu_CAM_update_bank1_ld_ROB_index <= '0;
			last_ssu_CAM_update_bank1_stamo_mdp_info <= '0;
			last_ssu_CAM_update_bank1_stamo_ROB_index <= '0;

		    // store set commit update
		        // implied no dep
			last_ssu_commit_update_valid <= '0;
			last_ssu_commit_update_mdp_info <= '0;
			last_ssu_commit_update_ROB_index <= '0;

		    // oldest stamofu advertisement
			last_stamofu_incomplete_active <= '0;
			last_stamofu_oldest_incomplete_ROB_index <= '0;

		    // stamofu mq complete notif
			stamofu_mq_complete_valid <= '0;
			stamofu_mq_complete_cq_index <= '0;

		    // ROB complete notif
			last_stamofu_complete_valid <= '0;
			last_stamofu_complete_ROB_index <= '0;

		    // op dequeue from acquire queue
			last_stamofu_aq_deq_valid <= '0;
			stamofu_aq_deq_ROB_index <= '0;

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
			stamofu_cq_enq_valid <= next_stamofu_cq_enq_valid;
			stamofu_cq_enq_killed <= next_stamofu_cq_enq_killed;
			stamofu_cq_enq_is_store <= next_stamofu_cq_enq_is_store;
			stamofu_cq_enq_is_amo <= next_stamofu_cq_enq_is_amo;
			stamofu_cq_enq_is_fence <= next_stamofu_cq_enq_is_fence;
			stamofu_cq_enq_op <= next_stamofu_cq_enq_op;
			stamofu_cq_enq_mdp_info <= next_stamofu_cq_enq_mdp_info;
			stamofu_cq_enq_mem_aq <= next_stamofu_cq_enq_mem_aq;
			stamofu_cq_enq_io_aq <= next_stamofu_cq_enq_io_aq;
			stamofu_cq_enq_mem_rl <= next_stamofu_cq_enq_mem_rl;
			stamofu_cq_enq_io_rl <= next_stamofu_cq_enq_io_rl;
			stamofu_cq_enq_dest_PR <= next_stamofu_cq_enq_dest_PR;
			stamofu_cq_enq_ROB_index <= next_stamofu_cq_enq_ROB_index;

		    // central queue enqueue feedback
			last_stamofu_cq_enq_ready <= stamofu_cq_enq_ready;
			last_stamofu_cq_enq_index <= stamofu_cq_enq_index;

		    // central queue info grab
			stamofu_cq_info_grab_bank0_cq_index <= next_stamofu_cq_info_grab_bank0_cq_index;
			last_stamofu_cq_info_grab_bank0_mdp_info <= stamofu_cq_info_grab_bank0_mdp_info;
			last_stamofu_cq_info_grab_bank0_mem_aq <= stamofu_cq_info_grab_bank0_mem_aq;
			last_stamofu_cq_info_grab_bank0_io_aq <= stamofu_cq_info_grab_bank0_io_aq;
			last_stamofu_cq_info_grab_bank0_mem_rl <= stamofu_cq_info_grab_bank0_mem_rl;
			last_stamofu_cq_info_grab_bank0_io_rl <= stamofu_cq_info_grab_bank0_io_rl;
			last_stamofu_cq_info_grab_bank0_ROB_index <= stamofu_cq_info_grab_bank0_ROB_index;

			stamofu_cq_info_grab_bank1_cq_index <= next_stamofu_cq_info_grab_bank1_cq_index;
			last_stamofu_cq_info_grab_bank1_mdp_info <= stamofu_cq_info_grab_bank1_mdp_info;
			last_stamofu_cq_info_grab_bank1_mem_aq <= stamofu_cq_info_grab_bank1_mem_aq;
			last_stamofu_cq_info_grab_bank1_io_aq <= stamofu_cq_info_grab_bank1_io_aq;
			last_stamofu_cq_info_grab_bank1_mem_rl <= stamofu_cq_info_grab_bank1_mem_rl;
			last_stamofu_cq_info_grab_bank1_io_rl <= stamofu_cq_info_grab_bank1_io_rl;
			last_stamofu_cq_info_grab_bank1_ROB_index <= stamofu_cq_info_grab_bank1_ROB_index;

		    // central queue info ret
			stamofu_cq_info_ret_bank0_valid <= next_stamofu_cq_info_ret_bank0_valid;
			stamofu_cq_info_ret_bank0_cq_index <= next_stamofu_cq_info_ret_bank0_cq_index;
			stamofu_cq_info_ret_bank0_dtlb_hit <= next_stamofu_cq_info_ret_bank0_dtlb_hit;
			stamofu_cq_info_ret_bank0_page_fault <= next_stamofu_cq_info_ret_bank0_page_fault;
			stamofu_cq_info_ret_bank0_access_fault <= next_stamofu_cq_info_ret_bank0_access_fault;
			stamofu_cq_info_ret_bank0_is_mem <= next_stamofu_cq_info_ret_bank0_is_mem;
			stamofu_cq_info_ret_bank0_mem_aq <= next_stamofu_cq_info_ret_bank0_mem_aq;
			stamofu_cq_info_ret_bank0_io_aq <= next_stamofu_cq_info_ret_bank0_io_aq;
			stamofu_cq_info_ret_bank0_mem_rl <= next_stamofu_cq_info_ret_bank0_mem_rl;
			stamofu_cq_info_ret_bank0_io_rl <= next_stamofu_cq_info_ret_bank0_io_rl;
			stamofu_cq_info_ret_bank0_misaligned <= next_stamofu_cq_info_ret_bank0_misaligned;
			stamofu_cq_info_ret_bank0_misaligned_exception <= next_stamofu_cq_info_ret_bank0_misaligned_exception;
			stamofu_cq_info_ret_bank0_PA_word <= next_stamofu_cq_info_ret_bank0_PA_word;
			stamofu_cq_info_ret_bank0_byte_mask <= next_stamofu_cq_info_ret_bank0_byte_mask;
			stamofu_cq_info_ret_bank0_data <= next_stamofu_cq_info_ret_bank0_data;

			stamofu_cq_info_ret_bank1_valid <= next_stamofu_cq_info_ret_bank1_valid;
			stamofu_cq_info_ret_bank1_cq_index <= next_stamofu_cq_info_ret_bank1_cq_index;
			stamofu_cq_info_ret_bank1_dtlb_hit <= next_stamofu_cq_info_ret_bank1_dtlb_hit;
			stamofu_cq_info_ret_bank1_page_fault <= next_stamofu_cq_info_ret_bank1_page_fault;
			stamofu_cq_info_ret_bank1_access_fault <= next_stamofu_cq_info_ret_bank1_access_fault;
			stamofu_cq_info_ret_bank1_is_mem <= next_stamofu_cq_info_ret_bank1_is_mem;
			stamofu_cq_info_ret_bank1_mem_aq <= next_stamofu_cq_info_ret_bank1_mem_aq;
			stamofu_cq_info_ret_bank1_io_aq <= next_stamofu_cq_info_ret_bank1_io_aq;
			stamofu_cq_info_ret_bank1_mem_rl <= next_stamofu_cq_info_ret_bank1_mem_rl;
			stamofu_cq_info_ret_bank1_io_rl <= next_stamofu_cq_info_ret_bank1_io_rl;
			stamofu_cq_info_ret_bank1_misaligned <= next_stamofu_cq_info_ret_bank1_misaligned;
			stamofu_cq_info_ret_bank1_misaligned_exception <= next_stamofu_cq_info_ret_bank1_misaligned_exception;
			stamofu_cq_info_ret_bank1_PA_word <= next_stamofu_cq_info_ret_bank1_PA_word;
			stamofu_cq_info_ret_bank1_byte_mask <= next_stamofu_cq_info_ret_bank1_byte_mask;
			stamofu_cq_info_ret_bank1_data <= next_stamofu_cq_info_ret_bank1_data;

		    // misaligned queue info ret
		        // need in order to tie cq entry to mq if misaligned
		        // also interested in exceptions
			stamofu_mq_info_ret_bank0_valid <= next_stamofu_mq_info_ret_bank0_valid;
			stamofu_mq_info_ret_bank0_cq_index <= next_stamofu_mq_info_ret_bank0_cq_index;
			stamofu_mq_info_ret_bank0_mq_index <= next_stamofu_mq_info_ret_bank0_mq_index;
			stamofu_mq_info_ret_bank0_dtlb_hit <= next_stamofu_mq_info_ret_bank0_dtlb_hit;
			stamofu_mq_info_ret_bank0_page_fault <= next_stamofu_mq_info_ret_bank0_page_fault;
			stamofu_mq_info_ret_bank0_access_fault <= next_stamofu_mq_info_ret_bank0_access_fault;

			stamofu_mq_info_ret_bank1_valid <= next_stamofu_mq_info_ret_bank1_valid;
			stamofu_mq_info_ret_bank1_cq_index <= next_stamofu_mq_info_ret_bank1_cq_index;
			stamofu_mq_info_ret_bank1_mq_index <= next_stamofu_mq_info_ret_bank1_mq_index;
			stamofu_mq_info_ret_bank1_dtlb_hit <= next_stamofu_mq_info_ret_bank1_dtlb_hit;
			stamofu_mq_info_ret_bank1_page_fault <= next_stamofu_mq_info_ret_bank1_page_fault;
			stamofu_mq_info_ret_bank1_access_fault <= next_stamofu_mq_info_ret_bank1_access_fault;

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
			stamofu_mq_ldu_CAM_launch_valid <= next_stamofu_mq_ldu_CAM_launch_valid;
			stamofu_mq_ldu_CAM_launch_cq_index <= next_stamofu_mq_ldu_CAM_launch_cq_index;
			stamofu_mq_ldu_CAM_launch_mq_index <= next_stamofu_mq_ldu_CAM_launch_mq_index;
			stamofu_mq_ldu_CAM_launch_PA_word <= next_stamofu_mq_ldu_CAM_launch_PA_word;
			stamofu_mq_ldu_CAM_launch_byte_mask <= next_stamofu_mq_ldu_CAM_launch_byte_mask;
			stamofu_mq_ldu_CAM_launch_write_data <= next_stamofu_mq_ldu_CAM_launch_write_data;
			stamofu_mq_ldu_CAM_launch_mdp_info <= next_stamofu_mq_ldu_CAM_launch_mdp_info;
			stamofu_mq_ldu_CAM_launch_ROB_index <= next_stamofu_mq_ldu_CAM_launch_ROB_index;

		    // ldu CAM launch
			last_ldu_CAM_launch_valid <= ldu_CAM_launch_valid;
			last_ldu_CAM_launch_cq_index <= ldu_CAM_launch_cq_index;
			last_ldu_CAM_launch_is_mq <= ldu_CAM_launch_is_mq;
			last_ldu_CAM_launch_mq_index <= ldu_CAM_launch_mq_index;
			last_ldu_CAM_launch_is_amo <= ldu_CAM_launch_is_amo;
			last_ldu_CAM_launch_PA_word <= ldu_CAM_launch_PA_word;
			last_ldu_CAM_launch_byte_mask <= ldu_CAM_launch_byte_mask;
			last_ldu_CAM_launch_write_data <= ldu_CAM_launch_write_data;
			last_ldu_CAM_launch_mdp_info <= ldu_CAM_launch_mdp_info;
			last_ldu_CAM_launch_ROB_index <= ldu_CAM_launch_ROB_index;

		    // ldu CAM return
			ldu_CAM_return_valid <= next_ldu_CAM_return_valid;
			ldu_CAM_return_cq_index <= next_ldu_CAM_return_cq_index;
			ldu_CAM_return_is_mq <= next_ldu_CAM_return_is_mq;
			ldu_CAM_return_mq_index <= next_ldu_CAM_return_mq_index;
			ldu_CAM_return_forward <= next_ldu_CAM_return_forward;

		    // stamofu CAM launch
			stamofu_CAM_launch_bank0_valid <= next_stamofu_CAM_launch_bank0_valid;
			stamofu_CAM_launch_bank0_cq_index <= next_stamofu_CAM_launch_bank0_cq_index;
			stamofu_CAM_launch_bank0_is_mq <= next_stamofu_CAM_launch_bank0_is_mq;
			stamofu_CAM_launch_bank0_mq_index <= next_stamofu_CAM_launch_bank0_mq_index;
			stamofu_CAM_launch_bank0_PA_word <= next_stamofu_CAM_launch_bank0_PA_word;
			stamofu_CAM_launch_bank0_byte_mask <= next_stamofu_CAM_launch_bank0_byte_mask;
			stamofu_CAM_launch_bank0_ROB_index <= next_stamofu_CAM_launch_bank0_ROB_index;
			stamofu_CAM_launch_bank0_mdp_info <= next_stamofu_CAM_launch_bank0_mdp_info;

			stamofu_CAM_launch_bank1_valid <= next_stamofu_CAM_launch_bank1_valid;
			stamofu_CAM_launch_bank1_cq_index <= next_stamofu_CAM_launch_bank1_cq_index;
			stamofu_CAM_launch_bank1_is_mq <= next_stamofu_CAM_launch_bank1_is_mq;
			stamofu_CAM_launch_bank1_mq_index <= next_stamofu_CAM_launch_bank1_mq_index;
			stamofu_CAM_launch_bank1_PA_word <= next_stamofu_CAM_launch_bank1_PA_word;
			stamofu_CAM_launch_bank1_byte_mask <= next_stamofu_CAM_launch_bank1_byte_mask;
			stamofu_CAM_launch_bank1_ROB_index <= next_stamofu_CAM_launch_bank1_ROB_index;
			stamofu_CAM_launch_bank1_mdp_info <= next_stamofu_CAM_launch_bank1_mdp_info;

		    // stamofu_mq CAM stage 2 info
			stamofu_mq_CAM_return_bank0_cq_index <= next_stamofu_mq_CAM_return_bank0_cq_index;
			stamofu_mq_CAM_return_bank0_stall <= next_stamofu_mq_CAM_return_bank0_stall;
			stamofu_mq_CAM_return_bank0_stall_count <= next_stamofu_mq_CAM_return_bank0_stall_count;
			stamofu_mq_CAM_return_bank0_forward <= next_stamofu_mq_CAM_return_bank0_forward;
			stamofu_mq_CAM_return_bank0_nasty_forward <= next_stamofu_mq_CAM_return_bank0_nasty_forward;
			stamofu_mq_CAM_return_bank0_forward_ROB_index <= next_stamofu_mq_CAM_return_bank0_forward_ROB_index;
			stamofu_mq_CAM_return_bank0_forward_data <= next_stamofu_mq_CAM_return_bank0_forward_data;

			stamofu_mq_CAM_return_bank1_cq_index <= next_stamofu_mq_CAM_return_bank1_cq_index;
			stamofu_mq_CAM_return_bank1_stall <= next_stamofu_mq_CAM_return_bank1_stall;
			stamofu_mq_CAM_return_bank1_stall_count <= next_stamofu_mq_CAM_return_bank1_stall_count;
			stamofu_mq_CAM_return_bank1_forward <= next_stamofu_mq_CAM_return_bank1_forward;
			stamofu_mq_CAM_return_bank1_nasty_forward <= next_stamofu_mq_CAM_return_bank1_nasty_forward;
			stamofu_mq_CAM_return_bank1_forward_ROB_index <= next_stamofu_mq_CAM_return_bank1_forward_ROB_index;
			stamofu_mq_CAM_return_bank1_forward_data <= next_stamofu_mq_CAM_return_bank1_forward_data;

		    // stamofu CAM return
			last_stamofu_CAM_return_bank0_valid <= stamofu_CAM_return_bank0_valid;
			last_stamofu_CAM_return_bank0_cq_index <= stamofu_CAM_return_bank0_cq_index;
			last_stamofu_CAM_return_bank0_is_mq <= stamofu_CAM_return_bank0_is_mq;
			last_stamofu_CAM_return_bank0_mq_index <= stamofu_CAM_return_bank0_mq_index;
			last_stamofu_CAM_return_bank0_stall <= stamofu_CAM_return_bank0_stall;
			last_stamofu_CAM_return_bank0_stall_count <= stamofu_CAM_return_bank0_stall_count;
			last_stamofu_CAM_return_bank0_forward <= stamofu_CAM_return_bank0_forward;
			last_stamofu_CAM_return_bank0_nasty_forward <= stamofu_CAM_return_bank0_nasty_forward;
			last_stamofu_CAM_return_bank0_forward_ROB_index <= stamofu_CAM_return_bank0_forward_ROB_index;
			last_stamofu_CAM_return_bank0_forward_data <= stamofu_CAM_return_bank0_forward_data;

			last_stamofu_CAM_return_bank1_valid <= stamofu_CAM_return_bank1_valid;
			last_stamofu_CAM_return_bank1_cq_index <= stamofu_CAM_return_bank1_cq_index;
			last_stamofu_CAM_return_bank1_is_mq <= stamofu_CAM_return_bank1_is_mq;
			last_stamofu_CAM_return_bank1_mq_index <= stamofu_CAM_return_bank1_mq_index;
			last_stamofu_CAM_return_bank1_stall <= stamofu_CAM_return_bank1_stall;
			last_stamofu_CAM_return_bank1_stall_count <= stamofu_CAM_return_bank1_stall_count;
			last_stamofu_CAM_return_bank1_forward <= stamofu_CAM_return_bank1_forward;
			last_stamofu_CAM_return_bank1_nasty_forward <= stamofu_CAM_return_bank1_nasty_forward;
			last_stamofu_CAM_return_bank1_forward_ROB_index <= stamofu_CAM_return_bank1_forward_ROB_index;
			last_stamofu_CAM_return_bank1_forward_data <= stamofu_CAM_return_bank1_forward_data;

		    // misaligned queue info grab
			last_stamofu_mq_info_grab_mq_index <= stamofu_mq_info_grab_mq_index;
			last_stamofu_mq_info_grab_clear_entry <= stamofu_mq_info_grab_clear_entry;
		        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
			stamofu_mq_info_grab_is_mem <= next_stamofu_mq_info_grab_is_mem;
			stamofu_mq_info_grab_PA_word <= next_stamofu_mq_info_grab_PA_word;
			stamofu_mq_info_grab_byte_mask <= next_stamofu_mq_info_grab_byte_mask;
			stamofu_mq_info_grab_data <= next_stamofu_mq_info_grab_data;

		    // write buffer enq bank 0
			last_wr_buf_enq_bank0_valid <= wr_buf_enq_bank0_valid;
			last_wr_buf_enq_bank0_is_amo <= wr_buf_enq_bank0_is_amo;
			last_wr_buf_enq_bank0_op <= wr_buf_enq_bank0_op;
			last_wr_buf_enq_bank0_dest_PR <= wr_buf_enq_bank0_dest_PR;
			last_wr_buf_enq_bank0_is_mem <= wr_buf_enq_bank0_is_mem;
			last_wr_buf_enq_bank0_PA_word <= wr_buf_enq_bank0_PA_word;
			last_wr_buf_enq_bank0_byte_mask <= wr_buf_enq_bank0_byte_mask;
			last_wr_buf_enq_bank0_data <= wr_buf_enq_bank0_data;

		    // write buffer enq feedback bank 0
			wr_buf_enq_bank0_ready <= next_wr_buf_enq_bank0_ready;
			wr_buf_enq_bank0_mem_present <= next_wr_buf_enq_bank0_mem_present;
			wr_buf_enq_bank0_io_present <= next_wr_buf_enq_bank0_io_present;

		    // write buffer enq bank 1
			last_wr_buf_enq_bank1_valid <= wr_buf_enq_bank1_valid;
			last_wr_buf_enq_bank1_is_amo <= wr_buf_enq_bank1_is_amo;
			last_wr_buf_enq_bank1_op <= wr_buf_enq_bank1_op;
			last_wr_buf_enq_bank1_dest_PR <= wr_buf_enq_bank1_dest_PR;
			last_wr_buf_enq_bank1_is_mem <= wr_buf_enq_bank1_is_mem;
			last_wr_buf_enq_bank1_PA_word <= wr_buf_enq_bank1_PA_word;
			last_wr_buf_enq_bank1_byte_mask <= wr_buf_enq_bank1_byte_mask;
			last_wr_buf_enq_bank1_data <= wr_buf_enq_bank1_data;

		    // write buffer enq feedback bank 1
			wr_buf_enq_bank1_ready <= next_wr_buf_enq_bank1_ready;
			wr_buf_enq_bank1_mem_present <= next_wr_buf_enq_bank1_mem_present;
			wr_buf_enq_bank1_io_present <= next_wr_buf_enq_bank1_io_present;

		    // fence restart notification to ROB
			last_fence_restart_notif_valid <= fence_restart_notif_valid;
			last_fence_restart_notif_ROB_index <= fence_restart_notif_ROB_index;

		    // fence restart notification backpressure from ROB
			fence_restart_notif_ready <= next_fence_restart_notif_ready;

		    // sfence invalidation to MMU
			last_sfence_inv_valid <= sfence_inv_valid;
			last_sfence_inv_VA <= sfence_inv_VA;
			last_sfence_inv_ASID <= sfence_inv_ASID;

		    // sfence invalidation backpressure from MMU
			sfence_inv_ready <= next_sfence_inv_ready;

		    // exception to ROB
			last_rob_exception_valid <= rob_exception_valid;
			last_rob_exception_VA <= rob_exception_VA;
			last_rob_exception_is_lr <= rob_exception_is_lr;
			last_rob_exception_page_fault <= rob_exception_page_fault;
			last_rob_exception_access_fault <= rob_exception_access_fault;
			last_rob_exception_misaligned_exception <= rob_exception_misaligned_exception;
			last_rob_exception_ROB_index <= rob_exception_ROB_index;

		    // exception backpressure from ROB
			rob_exception_ready <= next_rob_exception_ready;

		    // store set CAM update bank 0
		        // implied dep
			last_ssu_CAM_update_bank0_valid <= ssu_CAM_update_bank0_valid;
			last_ssu_CAM_update_bank0_ld_mdp_info <= ssu_CAM_update_bank0_ld_mdp_info;
			last_ssu_CAM_update_bank0_ld_ROB_index <= ssu_CAM_update_bank0_ld_ROB_index;
			last_ssu_CAM_update_bank0_stamo_mdp_info <= ssu_CAM_update_bank0_stamo_mdp_info;
			last_ssu_CAM_update_bank0_stamo_ROB_index <= ssu_CAM_update_bank0_stamo_ROB_index;

		    // store set CAM update bank 1
		        // implied dep
			last_ssu_CAM_update_bank1_valid <= ssu_CAM_update_bank1_valid;
			last_ssu_CAM_update_bank1_ld_mdp_info <= ssu_CAM_update_bank1_ld_mdp_info;
			last_ssu_CAM_update_bank1_ld_ROB_index <= ssu_CAM_update_bank1_ld_ROB_index;
			last_ssu_CAM_update_bank1_stamo_mdp_info <= ssu_CAM_update_bank1_stamo_mdp_info;
			last_ssu_CAM_update_bank1_stamo_ROB_index <= ssu_CAM_update_bank1_stamo_ROB_index;

		    // store set commit update
		        // implied no dep
			last_ssu_commit_update_valid <= ssu_commit_update_valid;
			last_ssu_commit_update_mdp_info <= ssu_commit_update_mdp_info;
			last_ssu_commit_update_ROB_index <= ssu_commit_update_ROB_index;

		    // oldest stamofu advertisement
			last_stamofu_incomplete_active <= stamofu_incomplete_active;
			last_stamofu_oldest_incomplete_ROB_index <= stamofu_oldest_incomplete_ROB_index;

		    // stamofu mq complete notif
			stamofu_mq_complete_valid <= next_stamofu_mq_complete_valid;
			stamofu_mq_complete_cq_index <= next_stamofu_mq_complete_cq_index;

		    // ROB complete notif
			last_stamofu_complete_valid <= stamofu_complete_valid;
			last_stamofu_complete_ROB_index <= stamofu_complete_ROB_index;

		    // op dequeue from acquire queue
			last_stamofu_aq_deq_valid <= stamofu_aq_deq_valid;
			stamofu_aq_deq_ROB_index <= next_stamofu_aq_deq_ROB_index;

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