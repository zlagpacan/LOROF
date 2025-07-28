/*
    Filename: stamofu_cq_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_cq module. 
    Spec: LOROF/spec/design/stamofu_cq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter STAMOFU_CQ_ENTRIES = 24;
parameter LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES);

module stamofu_cq_tb ();

    // ----------------------------------------------------------------
    // TB setup:

    // parameters
    parameter PERIOD = 10;

    // TB signals:
    logic CLK = 1'b1, nRST;
    string test_case;
    string sub_test_case;
    int test_num = 0;
    int num_errors = 0;
    logic tb_error = 1'b0;

    // clock gen
    always begin #(PERIOD/2); CLK = ~CLK; end

    // ----------------------------------------------------------------
    // DUT signals:

    // op enqueue to central queue
	logic tb_stamofu_cq_enq_valid;
	logic tb_stamofu_cq_enq_killed;
	logic tb_stamofu_cq_enq_is_store;
	logic tb_stamofu_cq_enq_is_amo;
	logic tb_stamofu_cq_enq_is_fence;
	logic [3:0] tb_stamofu_cq_enq_op;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_cq_enq_mdp_info;
	logic tb_stamofu_cq_enq_mem_aq;
	logic tb_stamofu_cq_enq_io_aq;
	logic tb_stamofu_cq_enq_mem_rl;
	logic tb_stamofu_cq_enq_io_rl;
	logic [LOG_PR_COUNT-1:0] tb_stamofu_cq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_cq_enq_ROB_index;

    // central queue enqueue feedback
	logic DUT_stamofu_cq_enq_ready, expected_stamofu_cq_enq_ready;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_cq_enq_index, expected_stamofu_cq_enq_index;

    // central queue info grab
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_cq_info_grab_bank0_cq_index;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_cq_info_grab_bank0_mdp_info, expected_stamofu_cq_info_grab_bank0_mdp_info;
	logic DUT_stamofu_cq_info_grab_bank0_mem_aq, expected_stamofu_cq_info_grab_bank0_mem_aq;
	logic DUT_stamofu_cq_info_grab_bank0_io_aq, expected_stamofu_cq_info_grab_bank0_io_aq;
	logic DUT_stamofu_cq_info_grab_bank0_mem_rl, expected_stamofu_cq_info_grab_bank0_mem_rl;
	logic DUT_stamofu_cq_info_grab_bank0_io_rl, expected_stamofu_cq_info_grab_bank0_io_rl;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_cq_info_grab_bank0_ROB_index, expected_stamofu_cq_info_grab_bank0_ROB_index;

	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_cq_info_grab_bank1_cq_index;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_cq_info_grab_bank1_mdp_info, expected_stamofu_cq_info_grab_bank1_mdp_info;
	logic DUT_stamofu_cq_info_grab_bank1_mem_aq, expected_stamofu_cq_info_grab_bank1_mem_aq;
	logic DUT_stamofu_cq_info_grab_bank1_io_aq, expected_stamofu_cq_info_grab_bank1_io_aq;
	logic DUT_stamofu_cq_info_grab_bank1_mem_rl, expected_stamofu_cq_info_grab_bank1_mem_rl;
	logic DUT_stamofu_cq_info_grab_bank1_io_rl, expected_stamofu_cq_info_grab_bank1_io_rl;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_cq_info_grab_bank1_ROB_index, expected_stamofu_cq_info_grab_bank1_ROB_index;

    // central queue info ret
	logic tb_stamofu_cq_info_ret_bank0_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_cq_info_ret_bank0_cq_index;
	logic tb_stamofu_cq_info_ret_bank0_dtlb_hit;
	logic tb_stamofu_cq_info_ret_bank0_page_fault;
	logic tb_stamofu_cq_info_ret_bank0_access_fault;
	logic tb_stamofu_cq_info_ret_bank0_is_mem;
	logic tb_stamofu_cq_info_ret_bank0_mem_aq;
	logic tb_stamofu_cq_info_ret_bank0_io_aq;
	logic tb_stamofu_cq_info_ret_bank0_mem_rl;
	logic tb_stamofu_cq_info_ret_bank0_io_rl;
	logic tb_stamofu_cq_info_ret_bank0_misaligned;
	logic tb_stamofu_cq_info_ret_bank0_misaligned_exception;
	logic [PA_WIDTH-2-1:0] tb_stamofu_cq_info_ret_bank0_PA_word;
	logic [3:0] tb_stamofu_cq_info_ret_bank0_byte_mask;
	logic [31:0] tb_stamofu_cq_info_ret_bank0_data;

	logic tb_stamofu_cq_info_ret_bank1_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_cq_info_ret_bank1_cq_index;
	logic tb_stamofu_cq_info_ret_bank1_dtlb_hit;
	logic tb_stamofu_cq_info_ret_bank1_page_fault;
	logic tb_stamofu_cq_info_ret_bank1_access_fault;
	logic tb_stamofu_cq_info_ret_bank1_is_mem;
	logic tb_stamofu_cq_info_ret_bank1_mem_aq;
	logic tb_stamofu_cq_info_ret_bank1_io_aq;
	logic tb_stamofu_cq_info_ret_bank1_mem_rl;
	logic tb_stamofu_cq_info_ret_bank1_io_rl;
	logic tb_stamofu_cq_info_ret_bank1_misaligned;
	logic tb_stamofu_cq_info_ret_bank1_misaligned_exception;
	logic [PA_WIDTH-2-1:0] tb_stamofu_cq_info_ret_bank1_PA_word;
	logic [3:0] tb_stamofu_cq_info_ret_bank1_byte_mask;
	logic [31:0] tb_stamofu_cq_info_ret_bank1_data;

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
	logic tb_stamofu_mq_info_ret_bank0_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank0_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank0_mq_index;

	logic tb_stamofu_mq_info_ret_bank1_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank1_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank1_mq_index;

    // dtlb miss resp
	logic tb_dtlb_miss_resp_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_dtlb_miss_resp_cq_index;
	logic tb_dtlb_miss_resp_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_dtlb_miss_resp_mq_index;
	logic [PPN_WIDTH-1:0] tb_dtlb_miss_resp_PPN;
	logic tb_dtlb_miss_resp_is_mem;
	logic tb_dtlb_miss_resp_page_fault;
	logic tb_dtlb_miss_resp_access_fault;

    // ldu CAM launch
	logic DUT_ldu_CAM_launch_valid, expected_ldu_CAM_launch_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_ldu_CAM_launch_cq_index, expected_ldu_CAM_launch_cq_index;
	logic DUT_ldu_CAM_launch_is_mq, expected_ldu_CAM_launch_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] DUT_ldu_CAM_launch_mq_index, expected_ldu_CAM_launch_mq_index;
	logic DUT_ldu_CAM_launch_is_amo, expected_ldu_CAM_launch_is_amo;
	logic [PA_WIDTH-2-1:0] DUT_ldu_CAM_launch_PA_word, expected_ldu_CAM_launch_PA_word;
	logic [3:0] DUT_ldu_CAM_launch_byte_mask, expected_ldu_CAM_launch_byte_mask;
	logic [31:0] DUT_ldu_CAM_launch_write_data, expected_ldu_CAM_launch_write_data;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ldu_CAM_launch_mdp_info, expected_ldu_CAM_launch_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ldu_CAM_launch_ROB_index, expected_ldu_CAM_launch_ROB_index;

    // ldu CAM launch feedback
        // externally select stamofu_cq vs. stamofu_mq launch this cycle
        // not ready if doing mq this cycle
	logic tb_ldu_CAM_launch_ready;

    // ldu CAM return
	logic tb_ldu_CAM_return_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_ldu_CAM_return_cq_index;
	logic tb_ldu_CAM_return_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_ldu_CAM_return_mq_index;
	logic tb_ldu_CAM_return_forward;

    // stamofu CAM launch
	logic tb_stamofu_CAM_launch_bank0_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_stamofu_CAM_launch_bank0_cq_index;
	logic tb_stamofu_CAM_launch_bank0_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_stamofu_CAM_launch_bank0_mq_index;
	logic [PA_WIDTH-2-1:0] tb_stamofu_CAM_launch_bank0_PA_word;
	logic [3:0] tb_stamofu_CAM_launch_bank0_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_CAM_launch_bank0_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_CAM_launch_bank0_mdp_info;

	logic tb_stamofu_CAM_launch_bank1_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_stamofu_CAM_launch_bank1_cq_index;
	logic tb_stamofu_CAM_launch_bank1_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_stamofu_CAM_launch_bank1_mq_index;
	logic [PA_WIDTH-2-1:0] tb_stamofu_CAM_launch_bank1_PA_word;
	logic [3:0] tb_stamofu_CAM_launch_bank1_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_CAM_launch_bank1_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_CAM_launch_bank1_mdp_info;

    // stamofu_mq CAM stage 2 info
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_mq_CAM_return_bank0_updated_mdp_info;
	logic tb_stamofu_mq_CAM_return_bank0_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_mq_CAM_return_bank0_stall_count;
	logic [3:0] tb_stamofu_mq_CAM_return_bank0_forward;
	logic tb_stamofu_mq_CAM_return_bank0_nasty_forward;
	logic tb_stamofu_mq_CAM_return_bank0_forward_ROB_index;
	logic [31:0] tb_stamofu_mq_CAM_return_bank0_forward_data;

	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_mq_CAM_return_bank1_updated_mdp_info;
	logic tb_stamofu_mq_CAM_return_bank1_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_mq_CAM_return_bank1_stall_count;
	logic [3:0] tb_stamofu_mq_CAM_return_bank1_forward;
	logic tb_stamofu_mq_CAM_return_bank1_nasty_forward;
	logic tb_stamofu_mq_CAM_return_bank1_forward_ROB_index;
	logic [31:0] tb_stamofu_mq_CAM_return_bank1_forward_data;

    // stamofu CAM return
	logic DUT_stamofu_CAM_return_bank0_valid, expected_stamofu_CAM_return_bank0_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_stamofu_CAM_return_bank0_cq_index, expected_stamofu_CAM_return_bank0_cq_index;
	logic DUT_stamofu_CAM_return_bank0_is_mq, expected_stamofu_CAM_return_bank0_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_stamofu_CAM_return_bank0_mq_index, expected_stamofu_CAM_return_bank0_mq_index;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_CAM_return_bank0_updated_mdp_info, expected_stamofu_CAM_return_bank0_updated_mdp_info;
	logic DUT_stamofu_CAM_return_bank0_stall, expected_stamofu_CAM_return_bank0_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_CAM_return_bank0_stall_count, expected_stamofu_CAM_return_bank0_stall_count;
	logic [3:0] DUT_stamofu_CAM_return_bank0_forward, expected_stamofu_CAM_return_bank0_forward;
	logic DUT_stamofu_CAM_return_bank0_nasty_forward, expected_stamofu_CAM_return_bank0_nasty_forward;
	logic DUT_stamofu_CAM_return_bank0_forward_ROB_index, expected_stamofu_CAM_return_bank0_forward_ROB_index;
	logic [31:0] DUT_stamofu_CAM_return_bank0_forward_data, expected_stamofu_CAM_return_bank0_forward_data;

	logic DUT_stamofu_CAM_return_bank1_valid, expected_stamofu_CAM_return_bank1_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_stamofu_CAM_return_bank1_cq_index, expected_stamofu_CAM_return_bank1_cq_index;
	logic DUT_stamofu_CAM_return_bank1_is_mq, expected_stamofu_CAM_return_bank1_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_stamofu_CAM_return_bank1_mq_index, expected_stamofu_CAM_return_bank1_mq_index;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_CAM_return_bank1_updated_mdp_info, expected_stamofu_CAM_return_bank1_updated_mdp_info;
	logic DUT_stamofu_CAM_return_bank1_stall, expected_stamofu_CAM_return_bank1_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_CAM_return_bank1_stall_count, expected_stamofu_CAM_return_bank1_stall_count;
	logic [3:0] DUT_stamofu_CAM_return_bank1_forward, expected_stamofu_CAM_return_bank1_forward;
	logic DUT_stamofu_CAM_return_bank1_nasty_forward, expected_stamofu_CAM_return_bank1_nasty_forward;
	logic DUT_stamofu_CAM_return_bank1_forward_ROB_index, expected_stamofu_CAM_return_bank1_forward_ROB_index;
	logic [31:0] DUT_stamofu_CAM_return_bank1_forward_data, expected_stamofu_CAM_return_bank1_forward_data;

    // misaligned queue info grab
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] DUT_stamofu_mq_info_grab_mq_index, expected_stamofu_mq_info_grab_mq_index;
	logic DUT_stamofu_mq_info_grab_clear_entry, expected_stamofu_mq_info_grab_clear_entry;
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
	logic tb_stamofu_mq_info_grab_is_mem;
	logic [PA_WIDTH-2-1:0] tb_stamofu_mq_info_grab_PA_word;
	logic [3:0] tb_stamofu_mq_info_grab_byte_mask;
	logic [31:0] tb_stamofu_mq_info_grab_data;

    // write buffer enq
	logic DUT_wr_buf_enq_valid, expected_wr_buf_enq_valid;
	logic DUT_wr_buf_enq_is_amo, expected_wr_buf_enq_is_amo;
	logic [3:0] DUT_wr_buf_enq_op, expected_wr_buf_enq_op;
	logic DUT_wr_buf_enq_is_mem, expected_wr_buf_enq_is_mem;
	logic [PA_WIDTH-2-1:0] DUT_wr_buf_enq_PA_word, expected_wr_buf_enq_PA_word;
	logic [3:0] DUT_wr_buf_enq_byte_mask, expected_wr_buf_enq_byte_mask;
	logic [31:0] DUT_wr_buf_enq_data, expected_wr_buf_enq_data;

    // write buffer enq feedback
	logic tb_wr_buf_ready;
	logic tb_wr_buf_mem_present;
	logic tb_wr_buf_io_present;

    // fence restart notification to ROB
	logic DUT_fence_restart_notif_valid, expected_fence_restart_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] DUT_fence_restart_notif_ROB_index, expected_fence_restart_notif_ROB_index;

    // fence restart notification backpressure from ROB
	logic tb_fence_restart_notif_ready;

    // exception to ROB
	logic DUT_rob_exception_valid, expected_rob_exception_valid;
	logic [VA_WIDTH-1:0] DUT_rob_exception_VA, expected_rob_exception_VA;
	logic DUT_rob_exception_is_lr, expected_rob_exception_is_lr;
	logic DUT_rob_exception_page_fault, expected_rob_exception_page_fault;
	logic DUT_rob_exception_access_fault, expected_rob_exception_access_fault;
	logic DUT_rob_exception_misaligned_exception, expected_rob_exception_misaligned_exception;
	logic [LOG_ROB_ENTRIES-1:0] DUT_rob_exception_ROB_index, expected_rob_exception_ROB_index;

    // exception backpressure from ROB
	logic tb_rob_exception_ready;

    // store set commit update
        // implied no dep
	logic DUT_ssu_commit_update_valid, expected_ssu_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ssu_commit_update_mdp_info, expected_ssu_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ssu_commit_update_ROB_index, expected_ssu_commit_update_ROB_index;

    // oldest stamofu advertisement
	logic DUT_stamofu_active, expected_stamofu_active;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_oldest_ROB_index, expected_stamofu_oldest_ROB_index;

    // stamofu mq complete notif
	logic tb_stamofu_mq_complete_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_mq_complete_cq_index;

    // ROB complete notif
	logic DUT_stamofu_complete_valid, expected_stamofu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_complete_ROB_index, expected_stamofu_complete_ROB_index;

    // op dequeue from acquire queue
	logic DUT_stamofu_aq_deq_valid, expected_stamofu_aq_deq_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_deq_ROB_index;

    // ROB commit
	logic [LOG_ROB_ENTRIES-3:0] tb_rob_commit_upper_index;
	logic [3:0] tb_rob_commit_lower_index_valid_mask;

    // ROB kill
	logic tb_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_cq #(
		.STAMOFU_CQ_ENTRIES(STAMOFU_CQ_ENTRIES),
		.LOG_STAMOFU_CQ_ENTRIES(LOG_STAMOFU_CQ_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to central queue
		.stamofu_cq_enq_valid(tb_stamofu_cq_enq_valid),
		.stamofu_cq_enq_killed(tb_stamofu_cq_enq_killed),
		.stamofu_cq_enq_is_store(tb_stamofu_cq_enq_is_store),
		.stamofu_cq_enq_is_amo(tb_stamofu_cq_enq_is_amo),
		.stamofu_cq_enq_is_fence(tb_stamofu_cq_enq_is_fence),
		.stamofu_cq_enq_op(tb_stamofu_cq_enq_op),
		.stamofu_cq_enq_mdp_info(tb_stamofu_cq_enq_mdp_info),
		.stamofu_cq_enq_mem_aq(tb_stamofu_cq_enq_mem_aq),
		.stamofu_cq_enq_io_aq(tb_stamofu_cq_enq_io_aq),
		.stamofu_cq_enq_mem_rl(tb_stamofu_cq_enq_mem_rl),
		.stamofu_cq_enq_io_rl(tb_stamofu_cq_enq_io_rl),
		.stamofu_cq_enq_dest_PR(tb_stamofu_cq_enq_dest_PR),
		.stamofu_cq_enq_ROB_index(tb_stamofu_cq_enq_ROB_index),

	    // central queue enqueue feedback
		.stamofu_cq_enq_ready(DUT_stamofu_cq_enq_ready),
		.stamofu_cq_enq_index(DUT_stamofu_cq_enq_index),

	    // central queue info grab
		.stamofu_cq_info_grab_bank0_cq_index(tb_stamofu_cq_info_grab_bank0_cq_index),
		.stamofu_cq_info_grab_bank0_mdp_info(DUT_stamofu_cq_info_grab_bank0_mdp_info),
		.stamofu_cq_info_grab_bank0_mem_aq(DUT_stamofu_cq_info_grab_bank0_mem_aq),
		.stamofu_cq_info_grab_bank0_io_aq(DUT_stamofu_cq_info_grab_bank0_io_aq),
		.stamofu_cq_info_grab_bank0_mem_rl(DUT_stamofu_cq_info_grab_bank0_mem_rl),
		.stamofu_cq_info_grab_bank0_io_rl(DUT_stamofu_cq_info_grab_bank0_io_rl),
		.stamofu_cq_info_grab_bank0_ROB_index(DUT_stamofu_cq_info_grab_bank0_ROB_index),

		.stamofu_cq_info_grab_bank1_cq_index(tb_stamofu_cq_info_grab_bank1_cq_index),
		.stamofu_cq_info_grab_bank1_mdp_info(DUT_stamofu_cq_info_grab_bank1_mdp_info),
		.stamofu_cq_info_grab_bank1_mem_aq(DUT_stamofu_cq_info_grab_bank1_mem_aq),
		.stamofu_cq_info_grab_bank1_io_aq(DUT_stamofu_cq_info_grab_bank1_io_aq),
		.stamofu_cq_info_grab_bank1_mem_rl(DUT_stamofu_cq_info_grab_bank1_mem_rl),
		.stamofu_cq_info_grab_bank1_io_rl(DUT_stamofu_cq_info_grab_bank1_io_rl),
		.stamofu_cq_info_grab_bank1_ROB_index(DUT_stamofu_cq_info_grab_bank1_ROB_index),

	    // central queue info ret
		.stamofu_cq_info_ret_bank0_valid(tb_stamofu_cq_info_ret_bank0_valid),
		.stamofu_cq_info_ret_bank0_cq_index(tb_stamofu_cq_info_ret_bank0_cq_index),
		.stamofu_cq_info_ret_bank0_dtlb_hit(tb_stamofu_cq_info_ret_bank0_dtlb_hit),
		.stamofu_cq_info_ret_bank0_page_fault(tb_stamofu_cq_info_ret_bank0_page_fault),
		.stamofu_cq_info_ret_bank0_access_fault(tb_stamofu_cq_info_ret_bank0_access_fault),
		.stamofu_cq_info_ret_bank0_is_mem(tb_stamofu_cq_info_ret_bank0_is_mem),
		.stamofu_cq_info_ret_bank0_mem_aq(tb_stamofu_cq_info_ret_bank0_mem_aq),
		.stamofu_cq_info_ret_bank0_io_aq(tb_stamofu_cq_info_ret_bank0_io_aq),
		.stamofu_cq_info_ret_bank0_mem_rl(tb_stamofu_cq_info_ret_bank0_mem_rl),
		.stamofu_cq_info_ret_bank0_io_rl(tb_stamofu_cq_info_ret_bank0_io_rl),
		.stamofu_cq_info_ret_bank0_misaligned(tb_stamofu_cq_info_ret_bank0_misaligned),
		.stamofu_cq_info_ret_bank0_misaligned_exception(tb_stamofu_cq_info_ret_bank0_misaligned_exception),
		.stamofu_cq_info_ret_bank0_PA_word(tb_stamofu_cq_info_ret_bank0_PA_word),
		.stamofu_cq_info_ret_bank0_byte_mask(tb_stamofu_cq_info_ret_bank0_byte_mask),
		.stamofu_cq_info_ret_bank0_data(tb_stamofu_cq_info_ret_bank0_data),

		.stamofu_cq_info_ret_bank1_valid(tb_stamofu_cq_info_ret_bank1_valid),
		.stamofu_cq_info_ret_bank1_cq_index(tb_stamofu_cq_info_ret_bank1_cq_index),
		.stamofu_cq_info_ret_bank1_dtlb_hit(tb_stamofu_cq_info_ret_bank1_dtlb_hit),
		.stamofu_cq_info_ret_bank1_page_fault(tb_stamofu_cq_info_ret_bank1_page_fault),
		.stamofu_cq_info_ret_bank1_access_fault(tb_stamofu_cq_info_ret_bank1_access_fault),
		.stamofu_cq_info_ret_bank1_is_mem(tb_stamofu_cq_info_ret_bank1_is_mem),
		.stamofu_cq_info_ret_bank1_mem_aq(tb_stamofu_cq_info_ret_bank1_mem_aq),
		.stamofu_cq_info_ret_bank1_io_aq(tb_stamofu_cq_info_ret_bank1_io_aq),
		.stamofu_cq_info_ret_bank1_mem_rl(tb_stamofu_cq_info_ret_bank1_mem_rl),
		.stamofu_cq_info_ret_bank1_io_rl(tb_stamofu_cq_info_ret_bank1_io_rl),
		.stamofu_cq_info_ret_bank1_misaligned(tb_stamofu_cq_info_ret_bank1_misaligned),
		.stamofu_cq_info_ret_bank1_misaligned_exception(tb_stamofu_cq_info_ret_bank1_misaligned_exception),
		.stamofu_cq_info_ret_bank1_PA_word(tb_stamofu_cq_info_ret_bank1_PA_word),
		.stamofu_cq_info_ret_bank1_byte_mask(tb_stamofu_cq_info_ret_bank1_byte_mask),
		.stamofu_cq_info_ret_bank1_data(tb_stamofu_cq_info_ret_bank1_data),

	    // misaligned queue info ret
	        // need in order to tie cq entry to mq if misaligned
		.stamofu_mq_info_ret_bank0_valid(tb_stamofu_mq_info_ret_bank0_valid),
		.stamofu_mq_info_ret_bank0_cq_index(tb_stamofu_mq_info_ret_bank0_cq_index),
		.stamofu_mq_info_ret_bank0_mq_index(tb_stamofu_mq_info_ret_bank0_mq_index),

		.stamofu_mq_info_ret_bank1_valid(tb_stamofu_mq_info_ret_bank1_valid),
		.stamofu_mq_info_ret_bank1_cq_index(tb_stamofu_mq_info_ret_bank1_cq_index),
		.stamofu_mq_info_ret_bank1_mq_index(tb_stamofu_mq_info_ret_bank1_mq_index),

	    // dtlb miss resp
		.dtlb_miss_resp_valid(tb_dtlb_miss_resp_valid),
		.dtlb_miss_resp_cq_index(tb_dtlb_miss_resp_cq_index),
		.dtlb_miss_resp_is_mq(tb_dtlb_miss_resp_is_mq),
		.dtlb_miss_resp_mq_index(tb_dtlb_miss_resp_mq_index),
		.dtlb_miss_resp_PPN(tb_dtlb_miss_resp_PPN),
		.dtlb_miss_resp_is_mem(tb_dtlb_miss_resp_is_mem),
		.dtlb_miss_resp_page_fault(tb_dtlb_miss_resp_page_fault),
		.dtlb_miss_resp_access_fault(tb_dtlb_miss_resp_access_fault),

	    // ldu CAM launch
		.ldu_CAM_launch_valid(DUT_ldu_CAM_launch_valid),
		.ldu_CAM_launch_cq_index(DUT_ldu_CAM_launch_cq_index),
		.ldu_CAM_launch_is_mq(DUT_ldu_CAM_launch_is_mq),
		.ldu_CAM_launch_mq_index(DUT_ldu_CAM_launch_mq_index),
		.ldu_CAM_launch_is_amo(DUT_ldu_CAM_launch_is_amo),
		.ldu_CAM_launch_PA_word(DUT_ldu_CAM_launch_PA_word),
		.ldu_CAM_launch_byte_mask(DUT_ldu_CAM_launch_byte_mask),
		.ldu_CAM_launch_write_data(DUT_ldu_CAM_launch_write_data),
		.ldu_CAM_launch_mdp_info(DUT_ldu_CAM_launch_mdp_info),
		.ldu_CAM_launch_ROB_index(DUT_ldu_CAM_launch_ROB_index),

	    // ldu CAM launch feedback
	        // externally select stamofu_cq vs. stamofu_mq launch this cycle
	        // not ready if doing mq this cycle
		.ldu_CAM_launch_ready(tb_ldu_CAM_launch_ready),

	    // ldu CAM return
		.ldu_CAM_return_valid(tb_ldu_CAM_return_valid),
		.ldu_CAM_return_cq_index(tb_ldu_CAM_return_cq_index),
		.ldu_CAM_return_is_mq(tb_ldu_CAM_return_is_mq),
		.ldu_CAM_return_mq_index(tb_ldu_CAM_return_mq_index),
		.ldu_CAM_return_forward(tb_ldu_CAM_return_forward),

	    // stamofu CAM launch
		.stamofu_CAM_launch_bank0_valid(tb_stamofu_CAM_launch_bank0_valid),
		.stamofu_CAM_launch_bank0_cq_index(tb_stamofu_CAM_launch_bank0_cq_index),
		.stamofu_CAM_launch_bank0_is_mq(tb_stamofu_CAM_launch_bank0_is_mq),
		.stamofu_CAM_launch_bank0_mq_index(tb_stamofu_CAM_launch_bank0_mq_index),
		.stamofu_CAM_launch_bank0_PA_word(tb_stamofu_CAM_launch_bank0_PA_word),
		.stamofu_CAM_launch_bank0_byte_mask(tb_stamofu_CAM_launch_bank0_byte_mask),
		.stamofu_CAM_launch_bank0_ROB_index(tb_stamofu_CAM_launch_bank0_ROB_index),
		.stamofu_CAM_launch_bank0_mdp_info(tb_stamofu_CAM_launch_bank0_mdp_info),

		.stamofu_CAM_launch_bank1_valid(tb_stamofu_CAM_launch_bank1_valid),
		.stamofu_CAM_launch_bank1_cq_index(tb_stamofu_CAM_launch_bank1_cq_index),
		.stamofu_CAM_launch_bank1_is_mq(tb_stamofu_CAM_launch_bank1_is_mq),
		.stamofu_CAM_launch_bank1_mq_index(tb_stamofu_CAM_launch_bank1_mq_index),
		.stamofu_CAM_launch_bank1_PA_word(tb_stamofu_CAM_launch_bank1_PA_word),
		.stamofu_CAM_launch_bank1_byte_mask(tb_stamofu_CAM_launch_bank1_byte_mask),
		.stamofu_CAM_launch_bank1_ROB_index(tb_stamofu_CAM_launch_bank1_ROB_index),
		.stamofu_CAM_launch_bank1_mdp_info(tb_stamofu_CAM_launch_bank1_mdp_info),

	    // stamofu_mq CAM stage 2 info
		.stamofu_mq_CAM_return_bank0_updated_mdp_info(tb_stamofu_mq_CAM_return_bank0_updated_mdp_info),
		.stamofu_mq_CAM_return_bank0_stall(tb_stamofu_mq_CAM_return_bank0_stall),
		.stamofu_mq_CAM_return_bank0_stall_count(tb_stamofu_mq_CAM_return_bank0_stall_count),
		.stamofu_mq_CAM_return_bank0_forward(tb_stamofu_mq_CAM_return_bank0_forward),
		.stamofu_mq_CAM_return_bank0_nasty_forward(tb_stamofu_mq_CAM_return_bank0_nasty_forward),
		.stamofu_mq_CAM_return_bank0_forward_ROB_index(tb_stamofu_mq_CAM_return_bank0_forward_ROB_index),
		.stamofu_mq_CAM_return_bank0_forward_data(tb_stamofu_mq_CAM_return_bank0_forward_data),

		.stamofu_mq_CAM_return_bank1_updated_mdp_info(tb_stamofu_mq_CAM_return_bank1_updated_mdp_info),
		.stamofu_mq_CAM_return_bank1_stall(tb_stamofu_mq_CAM_return_bank1_stall),
		.stamofu_mq_CAM_return_bank1_stall_count(tb_stamofu_mq_CAM_return_bank1_stall_count),
		.stamofu_mq_CAM_return_bank1_forward(tb_stamofu_mq_CAM_return_bank1_forward),
		.stamofu_mq_CAM_return_bank1_nasty_forward(tb_stamofu_mq_CAM_return_bank1_nasty_forward),
		.stamofu_mq_CAM_return_bank1_forward_ROB_index(tb_stamofu_mq_CAM_return_bank1_forward_ROB_index),
		.stamofu_mq_CAM_return_bank1_forward_data(tb_stamofu_mq_CAM_return_bank1_forward_data),

	    // stamofu CAM return
		.stamofu_CAM_return_bank0_valid(DUT_stamofu_CAM_return_bank0_valid),
		.stamofu_CAM_return_bank0_cq_index(DUT_stamofu_CAM_return_bank0_cq_index),
		.stamofu_CAM_return_bank0_is_mq(DUT_stamofu_CAM_return_bank0_is_mq),
		.stamofu_CAM_return_bank0_mq_index(DUT_stamofu_CAM_return_bank0_mq_index),
		.stamofu_CAM_return_bank0_updated_mdp_info(DUT_stamofu_CAM_return_bank0_updated_mdp_info),
		.stamofu_CAM_return_bank0_stall(DUT_stamofu_CAM_return_bank0_stall),
		.stamofu_CAM_return_bank0_stall_count(DUT_stamofu_CAM_return_bank0_stall_count),
		.stamofu_CAM_return_bank0_forward(DUT_stamofu_CAM_return_bank0_forward),
		.stamofu_CAM_return_bank0_nasty_forward(DUT_stamofu_CAM_return_bank0_nasty_forward),
		.stamofu_CAM_return_bank0_forward_ROB_index(DUT_stamofu_CAM_return_bank0_forward_ROB_index),
		.stamofu_CAM_return_bank0_forward_data(DUT_stamofu_CAM_return_bank0_forward_data),

		.stamofu_CAM_return_bank1_valid(DUT_stamofu_CAM_return_bank1_valid),
		.stamofu_CAM_return_bank1_cq_index(DUT_stamofu_CAM_return_bank1_cq_index),
		.stamofu_CAM_return_bank1_is_mq(DUT_stamofu_CAM_return_bank1_is_mq),
		.stamofu_CAM_return_bank1_mq_index(DUT_stamofu_CAM_return_bank1_mq_index),
		.stamofu_CAM_return_bank1_updated_mdp_info(DUT_stamofu_CAM_return_bank1_updated_mdp_info),
		.stamofu_CAM_return_bank1_stall(DUT_stamofu_CAM_return_bank1_stall),
		.stamofu_CAM_return_bank1_stall_count(DUT_stamofu_CAM_return_bank1_stall_count),
		.stamofu_CAM_return_bank1_forward(DUT_stamofu_CAM_return_bank1_forward),
		.stamofu_CAM_return_bank1_nasty_forward(DUT_stamofu_CAM_return_bank1_nasty_forward),
		.stamofu_CAM_return_bank1_forward_ROB_index(DUT_stamofu_CAM_return_bank1_forward_ROB_index),
		.stamofu_CAM_return_bank1_forward_data(DUT_stamofu_CAM_return_bank1_forward_data),

	    // misaligned queue info grab
		.stamofu_mq_info_grab_mq_index(DUT_stamofu_mq_info_grab_mq_index),
		.stamofu_mq_info_grab_clear_entry(DUT_stamofu_mq_info_grab_clear_entry),
	        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
		.stamofu_mq_info_grab_is_mem(tb_stamofu_mq_info_grab_is_mem),
		.stamofu_mq_info_grab_PA_word(tb_stamofu_mq_info_grab_PA_word),
		.stamofu_mq_info_grab_byte_mask(tb_stamofu_mq_info_grab_byte_mask),
		.stamofu_mq_info_grab_data(tb_stamofu_mq_info_grab_data),

	    // write buffer enq
		.wr_buf_enq_valid(DUT_wr_buf_enq_valid),
		.wr_buf_enq_is_amo(DUT_wr_buf_enq_is_amo),
		.wr_buf_enq_op(DUT_wr_buf_enq_op),
		.wr_buf_enq_is_mem(DUT_wr_buf_enq_is_mem),
		.wr_buf_enq_PA_word(DUT_wr_buf_enq_PA_word),
		.wr_buf_enq_byte_mask(DUT_wr_buf_enq_byte_mask),
		.wr_buf_enq_data(DUT_wr_buf_enq_data),

	    // write buffer enq feedback
		.wr_buf_ready(tb_wr_buf_ready),
		.wr_buf_mem_present(tb_wr_buf_mem_present),
		.wr_buf_io_present(tb_wr_buf_io_present),

	    // fence restart notification to ROB
		.fence_restart_notif_valid(DUT_fence_restart_notif_valid),
		.fence_restart_notif_ROB_index(DUT_fence_restart_notif_ROB_index),

	    // fence restart notification backpressure from ROB
		.fence_restart_notif_ready(tb_fence_restart_notif_ready),

	    // exception to ROB
		.rob_exception_valid(DUT_rob_exception_valid),
		.rob_exception_VA(DUT_rob_exception_VA),
		.rob_exception_is_lr(DUT_rob_exception_is_lr),
		.rob_exception_page_fault(DUT_rob_exception_page_fault),
		.rob_exception_access_fault(DUT_rob_exception_access_fault),
		.rob_exception_misaligned_exception(DUT_rob_exception_misaligned_exception),
		.rob_exception_ROB_index(DUT_rob_exception_ROB_index),

	    // exception backpressure from ROB
		.rob_exception_ready(tb_rob_exception_ready),

	    // store set commit update
	        // implied no dep
		.ssu_commit_update_valid(DUT_ssu_commit_update_valid),
		.ssu_commit_update_mdp_info(DUT_ssu_commit_update_mdp_info),
		.ssu_commit_update_ROB_index(DUT_ssu_commit_update_ROB_index),

	    // oldest stamofu advertisement
		.stamofu_active(DUT_stamofu_active),
		.stamofu_oldest_ROB_index(DUT_stamofu_oldest_ROB_index),

	    // stamofu mq complete notif
		.stamofu_mq_complete_valid(tb_stamofu_mq_complete_valid),
		.stamofu_mq_complete_cq_index(tb_stamofu_mq_complete_cq_index),

	    // ROB complete notif
		.stamofu_complete_valid(DUT_stamofu_complete_valid),
		.stamofu_complete_ROB_index(DUT_stamofu_complete_ROB_index),

	    // op dequeue from acquire queue
		.stamofu_aq_deq_valid(DUT_stamofu_aq_deq_valid),
		.stamofu_aq_deq_ROB_index(tb_stamofu_aq_deq_ROB_index),

	    // ROB commit
		.rob_commit_upper_index(tb_rob_commit_upper_index),
		.rob_commit_lower_index_valid_mask(tb_rob_commit_lower_index_valid_mask),

	    // ROB kill
		.rob_kill_valid(tb_rob_kill_valid),
		.rob_kill_abs_head_index(tb_rob_kill_abs_head_index),
		.rob_kill_rel_kill_younger_index(tb_rob_kill_rel_kill_younger_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_stamofu_cq_enq_ready !== DUT_stamofu_cq_enq_ready) begin
			$display("TB ERROR: expected_stamofu_cq_enq_ready (%h) != DUT_stamofu_cq_enq_ready (%h)",
				expected_stamofu_cq_enq_ready, DUT_stamofu_cq_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_index !== DUT_stamofu_cq_enq_index) begin
			$display("TB ERROR: expected_stamofu_cq_enq_index (%h) != DUT_stamofu_cq_enq_index (%h)",
				expected_stamofu_cq_enq_index, DUT_stamofu_cq_enq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank0_mdp_info !== DUT_stamofu_cq_info_grab_bank0_mdp_info) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank0_mdp_info (%h) != DUT_stamofu_cq_info_grab_bank0_mdp_info (%h)",
				expected_stamofu_cq_info_grab_bank0_mdp_info, DUT_stamofu_cq_info_grab_bank0_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank0_mem_aq !== DUT_stamofu_cq_info_grab_bank0_mem_aq) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank0_mem_aq (%h) != DUT_stamofu_cq_info_grab_bank0_mem_aq (%h)",
				expected_stamofu_cq_info_grab_bank0_mem_aq, DUT_stamofu_cq_info_grab_bank0_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank0_io_aq !== DUT_stamofu_cq_info_grab_bank0_io_aq) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank0_io_aq (%h) != DUT_stamofu_cq_info_grab_bank0_io_aq (%h)",
				expected_stamofu_cq_info_grab_bank0_io_aq, DUT_stamofu_cq_info_grab_bank0_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank0_mem_rl !== DUT_stamofu_cq_info_grab_bank0_mem_rl) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank0_mem_rl (%h) != DUT_stamofu_cq_info_grab_bank0_mem_rl (%h)",
				expected_stamofu_cq_info_grab_bank0_mem_rl, DUT_stamofu_cq_info_grab_bank0_mem_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank0_io_rl !== DUT_stamofu_cq_info_grab_bank0_io_rl) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank0_io_rl (%h) != DUT_stamofu_cq_info_grab_bank0_io_rl (%h)",
				expected_stamofu_cq_info_grab_bank0_io_rl, DUT_stamofu_cq_info_grab_bank0_io_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank0_ROB_index !== DUT_stamofu_cq_info_grab_bank0_ROB_index) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank0_ROB_index (%h) != DUT_stamofu_cq_info_grab_bank0_ROB_index (%h)",
				expected_stamofu_cq_info_grab_bank0_ROB_index, DUT_stamofu_cq_info_grab_bank0_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank1_mdp_info !== DUT_stamofu_cq_info_grab_bank1_mdp_info) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank1_mdp_info (%h) != DUT_stamofu_cq_info_grab_bank1_mdp_info (%h)",
				expected_stamofu_cq_info_grab_bank1_mdp_info, DUT_stamofu_cq_info_grab_bank1_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank1_mem_aq !== DUT_stamofu_cq_info_grab_bank1_mem_aq) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank1_mem_aq (%h) != DUT_stamofu_cq_info_grab_bank1_mem_aq (%h)",
				expected_stamofu_cq_info_grab_bank1_mem_aq, DUT_stamofu_cq_info_grab_bank1_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank1_io_aq !== DUT_stamofu_cq_info_grab_bank1_io_aq) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank1_io_aq (%h) != DUT_stamofu_cq_info_grab_bank1_io_aq (%h)",
				expected_stamofu_cq_info_grab_bank1_io_aq, DUT_stamofu_cq_info_grab_bank1_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank1_mem_rl !== DUT_stamofu_cq_info_grab_bank1_mem_rl) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank1_mem_rl (%h) != DUT_stamofu_cq_info_grab_bank1_mem_rl (%h)",
				expected_stamofu_cq_info_grab_bank1_mem_rl, DUT_stamofu_cq_info_grab_bank1_mem_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank1_io_rl !== DUT_stamofu_cq_info_grab_bank1_io_rl) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank1_io_rl (%h) != DUT_stamofu_cq_info_grab_bank1_io_rl (%h)",
				expected_stamofu_cq_info_grab_bank1_io_rl, DUT_stamofu_cq_info_grab_bank1_io_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_grab_bank1_ROB_index !== DUT_stamofu_cq_info_grab_bank1_ROB_index) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_bank1_ROB_index (%h) != DUT_stamofu_cq_info_grab_bank1_ROB_index (%h)",
				expected_stamofu_cq_info_grab_bank1_ROB_index, DUT_stamofu_cq_info_grab_bank1_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_valid !== DUT_ldu_CAM_launch_valid) begin
			$display("TB ERROR: expected_ldu_CAM_launch_valid (%h) != DUT_ldu_CAM_launch_valid (%h)",
				expected_ldu_CAM_launch_valid, DUT_ldu_CAM_launch_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_cq_index !== DUT_ldu_CAM_launch_cq_index) begin
			$display("TB ERROR: expected_ldu_CAM_launch_cq_index (%h) != DUT_ldu_CAM_launch_cq_index (%h)",
				expected_ldu_CAM_launch_cq_index, DUT_ldu_CAM_launch_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_is_mq !== DUT_ldu_CAM_launch_is_mq) begin
			$display("TB ERROR: expected_ldu_CAM_launch_is_mq (%h) != DUT_ldu_CAM_launch_is_mq (%h)",
				expected_ldu_CAM_launch_is_mq, DUT_ldu_CAM_launch_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_mq_index !== DUT_ldu_CAM_launch_mq_index) begin
			$display("TB ERROR: expected_ldu_CAM_launch_mq_index (%h) != DUT_ldu_CAM_launch_mq_index (%h)",
				expected_ldu_CAM_launch_mq_index, DUT_ldu_CAM_launch_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_is_amo !== DUT_ldu_CAM_launch_is_amo) begin
			$display("TB ERROR: expected_ldu_CAM_launch_is_amo (%h) != DUT_ldu_CAM_launch_is_amo (%h)",
				expected_ldu_CAM_launch_is_amo, DUT_ldu_CAM_launch_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_PA_word !== DUT_ldu_CAM_launch_PA_word) begin
			$display("TB ERROR: expected_ldu_CAM_launch_PA_word (%h) != DUT_ldu_CAM_launch_PA_word (%h)",
				expected_ldu_CAM_launch_PA_word, DUT_ldu_CAM_launch_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_byte_mask !== DUT_ldu_CAM_launch_byte_mask) begin
			$display("TB ERROR: expected_ldu_CAM_launch_byte_mask (%h) != DUT_ldu_CAM_launch_byte_mask (%h)",
				expected_ldu_CAM_launch_byte_mask, DUT_ldu_CAM_launch_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_write_data !== DUT_ldu_CAM_launch_write_data) begin
			$display("TB ERROR: expected_ldu_CAM_launch_write_data (%h) != DUT_ldu_CAM_launch_write_data (%h)",
				expected_ldu_CAM_launch_write_data, DUT_ldu_CAM_launch_write_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_mdp_info !== DUT_ldu_CAM_launch_mdp_info) begin
			$display("TB ERROR: expected_ldu_CAM_launch_mdp_info (%h) != DUT_ldu_CAM_launch_mdp_info (%h)",
				expected_ldu_CAM_launch_mdp_info, DUT_ldu_CAM_launch_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_ROB_index !== DUT_ldu_CAM_launch_ROB_index) begin
			$display("TB ERROR: expected_ldu_CAM_launch_ROB_index (%h) != DUT_ldu_CAM_launch_ROB_index (%h)",
				expected_ldu_CAM_launch_ROB_index, DUT_ldu_CAM_launch_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_valid !== DUT_stamofu_CAM_return_bank0_valid) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_valid (%h) != DUT_stamofu_CAM_return_bank0_valid (%h)",
				expected_stamofu_CAM_return_bank0_valid, DUT_stamofu_CAM_return_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_cq_index !== DUT_stamofu_CAM_return_bank0_cq_index) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_cq_index (%h) != DUT_stamofu_CAM_return_bank0_cq_index (%h)",
				expected_stamofu_CAM_return_bank0_cq_index, DUT_stamofu_CAM_return_bank0_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_is_mq !== DUT_stamofu_CAM_return_bank0_is_mq) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_is_mq (%h) != DUT_stamofu_CAM_return_bank0_is_mq (%h)",
				expected_stamofu_CAM_return_bank0_is_mq, DUT_stamofu_CAM_return_bank0_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_mq_index !== DUT_stamofu_CAM_return_bank0_mq_index) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_mq_index (%h) != DUT_stamofu_CAM_return_bank0_mq_index (%h)",
				expected_stamofu_CAM_return_bank0_mq_index, DUT_stamofu_CAM_return_bank0_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_updated_mdp_info !== DUT_stamofu_CAM_return_bank0_updated_mdp_info) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_updated_mdp_info (%h) != DUT_stamofu_CAM_return_bank0_updated_mdp_info (%h)",
				expected_stamofu_CAM_return_bank0_updated_mdp_info, DUT_stamofu_CAM_return_bank0_updated_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_stall !== DUT_stamofu_CAM_return_bank0_stall) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_stall (%h) != DUT_stamofu_CAM_return_bank0_stall (%h)",
				expected_stamofu_CAM_return_bank0_stall, DUT_stamofu_CAM_return_bank0_stall);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_stall_count !== DUT_stamofu_CAM_return_bank0_stall_count) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_stall_count (%h) != DUT_stamofu_CAM_return_bank0_stall_count (%h)",
				expected_stamofu_CAM_return_bank0_stall_count, DUT_stamofu_CAM_return_bank0_stall_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_forward !== DUT_stamofu_CAM_return_bank0_forward) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_forward (%h) != DUT_stamofu_CAM_return_bank0_forward (%h)",
				expected_stamofu_CAM_return_bank0_forward, DUT_stamofu_CAM_return_bank0_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_nasty_forward !== DUT_stamofu_CAM_return_bank0_nasty_forward) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_nasty_forward (%h) != DUT_stamofu_CAM_return_bank0_nasty_forward (%h)",
				expected_stamofu_CAM_return_bank0_nasty_forward, DUT_stamofu_CAM_return_bank0_nasty_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_forward_ROB_index !== DUT_stamofu_CAM_return_bank0_forward_ROB_index) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_forward_ROB_index (%h) != DUT_stamofu_CAM_return_bank0_forward_ROB_index (%h)",
				expected_stamofu_CAM_return_bank0_forward_ROB_index, DUT_stamofu_CAM_return_bank0_forward_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank0_forward_data !== DUT_stamofu_CAM_return_bank0_forward_data) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank0_forward_data (%h) != DUT_stamofu_CAM_return_bank0_forward_data (%h)",
				expected_stamofu_CAM_return_bank0_forward_data, DUT_stamofu_CAM_return_bank0_forward_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_valid !== DUT_stamofu_CAM_return_bank1_valid) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_valid (%h) != DUT_stamofu_CAM_return_bank1_valid (%h)",
				expected_stamofu_CAM_return_bank1_valid, DUT_stamofu_CAM_return_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_cq_index !== DUT_stamofu_CAM_return_bank1_cq_index) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_cq_index (%h) != DUT_stamofu_CAM_return_bank1_cq_index (%h)",
				expected_stamofu_CAM_return_bank1_cq_index, DUT_stamofu_CAM_return_bank1_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_is_mq !== DUT_stamofu_CAM_return_bank1_is_mq) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_is_mq (%h) != DUT_stamofu_CAM_return_bank1_is_mq (%h)",
				expected_stamofu_CAM_return_bank1_is_mq, DUT_stamofu_CAM_return_bank1_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_mq_index !== DUT_stamofu_CAM_return_bank1_mq_index) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_mq_index (%h) != DUT_stamofu_CAM_return_bank1_mq_index (%h)",
				expected_stamofu_CAM_return_bank1_mq_index, DUT_stamofu_CAM_return_bank1_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_updated_mdp_info !== DUT_stamofu_CAM_return_bank1_updated_mdp_info) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_updated_mdp_info (%h) != DUT_stamofu_CAM_return_bank1_updated_mdp_info (%h)",
				expected_stamofu_CAM_return_bank1_updated_mdp_info, DUT_stamofu_CAM_return_bank1_updated_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_stall !== DUT_stamofu_CAM_return_bank1_stall) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_stall (%h) != DUT_stamofu_CAM_return_bank1_stall (%h)",
				expected_stamofu_CAM_return_bank1_stall, DUT_stamofu_CAM_return_bank1_stall);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_stall_count !== DUT_stamofu_CAM_return_bank1_stall_count) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_stall_count (%h) != DUT_stamofu_CAM_return_bank1_stall_count (%h)",
				expected_stamofu_CAM_return_bank1_stall_count, DUT_stamofu_CAM_return_bank1_stall_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_forward !== DUT_stamofu_CAM_return_bank1_forward) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_forward (%h) != DUT_stamofu_CAM_return_bank1_forward (%h)",
				expected_stamofu_CAM_return_bank1_forward, DUT_stamofu_CAM_return_bank1_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_nasty_forward !== DUT_stamofu_CAM_return_bank1_nasty_forward) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_nasty_forward (%h) != DUT_stamofu_CAM_return_bank1_nasty_forward (%h)",
				expected_stamofu_CAM_return_bank1_nasty_forward, DUT_stamofu_CAM_return_bank1_nasty_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_forward_ROB_index !== DUT_stamofu_CAM_return_bank1_forward_ROB_index) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_forward_ROB_index (%h) != DUT_stamofu_CAM_return_bank1_forward_ROB_index (%h)",
				expected_stamofu_CAM_return_bank1_forward_ROB_index, DUT_stamofu_CAM_return_bank1_forward_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_return_bank1_forward_data !== DUT_stamofu_CAM_return_bank1_forward_data) begin
			$display("TB ERROR: expected_stamofu_CAM_return_bank1_forward_data (%h) != DUT_stamofu_CAM_return_bank1_forward_data (%h)",
				expected_stamofu_CAM_return_bank1_forward_data, DUT_stamofu_CAM_return_bank1_forward_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_grab_mq_index !== DUT_stamofu_mq_info_grab_mq_index) begin
			$display("TB ERROR: expected_stamofu_mq_info_grab_mq_index (%h) != DUT_stamofu_mq_info_grab_mq_index (%h)",
				expected_stamofu_mq_info_grab_mq_index, DUT_stamofu_mq_info_grab_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_grab_clear_entry !== DUT_stamofu_mq_info_grab_clear_entry) begin
			$display("TB ERROR: expected_stamofu_mq_info_grab_clear_entry (%h) != DUT_stamofu_mq_info_grab_clear_entry (%h)",
				expected_stamofu_mq_info_grab_clear_entry, DUT_stamofu_mq_info_grab_clear_entry);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_valid !== DUT_wr_buf_enq_valid) begin
			$display("TB ERROR: expected_wr_buf_enq_valid (%h) != DUT_wr_buf_enq_valid (%h)",
				expected_wr_buf_enq_valid, DUT_wr_buf_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_is_amo !== DUT_wr_buf_enq_is_amo) begin
			$display("TB ERROR: expected_wr_buf_enq_is_amo (%h) != DUT_wr_buf_enq_is_amo (%h)",
				expected_wr_buf_enq_is_amo, DUT_wr_buf_enq_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_op !== DUT_wr_buf_enq_op) begin
			$display("TB ERROR: expected_wr_buf_enq_op (%h) != DUT_wr_buf_enq_op (%h)",
				expected_wr_buf_enq_op, DUT_wr_buf_enq_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_is_mem !== DUT_wr_buf_enq_is_mem) begin
			$display("TB ERROR: expected_wr_buf_enq_is_mem (%h) != DUT_wr_buf_enq_is_mem (%h)",
				expected_wr_buf_enq_is_mem, DUT_wr_buf_enq_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_PA_word !== DUT_wr_buf_enq_PA_word) begin
			$display("TB ERROR: expected_wr_buf_enq_PA_word (%h) != DUT_wr_buf_enq_PA_word (%h)",
				expected_wr_buf_enq_PA_word, DUT_wr_buf_enq_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_byte_mask !== DUT_wr_buf_enq_byte_mask) begin
			$display("TB ERROR: expected_wr_buf_enq_byte_mask (%h) != DUT_wr_buf_enq_byte_mask (%h)",
				expected_wr_buf_enq_byte_mask, DUT_wr_buf_enq_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_data !== DUT_wr_buf_enq_data) begin
			$display("TB ERROR: expected_wr_buf_enq_data (%h) != DUT_wr_buf_enq_data (%h)",
				expected_wr_buf_enq_data, DUT_wr_buf_enq_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_fence_restart_notif_valid !== DUT_fence_restart_notif_valid) begin
			$display("TB ERROR: expected_fence_restart_notif_valid (%h) != DUT_fence_restart_notif_valid (%h)",
				expected_fence_restart_notif_valid, DUT_fence_restart_notif_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_fence_restart_notif_ROB_index !== DUT_fence_restart_notif_ROB_index) begin
			$display("TB ERROR: expected_fence_restart_notif_ROB_index (%h) != DUT_fence_restart_notif_ROB_index (%h)",
				expected_fence_restart_notif_ROB_index, DUT_fence_restart_notif_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_exception_valid !== DUT_rob_exception_valid) begin
			$display("TB ERROR: expected_rob_exception_valid (%h) != DUT_rob_exception_valid (%h)",
				expected_rob_exception_valid, DUT_rob_exception_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_exception_VA !== DUT_rob_exception_VA) begin
			$display("TB ERROR: expected_rob_exception_VA (%h) != DUT_rob_exception_VA (%h)",
				expected_rob_exception_VA, DUT_rob_exception_VA);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_exception_is_lr !== DUT_rob_exception_is_lr) begin
			$display("TB ERROR: expected_rob_exception_is_lr (%h) != DUT_rob_exception_is_lr (%h)",
				expected_rob_exception_is_lr, DUT_rob_exception_is_lr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_exception_page_fault !== DUT_rob_exception_page_fault) begin
			$display("TB ERROR: expected_rob_exception_page_fault (%h) != DUT_rob_exception_page_fault (%h)",
				expected_rob_exception_page_fault, DUT_rob_exception_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_exception_access_fault !== DUT_rob_exception_access_fault) begin
			$display("TB ERROR: expected_rob_exception_access_fault (%h) != DUT_rob_exception_access_fault (%h)",
				expected_rob_exception_access_fault, DUT_rob_exception_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_exception_misaligned_exception !== DUT_rob_exception_misaligned_exception) begin
			$display("TB ERROR: expected_rob_exception_misaligned_exception (%h) != DUT_rob_exception_misaligned_exception (%h)",
				expected_rob_exception_misaligned_exception, DUT_rob_exception_misaligned_exception);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_exception_ROB_index !== DUT_rob_exception_ROB_index) begin
			$display("TB ERROR: expected_rob_exception_ROB_index (%h) != DUT_rob_exception_ROB_index (%h)",
				expected_rob_exception_ROB_index, DUT_rob_exception_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_commit_update_valid !== DUT_ssu_commit_update_valid) begin
			$display("TB ERROR: expected_ssu_commit_update_valid (%h) != DUT_ssu_commit_update_valid (%h)",
				expected_ssu_commit_update_valid, DUT_ssu_commit_update_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_commit_update_mdp_info !== DUT_ssu_commit_update_mdp_info) begin
			$display("TB ERROR: expected_ssu_commit_update_mdp_info (%h) != DUT_ssu_commit_update_mdp_info (%h)",
				expected_ssu_commit_update_mdp_info, DUT_ssu_commit_update_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_commit_update_ROB_index !== DUT_ssu_commit_update_ROB_index) begin
			$display("TB ERROR: expected_ssu_commit_update_ROB_index (%h) != DUT_ssu_commit_update_ROB_index (%h)",
				expected_ssu_commit_update_ROB_index, DUT_ssu_commit_update_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_active !== DUT_stamofu_active) begin
			$display("TB ERROR: expected_stamofu_active (%h) != DUT_stamofu_active (%h)",
				expected_stamofu_active, DUT_stamofu_active);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_oldest_ROB_index !== DUT_stamofu_oldest_ROB_index) begin
			$display("TB ERROR: expected_stamofu_oldest_ROB_index (%h) != DUT_stamofu_oldest_ROB_index (%h)",
				expected_stamofu_oldest_ROB_index, DUT_stamofu_oldest_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_complete_valid !== DUT_stamofu_complete_valid) begin
			$display("TB ERROR: expected_stamofu_complete_valid (%h) != DUT_stamofu_complete_valid (%h)",
				expected_stamofu_complete_valid, DUT_stamofu_complete_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_complete_ROB_index !== DUT_stamofu_complete_ROB_index) begin
			$display("TB ERROR: expected_stamofu_complete_ROB_index (%h) != DUT_stamofu_complete_ROB_index (%h)",
				expected_stamofu_complete_ROB_index, DUT_stamofu_complete_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_deq_valid !== DUT_stamofu_aq_deq_valid) begin
			$display("TB ERROR: expected_stamofu_aq_deq_valid (%h) != DUT_stamofu_aq_deq_valid (%h)",
				expected_stamofu_aq_deq_valid, DUT_stamofu_aq_deq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

        #(PERIOD / 10);
        tb_error = 1'b0;
    end
    endtask

    // ----------------------------------------------------------------
    // initial block:

    initial begin

        // ------------------------------------------------------------
        // reset:
        test_case = "reset";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        // inputs:
        sub_test_case = "assert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b0;
	    // op enqueue to central queue
		tb_stamofu_cq_enq_valid = 1'b0;
		tb_stamofu_cq_enq_killed = 1'b0;
		tb_stamofu_cq_enq_is_store = 1'b0;
		tb_stamofu_cq_enq_is_amo = 1'b0;
		tb_stamofu_cq_enq_is_fence = 1'b0;
		tb_stamofu_cq_enq_op = 4'b0000;
		tb_stamofu_cq_enq_mdp_info = 8'b00000000;
		tb_stamofu_cq_enq_mem_aq = 1'b0;
		tb_stamofu_cq_enq_io_aq = 1'b0;
		tb_stamofu_cq_enq_mem_rl = 1'b0;
		tb_stamofu_cq_enq_io_rl = 1'b0;
		tb_stamofu_cq_enq_dest_PR = 7'h00;
		tb_stamofu_cq_enq_ROB_index = 7'h00;
	    // central queue enqueue feedback
	    // central queue info grab
		tb_stamofu_cq_info_grab_bank0_cq_index = 'h0;
		tb_stamofu_cq_info_grab_bank1_cq_index = 'h0;
	    // central queue info ret
		tb_stamofu_cq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_cq_info_ret_bank0_cq_index = 'h0;
		tb_stamofu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_stamofu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_stamofu_cq_info_ret_bank0_mem_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank0_io_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank0_mem_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank0_io_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_stamofu_cq_info_ret_bank0_misaligned_exception = 1'b0;
		tb_stamofu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_stamofu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_stamofu_cq_info_ret_bank0_data = 32'h00000000;
		tb_stamofu_cq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_cq_info_ret_bank1_cq_index = 'h0;
		tb_stamofu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_stamofu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_stamofu_cq_info_ret_bank1_mem_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank1_io_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank1_mem_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank1_io_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_stamofu_cq_info_ret_bank1_misaligned_exception = 1'b0;
		tb_stamofu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_stamofu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_stamofu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_stamofu_mq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank0_cq_index = 'h0;
		tb_stamofu_mq_info_ret_bank0_mq_index = 'h0;
		tb_stamofu_mq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank1_cq_index = 'h0;
		tb_stamofu_mq_info_ret_bank1_mq_index = 'h0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_cq_index = 'h0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 'h0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // ldu CAM launch
	    // ldu CAM launch feedback
		tb_ldu_CAM_launch_ready = 1'b0;
	    // ldu CAM return
		tb_ldu_CAM_return_valid = 1'b0;
		tb_ldu_CAM_return_cq_index = 'h0;
		tb_ldu_CAM_return_is_mq = 1'b0;
		tb_ldu_CAM_return_mq_index = 'h0;
		tb_ldu_CAM_return_forward = 1'b0;
	    // stamofu CAM launch
		tb_stamofu_CAM_launch_bank0_valid = 1'b0;
		tb_stamofu_CAM_launch_bank0_cq_index = 'h0;
		tb_stamofu_CAM_launch_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_launch_bank0_mq_index = 'h0;
		tb_stamofu_CAM_launch_bank0_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank0_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank0_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank0_mdp_info = 8'b00000000;
		tb_stamofu_CAM_launch_bank1_valid = 1'b0;
		tb_stamofu_CAM_launch_bank1_cq_index = 'h0;
		tb_stamofu_CAM_launch_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_launch_bank1_mq_index = 'h0;
		tb_stamofu_CAM_launch_bank1_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank1_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank1_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank1_mdp_info = 8'b00000000;
	    // stamofu_mq CAM stage 2 info
		tb_stamofu_mq_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_mq_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_stall_count = 'h0;
		tb_stamofu_mq_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_mq_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_mq_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_mq_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_stall_count = 'h0;
		tb_stamofu_mq_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_mq_CAM_return_bank1_forward_data = 32'h00000000;
	    // stamofu CAM return
	    // misaligned queue info grab
		tb_stamofu_mq_info_grab_is_mem = 1'b0;
		tb_stamofu_mq_info_grab_PA_word = 32'h00000000;
		tb_stamofu_mq_info_grab_byte_mask = 4'b0000;
		tb_stamofu_mq_info_grab_data = 32'h00000000;
	    // write buffer enq
	    // write buffer enq feedback
		tb_wr_buf_ready = 1'b1;
		tb_wr_buf_mem_present = 1'b0;
		tb_wr_buf_io_present = 1'b0;
	    // fence restart notification to ROB
	    // fence restart notification backpressure from ROB
		tb_fence_restart_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // store set commit update
	    // oldest stamofu advertisement
	    // stamofu mq complete notif
		tb_stamofu_mq_complete_valid = 1'b0;
		tb_stamofu_mq_complete_cq_index = 'h0;
	    // ROB complete notif
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_ROB_index = 7'h00;
	    // ROB commit
		tb_rob_commit_upper_index = 5'h00;
		tb_rob_commit_lower_index_valid_mask = 4'b0000;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to central queue
	    // central queue enqueue feedback
		expected_stamofu_cq_enq_ready = 1'b1;
		expected_stamofu_cq_enq_index = 'h0;
	    // central queue info grab
		expected_stamofu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_stamofu_cq_info_grab_bank0_mem_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank0_io_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank0_mem_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank0_io_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank0_ROB_index = 7'h00;
		expected_stamofu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_stamofu_cq_info_grab_bank1_mem_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank1_io_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank1_mem_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank1_io_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // ldu CAM launch
		expected_ldu_CAM_launch_valid = 1'b0;
		expected_ldu_CAM_launch_cq_index = 'h0;
		expected_ldu_CAM_launch_is_mq = 1'b0;
		expected_ldu_CAM_launch_mq_index = 'h0;
		expected_ldu_CAM_launch_is_amo = 1'b0;
		expected_ldu_CAM_launch_PA_word = 32'h00000000;
		expected_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_ldu_CAM_launch_write_data = 32'h00000000;
		expected_ldu_CAM_launch_mdp_info = 8'b00000000;
		expected_ldu_CAM_launch_ROB_index = 7'h00;
	    // ldu CAM launch feedback
	    // ldu CAM return
	    // stamofu CAM launch
	    // stamofu_mq CAM stage 2 info
	    // stamofu CAM return
		expected_stamofu_CAM_return_bank0_valid = 1'b0;
		expected_stamofu_CAM_return_bank0_cq_index = 'h0;
		expected_stamofu_CAM_return_bank0_is_mq = 1'b0;
		expected_stamofu_CAM_return_bank0_mq_index = 'h0;
		expected_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		expected_stamofu_CAM_return_bank0_stall = 1'b0;
		expected_stamofu_CAM_return_bank0_stall_count = 'h0;
		expected_stamofu_CAM_return_bank0_forward = 1'b0;
		expected_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		expected_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		expected_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		expected_stamofu_CAM_return_bank1_valid = 1'b0;
		expected_stamofu_CAM_return_bank1_cq_index = 'h0;
		expected_stamofu_CAM_return_bank1_is_mq = 1'b0;
		expected_stamofu_CAM_return_bank1_mq_index = 'h0;
		expected_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		expected_stamofu_CAM_return_bank1_stall = 1'b0;
		expected_stamofu_CAM_return_bank1_stall_count = 'h0;
		expected_stamofu_CAM_return_bank1_forward = 1'b0;
		expected_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		expected_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		expected_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
	    // misaligned queue info grab
		expected_stamofu_mq_info_grab_mq_index = 'h0;
		expected_stamofu_mq_info_grab_clear_entry = 1'b0;
	    // write buffer enq
		expected_wr_buf_enq_valid = 1'b0;
		expected_wr_buf_enq_is_amo = 1'b0;
		expected_wr_buf_enq_op = 4'b0000;
		expected_wr_buf_enq_is_mem = 1'b0;
		expected_wr_buf_enq_PA_word = 32'h00000000;
		expected_wr_buf_enq_byte_mask = 4'b0000;
		expected_wr_buf_enq_data = 32'h00000000;
	    // write buffer enq feedback
	    // fence restart notification to ROB
		expected_fence_restart_notif_valid = 1'b0;
		expected_fence_restart_notif_ROB_index = 7'h00;
	    // fence restart notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_is_lr = 1'b0;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_misaligned_exception = 1'b0;
		expected_rob_exception_ROB_index = 7'h00;
	    // exception backpressure from ROB
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		expected_stamofu_active = 1'b0;
		expected_stamofu_oldest_ROB_index = 7'h00;
	    // stamofu mq complete notif
	    // ROB complete notif
		expected_stamofu_complete_valid = 1'b0;
		expected_stamofu_complete_ROB_index = 7'h00;
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_valid = 1'b0;
	    // ROB commit
	    // ROB kill

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_stamofu_cq_enq_valid = 1'b0;
		tb_stamofu_cq_enq_killed = 1'b0;
		tb_stamofu_cq_enq_is_store = 1'b0;
		tb_stamofu_cq_enq_is_amo = 1'b0;
		tb_stamofu_cq_enq_is_fence = 1'b0;
		tb_stamofu_cq_enq_op = 4'b0000;
		tb_stamofu_cq_enq_mdp_info = 8'b00000000;
		tb_stamofu_cq_enq_mem_aq = 1'b0;
		tb_stamofu_cq_enq_io_aq = 1'b0;
		tb_stamofu_cq_enq_mem_rl = 1'b0;
		tb_stamofu_cq_enq_io_rl = 1'b0;
		tb_stamofu_cq_enq_dest_PR = 7'h00;
		tb_stamofu_cq_enq_ROB_index = 7'h00;
	    // central queue enqueue feedback
	    // central queue info grab
		tb_stamofu_cq_info_grab_bank0_cq_index = 'h0;
		tb_stamofu_cq_info_grab_bank1_cq_index = 'h0;
	    // central queue info ret
		tb_stamofu_cq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_cq_info_ret_bank0_cq_index = 'h0;
		tb_stamofu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_stamofu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_stamofu_cq_info_ret_bank0_mem_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank0_io_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank0_mem_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank0_io_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_stamofu_cq_info_ret_bank0_misaligned_exception = 1'b0;
		tb_stamofu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_stamofu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_stamofu_cq_info_ret_bank0_data = 32'h00000000;
		tb_stamofu_cq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_cq_info_ret_bank1_cq_index = 'h0;
		tb_stamofu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_stamofu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_stamofu_cq_info_ret_bank1_mem_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank1_io_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank1_mem_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank1_io_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_stamofu_cq_info_ret_bank1_misaligned_exception = 1'b0;
		tb_stamofu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_stamofu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_stamofu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_stamofu_mq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank0_cq_index = 'h0;
		tb_stamofu_mq_info_ret_bank0_mq_index = 'h0;
		tb_stamofu_mq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank1_cq_index = 'h0;
		tb_stamofu_mq_info_ret_bank1_mq_index = 'h0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_cq_index = 'h0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 'h0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // ldu CAM launch
	    // ldu CAM launch feedback
		tb_ldu_CAM_launch_ready = 1'b0;
	    // ldu CAM return
		tb_ldu_CAM_return_valid = 1'b0;
		tb_ldu_CAM_return_cq_index = 'h0;
		tb_ldu_CAM_return_is_mq = 1'b0;
		tb_ldu_CAM_return_mq_index = 'h0;
		tb_ldu_CAM_return_forward = 1'b0;
	    // stamofu CAM launch
		tb_stamofu_CAM_launch_bank0_valid = 1'b0;
		tb_stamofu_CAM_launch_bank0_cq_index = 'h0;
		tb_stamofu_CAM_launch_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_launch_bank0_mq_index = 'h0;
		tb_stamofu_CAM_launch_bank0_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank0_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank0_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank0_mdp_info = 8'b00000000;
		tb_stamofu_CAM_launch_bank1_valid = 1'b0;
		tb_stamofu_CAM_launch_bank1_cq_index = 'h0;
		tb_stamofu_CAM_launch_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_launch_bank1_mq_index = 'h0;
		tb_stamofu_CAM_launch_bank1_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank1_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank1_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank1_mdp_info = 8'b00000000;
	    // stamofu_mq CAM stage 2 info
		tb_stamofu_mq_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_mq_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_stall_count = 'h0;
		tb_stamofu_mq_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_mq_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_mq_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_mq_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_stall_count = 'h0;
		tb_stamofu_mq_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_mq_CAM_return_bank1_forward_data = 32'h00000000;
	    // stamofu CAM return
	    // misaligned queue info grab
		tb_stamofu_mq_info_grab_is_mem = 1'b0;
		tb_stamofu_mq_info_grab_PA_word = 32'h00000000;
		tb_stamofu_mq_info_grab_byte_mask = 4'b0000;
		tb_stamofu_mq_info_grab_data = 32'h00000000;
	    // write buffer enq
	    // write buffer enq feedback
		tb_wr_buf_ready = 1'b1;
		tb_wr_buf_mem_present = 1'b0;
		tb_wr_buf_io_present = 1'b0;
	    // fence restart notification to ROB
	    // fence restart notification backpressure from ROB
		tb_fence_restart_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // store set commit update
	    // oldest stamofu advertisement
	    // stamofu mq complete notif
		tb_stamofu_mq_complete_valid = 1'b0;
		tb_stamofu_mq_complete_cq_index = 'h0;
	    // ROB complete notif
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_ROB_index = 7'h00;
	    // ROB commit
		tb_rob_commit_upper_index = 5'h00;
		tb_rob_commit_lower_index_valid_mask = 4'b0000;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to central queue
	    // central queue enqueue feedback
		expected_stamofu_cq_enq_ready = 1'b1;
		expected_stamofu_cq_enq_index = 'h0;
	    // central queue info grab
		expected_stamofu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_stamofu_cq_info_grab_bank0_mem_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank0_io_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank0_mem_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank0_io_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank0_ROB_index = 7'h00;
		expected_stamofu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_stamofu_cq_info_grab_bank1_mem_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank1_io_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank1_mem_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank1_io_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // ldu CAM launch
		expected_ldu_CAM_launch_valid = 1'b0;
		expected_ldu_CAM_launch_cq_index = 'h0;
		expected_ldu_CAM_launch_is_mq = 1'b0;
		expected_ldu_CAM_launch_mq_index = 'h0;
		expected_ldu_CAM_launch_is_amo = 1'b0;
		expected_ldu_CAM_launch_PA_word = 32'h00000000;
		expected_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_ldu_CAM_launch_write_data = 32'h00000000;
		expected_ldu_CAM_launch_mdp_info = 8'b00000000;
		expected_ldu_CAM_launch_ROB_index = 7'h00;
	    // ldu CAM launch feedback
	    // ldu CAM return
	    // stamofu CAM launch
	    // stamofu_mq CAM stage 2 info
	    // stamofu CAM return
		expected_stamofu_CAM_return_bank0_valid = 1'b0;
		expected_stamofu_CAM_return_bank0_cq_index = 'h0;
		expected_stamofu_CAM_return_bank0_is_mq = 1'b0;
		expected_stamofu_CAM_return_bank0_mq_index = 'h0;
		expected_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		expected_stamofu_CAM_return_bank0_stall = 1'b0;
		expected_stamofu_CAM_return_bank0_stall_count = 'h0;
		expected_stamofu_CAM_return_bank0_forward = 1'b0;
		expected_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		expected_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		expected_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		expected_stamofu_CAM_return_bank1_valid = 1'b0;
		expected_stamofu_CAM_return_bank1_cq_index = 'h0;
		expected_stamofu_CAM_return_bank1_is_mq = 1'b0;
		expected_stamofu_CAM_return_bank1_mq_index = 'h0;
		expected_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		expected_stamofu_CAM_return_bank1_stall = 1'b0;
		expected_stamofu_CAM_return_bank1_stall_count = 'h0;
		expected_stamofu_CAM_return_bank1_forward = 1'b0;
		expected_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		expected_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		expected_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
	    // misaligned queue info grab
		expected_stamofu_mq_info_grab_mq_index = 'h0;
		expected_stamofu_mq_info_grab_clear_entry = 1'b0;
	    // write buffer enq
		expected_wr_buf_enq_valid = 1'b0;
		expected_wr_buf_enq_is_amo = 1'b0;
		expected_wr_buf_enq_op = 4'b0000;
		expected_wr_buf_enq_is_mem = 1'b0;
		expected_wr_buf_enq_PA_word = 32'h00000000;
		expected_wr_buf_enq_byte_mask = 4'b0000;
		expected_wr_buf_enq_data = 32'h00000000;
	    // write buffer enq feedback
	    // fence restart notification to ROB
		expected_fence_restart_notif_valid = 1'b0;
		expected_fence_restart_notif_ROB_index = 7'h00;
	    // fence restart notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_is_lr = 1'b0;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_misaligned_exception = 1'b0;
		expected_rob_exception_ROB_index = 7'h00;
	    // exception backpressure from ROB
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		expected_stamofu_active = 1'b0;
		expected_stamofu_oldest_ROB_index = 7'h00;
	    // stamofu mq complete notif
	    // ROB complete notif
		expected_stamofu_complete_valid = 1'b0;
		expected_stamofu_complete_ROB_index = 7'h00;
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_valid = 1'b0;
	    // ROB commit
	    // ROB kill

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "default";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_stamofu_cq_enq_valid = 1'b0;
		tb_stamofu_cq_enq_killed = 1'b0;
		tb_stamofu_cq_enq_is_store = 1'b0;
		tb_stamofu_cq_enq_is_amo = 1'b0;
		tb_stamofu_cq_enq_is_fence = 1'b0;
		tb_stamofu_cq_enq_op = 4'b0000;
		tb_stamofu_cq_enq_mdp_info = 8'b00000000;
		tb_stamofu_cq_enq_mem_aq = 1'b0;
		tb_stamofu_cq_enq_io_aq = 1'b0;
		tb_stamofu_cq_enq_mem_rl = 1'b0;
		tb_stamofu_cq_enq_io_rl = 1'b0;
		tb_stamofu_cq_enq_dest_PR = 7'h00;
		tb_stamofu_cq_enq_ROB_index = 7'h00;
	    // central queue enqueue feedback
	    // central queue info grab
		tb_stamofu_cq_info_grab_bank0_cq_index = 'h0;
		tb_stamofu_cq_info_grab_bank1_cq_index = 'h0;
	    // central queue info ret
		tb_stamofu_cq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_cq_info_ret_bank0_cq_index = 'h0;
		tb_stamofu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_stamofu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_stamofu_cq_info_ret_bank0_mem_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank0_io_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank0_mem_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank0_io_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_stamofu_cq_info_ret_bank0_misaligned_exception = 1'b0;
		tb_stamofu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_stamofu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_stamofu_cq_info_ret_bank0_data = 32'h00000000;
		tb_stamofu_cq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_cq_info_ret_bank1_cq_index = 'h0;
		tb_stamofu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_stamofu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_stamofu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_stamofu_cq_info_ret_bank1_mem_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank1_io_aq = 1'b0;
		tb_stamofu_cq_info_ret_bank1_mem_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank1_io_rl = 1'b0;
		tb_stamofu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_stamofu_cq_info_ret_bank1_misaligned_exception = 1'b0;
		tb_stamofu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_stamofu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_stamofu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_stamofu_mq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank0_cq_index = 'h0;
		tb_stamofu_mq_info_ret_bank0_mq_index = 'h0;
		tb_stamofu_mq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank1_cq_index = 'h0;
		tb_stamofu_mq_info_ret_bank1_mq_index = 'h0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_cq_index = 'h0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 'h0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // ldu CAM launch
	    // ldu CAM launch feedback
		tb_ldu_CAM_launch_ready = 1'b0;
	    // ldu CAM return
		tb_ldu_CAM_return_valid = 1'b0;
		tb_ldu_CAM_return_cq_index = 'h0;
		tb_ldu_CAM_return_is_mq = 1'b0;
		tb_ldu_CAM_return_mq_index = 'h0;
		tb_ldu_CAM_return_forward = 1'b0;
	    // stamofu CAM launch
		tb_stamofu_CAM_launch_bank0_valid = 1'b0;
		tb_stamofu_CAM_launch_bank0_cq_index = 'h0;
		tb_stamofu_CAM_launch_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_launch_bank0_mq_index = 'h0;
		tb_stamofu_CAM_launch_bank0_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank0_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank0_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank0_mdp_info = 8'b00000000;
		tb_stamofu_CAM_launch_bank1_valid = 1'b0;
		tb_stamofu_CAM_launch_bank1_cq_index = 'h0;
		tb_stamofu_CAM_launch_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_launch_bank1_mq_index = 'h0;
		tb_stamofu_CAM_launch_bank1_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank1_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank1_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank1_mdp_info = 8'b00000000;
	    // stamofu_mq CAM stage 2 info
		tb_stamofu_mq_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_mq_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_stall_count = 'h0;
		tb_stamofu_mq_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_mq_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_mq_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_mq_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_stall_count = 'h0;
		tb_stamofu_mq_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_mq_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_mq_CAM_return_bank1_forward_data = 32'h00000000;
	    // stamofu CAM return
	    // misaligned queue info grab
		tb_stamofu_mq_info_grab_is_mem = 1'b0;
		tb_stamofu_mq_info_grab_PA_word = 32'h00000000;
		tb_stamofu_mq_info_grab_byte_mask = 4'b0000;
		tb_stamofu_mq_info_grab_data = 32'h00000000;
	    // write buffer enq
	    // write buffer enq feedback
		tb_wr_buf_ready = 1'b1;
		tb_wr_buf_mem_present = 1'b0;
		tb_wr_buf_io_present = 1'b0;
	    // fence restart notification to ROB
	    // fence restart notification backpressure from ROB
		tb_fence_restart_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // store set commit update
	    // oldest stamofu advertisement
	    // stamofu mq complete notif
		tb_stamofu_mq_complete_valid = 1'b0;
		tb_stamofu_mq_complete_cq_index = 'h0;
	    // ROB complete notif
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_ROB_index = 7'h00;
	    // ROB commit
		tb_rob_commit_upper_index = 5'h00;
		tb_rob_commit_lower_index_valid_mask = 4'b0000;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(negedge CLK);

		// outputs:

	    // op enqueue to central queue
	    // central queue enqueue feedback
		expected_stamofu_cq_enq_ready = 1'b1;
		expected_stamofu_cq_enq_index = 'h0;
	    // central queue info grab
		expected_stamofu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_stamofu_cq_info_grab_bank0_mem_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank0_io_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank0_mem_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank0_io_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank0_ROB_index = 7'h00;
		expected_stamofu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_stamofu_cq_info_grab_bank1_mem_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank1_io_aq = 1'b0;
		expected_stamofu_cq_info_grab_bank1_mem_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank1_io_rl = 1'b0;
		expected_stamofu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // ldu CAM launch
		expected_ldu_CAM_launch_valid = 1'b0;
		expected_ldu_CAM_launch_cq_index = 'h0;
		expected_ldu_CAM_launch_is_mq = 1'b0;
		expected_ldu_CAM_launch_mq_index = 'h0;
		expected_ldu_CAM_launch_is_amo = 1'b0;
		expected_ldu_CAM_launch_PA_word = 32'h00000000;
		expected_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_ldu_CAM_launch_write_data = 32'h00000000;
		expected_ldu_CAM_launch_mdp_info = 8'b00000000;
		expected_ldu_CAM_launch_ROB_index = 7'h00;
	    // ldu CAM launch feedback
	    // ldu CAM return
	    // stamofu CAM launch
	    // stamofu_mq CAM stage 2 info
	    // stamofu CAM return
		expected_stamofu_CAM_return_bank0_valid = 1'b0;
		expected_stamofu_CAM_return_bank0_cq_index = 'h0;
		expected_stamofu_CAM_return_bank0_is_mq = 1'b0;
		expected_stamofu_CAM_return_bank0_mq_index = 'h0;
		expected_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		expected_stamofu_CAM_return_bank0_stall = 1'b0;
		expected_stamofu_CAM_return_bank0_stall_count = 'h0;
		expected_stamofu_CAM_return_bank0_forward = 1'b0;
		expected_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		expected_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		expected_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		expected_stamofu_CAM_return_bank1_valid = 1'b0;
		expected_stamofu_CAM_return_bank1_cq_index = 'h0;
		expected_stamofu_CAM_return_bank1_is_mq = 1'b0;
		expected_stamofu_CAM_return_bank1_mq_index = 'h0;
		expected_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		expected_stamofu_CAM_return_bank1_stall = 1'b0;
		expected_stamofu_CAM_return_bank1_stall_count = 'h0;
		expected_stamofu_CAM_return_bank1_forward = 1'b0;
		expected_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		expected_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		expected_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
	    // misaligned queue info grab
		expected_stamofu_mq_info_grab_mq_index = 'h0;
		expected_stamofu_mq_info_grab_clear_entry = 1'b0;
	    // write buffer enq
		expected_wr_buf_enq_valid = 1'b0;
		expected_wr_buf_enq_is_amo = 1'b0;
		expected_wr_buf_enq_op = 4'b0000;
		expected_wr_buf_enq_is_mem = 1'b0;
		expected_wr_buf_enq_PA_word = 32'h00000000;
		expected_wr_buf_enq_byte_mask = 4'b0000;
		expected_wr_buf_enq_data = 32'h00000000;
	    // write buffer enq feedback
	    // fence restart notification to ROB
		expected_fence_restart_notif_valid = 1'b0;
		expected_fence_restart_notif_ROB_index = 7'h00;
	    // fence restart notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_is_lr = 1'b0;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_misaligned_exception = 1'b0;
		expected_rob_exception_ROB_index = 7'h00;
	    // exception backpressure from ROB
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		expected_stamofu_active = 1'b0;
		expected_stamofu_oldest_ROB_index = 7'h00;
	    // stamofu mq complete notif
	    // ROB complete notif
		expected_stamofu_complete_valid = 1'b0;
		expected_stamofu_complete_ROB_index = 7'h00;
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_valid = 1'b0;
	    // ROB commit
	    // ROB kill

		check_outputs();

        // ------------------------------------------------------------
        // finish:
        @(posedge CLK); #(PERIOD/10);
        
        test_case = "finish";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        $display();
        if (num_errors) begin
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule