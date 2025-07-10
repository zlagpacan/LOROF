/*
    Filename: ldu_cq_tb.sv
    Author: zlagpacan
    Description: Testbench for ldu_cq module. 
    Spec: LOROF/spec/design/ldu_cq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter LDU_CQ_ENTRIES = 10;
parameter LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES);

module ldu_cq_tb ();

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
	logic tb_ldu_cq_enq_valid;
	logic tb_ldu_cq_enq_killed;
	logic [3:0] tb_ldu_cq_enq_op;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_cq_enq_mdp_info;
	logic [LOG_PR_COUNT-1:0] tb_ldu_cq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_cq_enq_ROB_index;

    // second try
	logic DUT_second_try_bank0_valid, expected_second_try_bank0_valid;
	logic DUT_second_try_bank1_valid, expected_second_try_bank1_valid;

	logic DUT_second_try_do_mispred, expected_second_try_do_mispred;
	logic DUT_second_try_is_mq, expected_second_try_is_mq;
	logic DUT_second_try_misaligned, expected_second_try_misaligned;
	logic DUT_second_try_page_fault, expected_second_try_page_fault;
	logic DUT_second_try_access_fault, expected_second_try_access_fault;
	logic DUT_second_try_is_mem, expected_second_try_is_mem;
	logic [PPN_WIDTH-1:0] DUT_second_try_PPN, expected_second_try_PPN;
	logic [PO_WIDTH-3:0] DUT_second_try_PO_word, expected_second_try_PO_word;
	logic [3:0] DUT_second_try_byte_mask, expected_second_try_byte_mask;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_second_try_cq_index, expected_second_try_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_second_try_mq_index, expected_second_try_mq_index;

    // second try feedback
	logic tb_second_try_bank0_ack;
	logic tb_second_try_bank1_ack;

    // data try
	logic DUT_data_try_bank0_valid, expected_data_try_bank0_valid;
	logic DUT_data_try_bank1_valid, expected_data_try_bank1_valid;

	logic DUT_data_try_do_mispred, expected_data_try_do_mispred;
	logic [31:0] DUT_data_try_data, expected_data_try_data;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_data_try_cq_index, expected_data_try_cq_index;

    // data try feedback
	logic tb_data_try_bank0_ack;
	logic tb_data_try_bank1_ack;

    // misaligned queue data try req
	logic tb_ldu_mq_data_try_req_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_mq_data_try_cq_index;

    // misaligned queue info grab
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_ldu_mq_info_grab_mq_index, expected_ldu_mq_info_grab_mq_index;
	logic DUT_ldu_mq_info_grab_data_try_ack, expected_ldu_mq_info_grab_data_try_ack;
	logic tb_ldu_mq_info_grab_data_try_req;
	logic [31:0] tb_ldu_mq_info_grab_data;

    // central queue info grab
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_cq_info_grab_bank0_cq_index;
	logic [3:0] DUT_ldu_cq_info_grab_bank0_op, expected_ldu_cq_info_grab_bank0_op;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ldu_cq_info_grab_bank0_mdp_info, expected_ldu_cq_info_grab_bank0_mdp_info;
	logic [LOG_PR_COUNT-1:0] DUT_ldu_cq_info_grab_bank0_dest_PR, expected_ldu_cq_info_grab_bank0_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ldu_cq_info_grab_bank0_ROB_index, expected_ldu_cq_info_grab_bank0_ROB_index;

	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_cq_info_grab_bank1_cq_index;
	logic [3:0] DUT_ldu_cq_info_grab_bank1_op, expected_ldu_cq_info_grab_bank1_op;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ldu_cq_info_grab_bank1_mdp_info, expected_ldu_cq_info_grab_bank1_mdp_info;
	logic [LOG_PR_COUNT-1:0] DUT_ldu_cq_info_grab_bank1_dest_PR, expected_ldu_cq_info_grab_bank1_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ldu_cq_info_grab_bank1_ROB_index, expected_ldu_cq_info_grab_bank1_ROB_index;

    // central queue info ret
	logic tb_ldu_cq_info_ret_bank0_valid;
	logic tb_ldu_cq_info_ret_bank0_WB_sent;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_cq_info_ret_bank0_cq_index;
	logic tb_ldu_cq_info_ret_bank0_misaligned;
	logic tb_ldu_cq_info_ret_bank0_dtlb_hit;
	logic tb_ldu_cq_info_ret_bank0_page_fault;
	logic tb_ldu_cq_info_ret_bank0_access_fault;
	logic tb_ldu_cq_info_ret_bank0_dcache_hit;
	logic tb_ldu_cq_info_ret_bank0_is_mem;
	logic tb_ldu_cq_info_ret_bank0_aq_blocking;
	logic [PA_WIDTH-2-1:0] tb_ldu_cq_info_ret_bank0_PA_word;
	logic [3:0] tb_ldu_cq_info_ret_bank0_byte_mask;
	logic [31:0] tb_ldu_cq_info_ret_bank0_data;

	logic tb_ldu_cq_info_ret_bank1_valid;
	logic tb_ldu_cq_info_ret_bank1_WB_sent;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_cq_info_ret_bank1_cq_index;
	logic tb_ldu_cq_info_ret_bank1_misaligned;
	logic tb_ldu_cq_info_ret_bank1_dtlb_hit;
	logic tb_ldu_cq_info_ret_bank1_page_fault;
	logic tb_ldu_cq_info_ret_bank1_access_fault;
	logic tb_ldu_cq_info_ret_bank1_dcache_hit;
	logic tb_ldu_cq_info_ret_bank1_is_mem;
	logic tb_ldu_cq_info_ret_bank1_aq_blocking;
	logic [PA_WIDTH-2-1:0] tb_ldu_cq_info_ret_bank1_PA_word;
	logic [3:0] tb_ldu_cq_info_ret_bank1_byte_mask;
	logic [31:0] tb_ldu_cq_info_ret_bank1_data;

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
        // use cq_index ^
	logic tb_ldu_mq_info_ret_bank0_valid;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_ldu_mq_info_ret_bank0_mq_index;

	logic tb_ldu_mq_info_ret_bank1_valid;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_ldu_mq_info_ret_bank1_mq_index;

    // dtlb miss resp
	logic tb_dtlb_miss_resp_valid;
	logic tb_dtlb_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_dtlb_miss_resp_mq_index;
	logic [PPN_WIDTH-1:0] tb_dtlb_miss_resp_PPN;
	logic tb_dtlb_miss_resp_is_mem;
	logic tb_dtlb_miss_resp_page_fault;
	logic tb_dtlb_miss_resp_access_fault;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_dtlb_miss_resp_cq_index;

    // dcache miss resp
	logic tb_dcache_miss_resp_valid;
	logic tb_dcache_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_dcache_miss_resp_mq_index;
	logic [31:0] tb_dcache_miss_resp_data;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_dcache_miss_resp_cq_index;

    // stamofu CAM return
	logic tb_stamofu_CAM_return_bank0_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_CAM_return_bank0_updated_mdp_info;
	logic tb_stamofu_CAM_return_bank0_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank0_stall_count;
	logic [3:0] tb_stamofu_CAM_return_bank0_forward;
	logic tb_stamofu_CAM_return_bank0_nasty_forward;
	logic tb_stamofu_CAM_return_bank0_forward_ROB_index;
	logic [31:0] tb_stamofu_CAM_return_bank0_forward_data;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank0_cq_index;
	logic tb_stamofu_CAM_return_bank0_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank0_mq_index;

	logic tb_stamofu_CAM_return_bank1_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_CAM_return_bank1_updated_mdp_info;
	logic tb_stamofu_CAM_return_bank1_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank1_stall_count;
	logic [3:0] tb_stamofu_CAM_return_bank1_forward;
	logic tb_stamofu_CAM_return_bank1_nasty_forward;
	logic tb_stamofu_CAM_return_bank1_forward_ROB_index;
	logic [31:0] tb_stamofu_CAM_return_bank1_forward_data;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank1_cq_index;
	logic tb_stamofu_CAM_return_bank1_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank1_mq_index;

    // ldu CAM launch
	logic tb_ldu_CAM_launch_valid;
	logic tb_ldu_CAM_launch_is_amo;
	logic [PA_WIDTH-2-1:0] tb_ldu_CAM_launch_PA_word;
	logic [3:0] tb_ldu_CAM_launch_byte_mask;
	logic [31:0] tb_ldu_CAM_launch_write_data;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_CAM_launch_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_CAM_launch_ROB_index;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_ldu_CAM_launch_cq_index;
	logic tb_ldu_CAM_launch_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_ldu_CAM_launch_mq_index;

    // ldu CAM return
	logic DUT_ldu_CAM_return_valid, expected_ldu_CAM_return_valid;
	logic DUT_ldu_CAM_return_forward, expected_ldu_CAM_return_forward;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_ldu_CAM_return_cq_index, expected_ldu_CAM_return_cq_index;
	logic DUT_ldu_CAM_return_is_mq, expected_ldu_CAM_return_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] DUT_ldu_CAM_return_mq_index, expected_ldu_CAM_return_mq_index;

    // store set CAM update
        // implied dep
	logic DUT_ssu_CAM_update_valid, expected_ssu_CAM_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ssu_CAM_update_ld_mdp_info, expected_ssu_CAM_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ssu_CAM_update_ld_ROB_index, expected_ssu_CAM_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ssu_CAM_update_stamo_mdp_info, expected_ssu_CAM_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ssu_CAM_update_stamo_ROB_index, expected_ssu_CAM_update_stamo_ROB_index;

    // store set commit update
        // implied no dep
	logic DUT_ssu_commit_update_valid, expected_ssu_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ssu_commit_update_mdp_info, expected_ssu_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ssu_commit_update_ROB_index, expected_ssu_commit_update_ROB_index;

    // acquire advertisement
	logic tb_stamofu_aq_mem_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_mem_aq_oldest_abs_ROB_index;
	logic tb_stamofu_aq_io_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_io_aq_oldest_abs_ROB_index;

    // oldest stamofu advertisement
	logic tb_stamofu_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_oldest_ROB_index;

    // ROB complete notif
	logic DUT_ldu_complete_valid, expected_ldu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ldu_complete_ROB_index, expected_ldu_complete_ROB_index;

    // ROB commit
	logic [LOG_ROB_ENTRIES-3:0] tb_rob_commit_upper_index;
	logic [3:0] tb_rob_commit_lower_index_valid_mask;

    // ROB kill
	logic tb_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ldu_cq #(
		.LDU_CQ_ENTRIES(LDU_CQ_ENTRIES),
		.LOG_LDU_CQ_ENTRIES(LOG_LDU_CQ_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to central queue
		.ldu_cq_enq_valid(tb_ldu_cq_enq_valid),
		.ldu_cq_enq_killed(tb_ldu_cq_enq_killed),
		.ldu_cq_enq_op(tb_ldu_cq_enq_op),
		.ldu_cq_enq_mdp_info(tb_ldu_cq_enq_mdp_info),
		.ldu_cq_enq_dest_PR(tb_ldu_cq_enq_dest_PR),
		.ldu_cq_enq_ROB_index(tb_ldu_cq_enq_ROB_index),

	    // second try
		.second_try_bank0_valid(DUT_second_try_bank0_valid),
		.second_try_bank1_valid(DUT_second_try_bank1_valid),

		.second_try_do_mispred(DUT_second_try_do_mispred),
		.second_try_is_mq(DUT_second_try_is_mq),
		.second_try_misaligned(DUT_second_try_misaligned),
		.second_try_page_fault(DUT_second_try_page_fault),
		.second_try_access_fault(DUT_second_try_access_fault),
		.second_try_is_mem(DUT_second_try_is_mem),
		.second_try_PPN(DUT_second_try_PPN),
		.second_try_PO_word(DUT_second_try_PO_word),
		.second_try_byte_mask(DUT_second_try_byte_mask),
		.second_try_cq_index(DUT_second_try_cq_index),
		.second_try_mq_index(DUT_second_try_mq_index),

	    // second try feedback
		.second_try_bank0_ack(tb_second_try_bank0_ack),
		.second_try_bank1_ack(tb_second_try_bank1_ack),

	    // data try
		.data_try_bank0_valid(DUT_data_try_bank0_valid),
		.data_try_bank1_valid(DUT_data_try_bank1_valid),

		.data_try_do_mispred(DUT_data_try_do_mispred),
		.data_try_data(DUT_data_try_data),
		.data_try_cq_index(DUT_data_try_cq_index),

	    // data try feedback
		.data_try_bank0_ack(tb_data_try_bank0_ack),
		.data_try_bank1_ack(tb_data_try_bank1_ack),

	    // misaligned queue data try req
		.ldu_mq_data_try_req_valid(tb_ldu_mq_data_try_req_valid),
		.ldu_mq_data_try_cq_index(tb_ldu_mq_data_try_cq_index),

	    // misaligned queue info grab
		.ldu_mq_info_grab_mq_index(DUT_ldu_mq_info_grab_mq_index),
		.ldu_mq_info_grab_data_try_ack(DUT_ldu_mq_info_grab_data_try_ack),
		.ldu_mq_info_grab_data_try_req(tb_ldu_mq_info_grab_data_try_req),
		.ldu_mq_info_grab_data(tb_ldu_mq_info_grab_data),

	    // central queue info grab
		.ldu_cq_info_grab_bank0_cq_index(tb_ldu_cq_info_grab_bank0_cq_index),
		.ldu_cq_info_grab_bank0_op(DUT_ldu_cq_info_grab_bank0_op),
		.ldu_cq_info_grab_bank0_mdp_info(DUT_ldu_cq_info_grab_bank0_mdp_info),
		.ldu_cq_info_grab_bank0_dest_PR(DUT_ldu_cq_info_grab_bank0_dest_PR),
		.ldu_cq_info_grab_bank0_ROB_index(DUT_ldu_cq_info_grab_bank0_ROB_index),

		.ldu_cq_info_grab_bank1_cq_index(tb_ldu_cq_info_grab_bank1_cq_index),
		.ldu_cq_info_grab_bank1_op(DUT_ldu_cq_info_grab_bank1_op),
		.ldu_cq_info_grab_bank1_mdp_info(DUT_ldu_cq_info_grab_bank1_mdp_info),
		.ldu_cq_info_grab_bank1_dest_PR(DUT_ldu_cq_info_grab_bank1_dest_PR),
		.ldu_cq_info_grab_bank1_ROB_index(DUT_ldu_cq_info_grab_bank1_ROB_index),

	    // central queue info ret
		.ldu_cq_info_ret_bank0_valid(tb_ldu_cq_info_ret_bank0_valid),
		.ldu_cq_info_ret_bank0_WB_sent(tb_ldu_cq_info_ret_bank0_WB_sent),
		.ldu_cq_info_ret_bank0_cq_index(tb_ldu_cq_info_ret_bank0_cq_index),
		.ldu_cq_info_ret_bank0_misaligned(tb_ldu_cq_info_ret_bank0_misaligned),
		.ldu_cq_info_ret_bank0_dtlb_hit(tb_ldu_cq_info_ret_bank0_dtlb_hit),
		.ldu_cq_info_ret_bank0_page_fault(tb_ldu_cq_info_ret_bank0_page_fault),
		.ldu_cq_info_ret_bank0_access_fault(tb_ldu_cq_info_ret_bank0_access_fault),
		.ldu_cq_info_ret_bank0_dcache_hit(tb_ldu_cq_info_ret_bank0_dcache_hit),
		.ldu_cq_info_ret_bank0_is_mem(tb_ldu_cq_info_ret_bank0_is_mem),
		.ldu_cq_info_ret_bank0_aq_blocking(tb_ldu_cq_info_ret_bank0_aq_blocking),
		.ldu_cq_info_ret_bank0_PA_word(tb_ldu_cq_info_ret_bank0_PA_word),
		.ldu_cq_info_ret_bank0_byte_mask(tb_ldu_cq_info_ret_bank0_byte_mask),
		.ldu_cq_info_ret_bank0_data(tb_ldu_cq_info_ret_bank0_data),

		.ldu_cq_info_ret_bank1_valid(tb_ldu_cq_info_ret_bank1_valid),
		.ldu_cq_info_ret_bank1_WB_sent(tb_ldu_cq_info_ret_bank1_WB_sent),
		.ldu_cq_info_ret_bank1_cq_index(tb_ldu_cq_info_ret_bank1_cq_index),
		.ldu_cq_info_ret_bank1_misaligned(tb_ldu_cq_info_ret_bank1_misaligned),
		.ldu_cq_info_ret_bank1_dtlb_hit(tb_ldu_cq_info_ret_bank1_dtlb_hit),
		.ldu_cq_info_ret_bank1_page_fault(tb_ldu_cq_info_ret_bank1_page_fault),
		.ldu_cq_info_ret_bank1_access_fault(tb_ldu_cq_info_ret_bank1_access_fault),
		.ldu_cq_info_ret_bank1_dcache_hit(tb_ldu_cq_info_ret_bank1_dcache_hit),
		.ldu_cq_info_ret_bank1_is_mem(tb_ldu_cq_info_ret_bank1_is_mem),
		.ldu_cq_info_ret_bank1_aq_blocking(tb_ldu_cq_info_ret_bank1_aq_blocking),
		.ldu_cq_info_ret_bank1_PA_word(tb_ldu_cq_info_ret_bank1_PA_word),
		.ldu_cq_info_ret_bank1_byte_mask(tb_ldu_cq_info_ret_bank1_byte_mask),
		.ldu_cq_info_ret_bank1_data(tb_ldu_cq_info_ret_bank1_data),

	    // misaligned queue info ret
	        // need in order to tie cq entry to mq if misaligned
	        // use cq_index ^
		.ldu_mq_info_ret_bank0_valid(tb_ldu_mq_info_ret_bank0_valid),
		.ldu_mq_info_ret_bank0_mq_index(tb_ldu_mq_info_ret_bank0_mq_index),

		.ldu_mq_info_ret_bank1_valid(tb_ldu_mq_info_ret_bank1_valid),
		.ldu_mq_info_ret_bank1_mq_index(tb_ldu_mq_info_ret_bank1_mq_index),

	    // dtlb miss resp
		.dtlb_miss_resp_valid(tb_dtlb_miss_resp_valid),
		.dtlb_miss_resp_is_mq(tb_dtlb_miss_resp_is_mq),
		.dtlb_miss_resp_mq_index(tb_dtlb_miss_resp_mq_index),
		.dtlb_miss_resp_PPN(tb_dtlb_miss_resp_PPN),
		.dtlb_miss_resp_is_mem(tb_dtlb_miss_resp_is_mem),
		.dtlb_miss_resp_page_fault(tb_dtlb_miss_resp_page_fault),
		.dtlb_miss_resp_access_fault(tb_dtlb_miss_resp_access_fault),
		.dtlb_miss_resp_cq_index(tb_dtlb_miss_resp_cq_index),

	    // dcache miss resp
		.dcache_miss_resp_valid(tb_dcache_miss_resp_valid),
		.dcache_miss_resp_is_mq(tb_dcache_miss_resp_is_mq),
		.dcache_miss_resp_mq_index(tb_dcache_miss_resp_mq_index),
		.dcache_miss_resp_data(tb_dcache_miss_resp_data),
		.dcache_miss_resp_cq_index(tb_dcache_miss_resp_cq_index),

	    // stamofu CAM return
		.stamofu_CAM_return_bank0_valid(tb_stamofu_CAM_return_bank0_valid),
		.stamofu_CAM_return_bank0_updated_mdp_info(tb_stamofu_CAM_return_bank0_updated_mdp_info),
		.stamofu_CAM_return_bank0_stall(tb_stamofu_CAM_return_bank0_stall),
		.stamofu_CAM_return_bank0_stall_count(tb_stamofu_CAM_return_bank0_stall_count),
		.stamofu_CAM_return_bank0_forward(tb_stamofu_CAM_return_bank0_forward),
		.stamofu_CAM_return_bank0_nasty_forward(tb_stamofu_CAM_return_bank0_nasty_forward),
		.stamofu_CAM_return_bank0_forward_ROB_index(tb_stamofu_CAM_return_bank0_forward_ROB_index),
		.stamofu_CAM_return_bank0_forward_data(tb_stamofu_CAM_return_bank0_forward_data),
		.stamofu_CAM_return_bank0_cq_index(tb_stamofu_CAM_return_bank0_cq_index),
		.stamofu_CAM_return_bank0_is_mq(tb_stamofu_CAM_return_bank0_is_mq),
		.stamofu_CAM_return_bank0_mq_index(tb_stamofu_CAM_return_bank0_mq_index),

		.stamofu_CAM_return_bank1_valid(tb_stamofu_CAM_return_bank1_valid),
		.stamofu_CAM_return_bank1_updated_mdp_info(tb_stamofu_CAM_return_bank1_updated_mdp_info),
		.stamofu_CAM_return_bank1_stall(tb_stamofu_CAM_return_bank1_stall),
		.stamofu_CAM_return_bank1_stall_count(tb_stamofu_CAM_return_bank1_stall_count),
		.stamofu_CAM_return_bank1_forward(tb_stamofu_CAM_return_bank1_forward),
		.stamofu_CAM_return_bank1_nasty_forward(tb_stamofu_CAM_return_bank1_nasty_forward),
		.stamofu_CAM_return_bank1_forward_ROB_index(tb_stamofu_CAM_return_bank1_forward_ROB_index),
		.stamofu_CAM_return_bank1_forward_data(tb_stamofu_CAM_return_bank1_forward_data),
		.stamofu_CAM_return_bank1_cq_index(tb_stamofu_CAM_return_bank1_cq_index),
		.stamofu_CAM_return_bank1_is_mq(tb_stamofu_CAM_return_bank1_is_mq),
		.stamofu_CAM_return_bank1_mq_index(tb_stamofu_CAM_return_bank1_mq_index),

	    // ldu CAM launch
		.ldu_CAM_launch_valid(tb_ldu_CAM_launch_valid),
		.ldu_CAM_launch_is_amo(tb_ldu_CAM_launch_is_amo),
		.ldu_CAM_launch_PA_word(tb_ldu_CAM_launch_PA_word),
		.ldu_CAM_launch_byte_mask(tb_ldu_CAM_launch_byte_mask),
		.ldu_CAM_launch_write_data(tb_ldu_CAM_launch_write_data),
		.ldu_CAM_launch_mdp_info(tb_ldu_CAM_launch_mdp_info),
		.ldu_CAM_launch_ROB_index(tb_ldu_CAM_launch_ROB_index),
		.ldu_CAM_launch_cq_index(tb_ldu_CAM_launch_cq_index),
		.ldu_CAM_launch_is_mq(tb_ldu_CAM_launch_is_mq),
		.ldu_CAM_launch_mq_index(tb_ldu_CAM_launch_mq_index),

	    // ldu CAM return
		.ldu_CAM_return_valid(DUT_ldu_CAM_return_valid),
		.ldu_CAM_return_forward(DUT_ldu_CAM_return_forward),
		.ldu_CAM_return_cq_index(DUT_ldu_CAM_return_cq_index),
		.ldu_CAM_return_is_mq(DUT_ldu_CAM_return_is_mq),
		.ldu_CAM_return_mq_index(DUT_ldu_CAM_return_mq_index),

	    // store set CAM update
	        // implied dep
		.ssu_CAM_update_valid(DUT_ssu_CAM_update_valid),
		.ssu_CAM_update_ld_mdp_info(DUT_ssu_CAM_update_ld_mdp_info),
		.ssu_CAM_update_ld_ROB_index(DUT_ssu_CAM_update_ld_ROB_index),
		.ssu_CAM_update_stamo_mdp_info(DUT_ssu_CAM_update_stamo_mdp_info),
		.ssu_CAM_update_stamo_ROB_index(DUT_ssu_CAM_update_stamo_ROB_index),

	    // store set commit update
	        // implied no dep
		.ssu_commit_update_valid(DUT_ssu_commit_update_valid),
		.ssu_commit_update_mdp_info(DUT_ssu_commit_update_mdp_info),
		.ssu_commit_update_ROB_index(DUT_ssu_commit_update_ROB_index),

	    // acquire advertisement
		.stamofu_aq_mem_aq_active(tb_stamofu_aq_mem_aq_active),
		.stamofu_aq_mem_aq_oldest_abs_ROB_index(tb_stamofu_aq_mem_aq_oldest_abs_ROB_index),
		.stamofu_aq_io_aq_active(tb_stamofu_aq_io_aq_active),
		.stamofu_aq_io_aq_oldest_abs_ROB_index(tb_stamofu_aq_io_aq_oldest_abs_ROB_index),

	    // oldest stamofu advertisement
		.stamofu_active(tb_stamofu_active),
		.stamofu_oldest_ROB_index(tb_stamofu_oldest_ROB_index),

	    // ROB complete notif
		.ldu_complete_valid(DUT_ldu_complete_valid),
		.ldu_complete_ROB_index(DUT_ldu_complete_ROB_index),

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
		if (expected_second_try_bank0_valid !== DUT_second_try_bank0_valid) begin
			$display("TB ERROR: expected_second_try_bank0_valid (%h) != DUT_second_try_bank0_valid (%h)",
				expected_second_try_bank0_valid, DUT_second_try_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_bank1_valid !== DUT_second_try_bank1_valid) begin
			$display("TB ERROR: expected_second_try_bank1_valid (%h) != DUT_second_try_bank1_valid (%h)",
				expected_second_try_bank1_valid, DUT_second_try_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_do_mispred !== DUT_second_try_do_mispred) begin
			$display("TB ERROR: expected_second_try_do_mispred (%h) != DUT_second_try_do_mispred (%h)",
				expected_second_try_do_mispred, DUT_second_try_do_mispred);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_is_mq !== DUT_second_try_is_mq) begin
			$display("TB ERROR: expected_second_try_is_mq (%h) != DUT_second_try_is_mq (%h)",
				expected_second_try_is_mq, DUT_second_try_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_misaligned !== DUT_second_try_misaligned) begin
			$display("TB ERROR: expected_second_try_misaligned (%h) != DUT_second_try_misaligned (%h)",
				expected_second_try_misaligned, DUT_second_try_misaligned);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_page_fault !== DUT_second_try_page_fault) begin
			$display("TB ERROR: expected_second_try_page_fault (%h) != DUT_second_try_page_fault (%h)",
				expected_second_try_page_fault, DUT_second_try_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_access_fault !== DUT_second_try_access_fault) begin
			$display("TB ERROR: expected_second_try_access_fault (%h) != DUT_second_try_access_fault (%h)",
				expected_second_try_access_fault, DUT_second_try_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_is_mem !== DUT_second_try_is_mem) begin
			$display("TB ERROR: expected_second_try_is_mem (%h) != DUT_second_try_is_mem (%h)",
				expected_second_try_is_mem, DUT_second_try_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_PPN !== DUT_second_try_PPN) begin
			$display("TB ERROR: expected_second_try_PPN (%h) != DUT_second_try_PPN (%h)",
				expected_second_try_PPN, DUT_second_try_PPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_PO_word !== DUT_second_try_PO_word) begin
			$display("TB ERROR: expected_second_try_PO_word (%h) != DUT_second_try_PO_word (%h)",
				expected_second_try_PO_word, DUT_second_try_PO_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_byte_mask !== DUT_second_try_byte_mask) begin
			$display("TB ERROR: expected_second_try_byte_mask (%h) != DUT_second_try_byte_mask (%h)",
				expected_second_try_byte_mask, DUT_second_try_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_cq_index !== DUT_second_try_cq_index) begin
			$display("TB ERROR: expected_second_try_cq_index (%h) != DUT_second_try_cq_index (%h)",
				expected_second_try_cq_index, DUT_second_try_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_mq_index !== DUT_second_try_mq_index) begin
			$display("TB ERROR: expected_second_try_mq_index (%h) != DUT_second_try_mq_index (%h)",
				expected_second_try_mq_index, DUT_second_try_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_data_try_bank0_valid !== DUT_data_try_bank0_valid) begin
			$display("TB ERROR: expected_data_try_bank0_valid (%h) != DUT_data_try_bank0_valid (%h)",
				expected_data_try_bank0_valid, DUT_data_try_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_data_try_bank1_valid !== DUT_data_try_bank1_valid) begin
			$display("TB ERROR: expected_data_try_bank1_valid (%h) != DUT_data_try_bank1_valid (%h)",
				expected_data_try_bank1_valid, DUT_data_try_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_data_try_do_mispred !== DUT_data_try_do_mispred) begin
			$display("TB ERROR: expected_data_try_do_mispred (%h) != DUT_data_try_do_mispred (%h)",
				expected_data_try_do_mispred, DUT_data_try_do_mispred);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_data_try_data !== DUT_data_try_data) begin
			$display("TB ERROR: expected_data_try_data (%h) != DUT_data_try_data (%h)",
				expected_data_try_data, DUT_data_try_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_data_try_cq_index !== DUT_data_try_cq_index) begin
			$display("TB ERROR: expected_data_try_cq_index (%h) != DUT_data_try_cq_index (%h)",
				expected_data_try_cq_index, DUT_data_try_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_grab_mq_index !== DUT_ldu_mq_info_grab_mq_index) begin
			$display("TB ERROR: expected_ldu_mq_info_grab_mq_index (%h) != DUT_ldu_mq_info_grab_mq_index (%h)",
				expected_ldu_mq_info_grab_mq_index, DUT_ldu_mq_info_grab_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_grab_data_try_ack !== DUT_ldu_mq_info_grab_data_try_ack) begin
			$display("TB ERROR: expected_ldu_mq_info_grab_data_try_ack (%h) != DUT_ldu_mq_info_grab_data_try_ack (%h)",
				expected_ldu_mq_info_grab_data_try_ack, DUT_ldu_mq_info_grab_data_try_ack);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank0_op !== DUT_ldu_cq_info_grab_bank0_op) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank0_op (%h) != DUT_ldu_cq_info_grab_bank0_op (%h)",
				expected_ldu_cq_info_grab_bank0_op, DUT_ldu_cq_info_grab_bank0_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank0_mdp_info !== DUT_ldu_cq_info_grab_bank0_mdp_info) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank0_mdp_info (%h) != DUT_ldu_cq_info_grab_bank0_mdp_info (%h)",
				expected_ldu_cq_info_grab_bank0_mdp_info, DUT_ldu_cq_info_grab_bank0_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank0_dest_PR !== DUT_ldu_cq_info_grab_bank0_dest_PR) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank0_dest_PR (%h) != DUT_ldu_cq_info_grab_bank0_dest_PR (%h)",
				expected_ldu_cq_info_grab_bank0_dest_PR, DUT_ldu_cq_info_grab_bank0_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank0_ROB_index !== DUT_ldu_cq_info_grab_bank0_ROB_index) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank0_ROB_index (%h) != DUT_ldu_cq_info_grab_bank0_ROB_index (%h)",
				expected_ldu_cq_info_grab_bank0_ROB_index, DUT_ldu_cq_info_grab_bank0_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank1_op !== DUT_ldu_cq_info_grab_bank1_op) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank1_op (%h) != DUT_ldu_cq_info_grab_bank1_op (%h)",
				expected_ldu_cq_info_grab_bank1_op, DUT_ldu_cq_info_grab_bank1_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank1_mdp_info !== DUT_ldu_cq_info_grab_bank1_mdp_info) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank1_mdp_info (%h) != DUT_ldu_cq_info_grab_bank1_mdp_info (%h)",
				expected_ldu_cq_info_grab_bank1_mdp_info, DUT_ldu_cq_info_grab_bank1_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank1_dest_PR !== DUT_ldu_cq_info_grab_bank1_dest_PR) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank1_dest_PR (%h) != DUT_ldu_cq_info_grab_bank1_dest_PR (%h)",
				expected_ldu_cq_info_grab_bank1_dest_PR, DUT_ldu_cq_info_grab_bank1_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_bank1_ROB_index !== DUT_ldu_cq_info_grab_bank1_ROB_index) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_bank1_ROB_index (%h) != DUT_ldu_cq_info_grab_bank1_ROB_index (%h)",
				expected_ldu_cq_info_grab_bank1_ROB_index, DUT_ldu_cq_info_grab_bank1_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_return_valid !== DUT_ldu_CAM_return_valid) begin
			$display("TB ERROR: expected_ldu_CAM_return_valid (%h) != DUT_ldu_CAM_return_valid (%h)",
				expected_ldu_CAM_return_valid, DUT_ldu_CAM_return_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_return_forward !== DUT_ldu_CAM_return_forward) begin
			$display("TB ERROR: expected_ldu_CAM_return_forward (%h) != DUT_ldu_CAM_return_forward (%h)",
				expected_ldu_CAM_return_forward, DUT_ldu_CAM_return_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_return_cq_index !== DUT_ldu_CAM_return_cq_index) begin
			$display("TB ERROR: expected_ldu_CAM_return_cq_index (%h) != DUT_ldu_CAM_return_cq_index (%h)",
				expected_ldu_CAM_return_cq_index, DUT_ldu_CAM_return_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_return_is_mq !== DUT_ldu_CAM_return_is_mq) begin
			$display("TB ERROR: expected_ldu_CAM_return_is_mq (%h) != DUT_ldu_CAM_return_is_mq (%h)",
				expected_ldu_CAM_return_is_mq, DUT_ldu_CAM_return_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_return_mq_index !== DUT_ldu_CAM_return_mq_index) begin
			$display("TB ERROR: expected_ldu_CAM_return_mq_index (%h) != DUT_ldu_CAM_return_mq_index (%h)",
				expected_ldu_CAM_return_mq_index, DUT_ldu_CAM_return_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_CAM_update_valid !== DUT_ssu_CAM_update_valid) begin
			$display("TB ERROR: expected_ssu_CAM_update_valid (%h) != DUT_ssu_CAM_update_valid (%h)",
				expected_ssu_CAM_update_valid, DUT_ssu_CAM_update_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_CAM_update_ld_mdp_info !== DUT_ssu_CAM_update_ld_mdp_info) begin
			$display("TB ERROR: expected_ssu_CAM_update_ld_mdp_info (%h) != DUT_ssu_CAM_update_ld_mdp_info (%h)",
				expected_ssu_CAM_update_ld_mdp_info, DUT_ssu_CAM_update_ld_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_CAM_update_ld_ROB_index !== DUT_ssu_CAM_update_ld_ROB_index) begin
			$display("TB ERROR: expected_ssu_CAM_update_ld_ROB_index (%h) != DUT_ssu_CAM_update_ld_ROB_index (%h)",
				expected_ssu_CAM_update_ld_ROB_index, DUT_ssu_CAM_update_ld_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_CAM_update_stamo_mdp_info !== DUT_ssu_CAM_update_stamo_mdp_info) begin
			$display("TB ERROR: expected_ssu_CAM_update_stamo_mdp_info (%h) != DUT_ssu_CAM_update_stamo_mdp_info (%h)",
				expected_ssu_CAM_update_stamo_mdp_info, DUT_ssu_CAM_update_stamo_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_CAM_update_stamo_ROB_index !== DUT_ssu_CAM_update_stamo_ROB_index) begin
			$display("TB ERROR: expected_ssu_CAM_update_stamo_ROB_index (%h) != DUT_ssu_CAM_update_stamo_ROB_index (%h)",
				expected_ssu_CAM_update_stamo_ROB_index, DUT_ssu_CAM_update_stamo_ROB_index);
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

		if (expected_ldu_complete_valid !== DUT_ldu_complete_valid) begin
			$display("TB ERROR: expected_ldu_complete_valid (%h) != DUT_ldu_complete_valid (%h)",
				expected_ldu_complete_valid, DUT_ldu_complete_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_complete_ROB_index !== DUT_ldu_complete_ROB_index) begin
			$display("TB ERROR: expected_ldu_complete_ROB_index (%h) != DUT_ldu_complete_ROB_index (%h)",
				expected_ldu_complete_ROB_index, DUT_ldu_complete_ROB_index);
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
		tb_ldu_cq_enq_valid = 1'b0;
		tb_ldu_cq_enq_killed = 1'b0;
		tb_ldu_cq_enq_op = 4'b0000;
		tb_ldu_cq_enq_mdp_info = 8'b00000000;
		tb_ldu_cq_enq_dest_PR = 7'h00;
		tb_ldu_cq_enq_ROB_index = 7'h00;
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;

		tb_second_try_bank1_ack = 1'b0;
	    // data try
	    // data try feedback
		tb_data_try_bank0_ack = 1'b0;

		tb_data_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
		tb_ldu_mq_data_try_req_valid = 1'b0;
		tb_ldu_mq_data_try_cq_index = 0;
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_data_try_req = 1'b0;
		tb_ldu_mq_info_grab_data = 32'h00000000;
	    // central queue info grab
		tb_ldu_cq_info_grab_bank0_cq_index = 0;

		tb_ldu_cq_info_grab_bank1_cq_index = 0;
	    // central queue info ret
		tb_ldu_cq_info_ret_bank0_valid = 1'b0;
		tb_ldu_cq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank0_cq_index = 0;
		tb_ldu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank0_data = 32'h00000000;

		tb_ldu_cq_info_ret_bank1_valid = 1'b0;
		tb_ldu_cq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank1_cq_index = 0;
		tb_ldu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_mq_index = 0;

		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_mq_index = 0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
		tb_dcache_miss_resp_cq_index = 0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank0_cq_index = 0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_mq_index = 0;

		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank1_cq_index = 0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_mq_index = 0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h00000000;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h00000000;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h00;
		tb_ldu_CAM_launch_cq_index = 0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 0;
	    // ldu CAM return
	    // store set CAM update
	    // store set commit update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h00;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h00;
	    // ROB complete notif
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
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b0;
		expected_second_try_misaligned = 1'b0;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 22'h000000;
		expected_second_try_PO_word = 10'h000;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 0;
		expected_second_try_mq_index = 0;
	    // second try feedback
	    // data try
		expected_data_try_bank0_valid = 1'b0;
		expected_data_try_bank1_valid = 1'b0;
		expected_data_try_do_mispred = 1'b0;
		expected_data_try_data = 32'h00000000;
		expected_data_try_cq_index = 0;
	    // data try feedback
	    // misaligned queue data try req
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_mq_index = 0;
		expected_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // central queue info grab
		expected_ldu_cq_info_grab_bank0_op = 4'b0000;
		expected_ldu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank0_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank0_ROB_index = 7'h00;

		expected_ldu_cq_info_grab_bank1_op = 4'b0000;
		expected_ldu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank1_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_valid = 1'b0;
		expected_ldu_CAM_return_forward = 1'b0;
		expected_ldu_CAM_return_cq_index = 0;
		expected_ldu_CAM_return_is_mq = 1'b0;
		expected_ldu_CAM_return_mq_index = 0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h00;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h00;
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB complete notif
		expected_ldu_complete_valid = 1'b0;
		expected_ldu_complete_ROB_index = 7'h00;
	    // ROB commit
	    // ROB kill

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_ldu_cq_enq_valid = 1'b0;
		tb_ldu_cq_enq_killed = 1'b0;
		tb_ldu_cq_enq_op = 4'b0000;
		tb_ldu_cq_enq_mdp_info = 8'b00000000;
		tb_ldu_cq_enq_dest_PR = 7'h00;
		tb_ldu_cq_enq_ROB_index = 7'h00;
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;

		tb_second_try_bank1_ack = 1'b0;
	    // data try
	    // data try feedback
		tb_data_try_bank0_ack = 1'b0;

		tb_data_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
		tb_ldu_mq_data_try_req_valid = 1'b0;
		tb_ldu_mq_data_try_cq_index = 0;
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_data_try_req = 1'b0;
		tb_ldu_mq_info_grab_data = 32'h00000000;
	    // central queue info grab
		tb_ldu_cq_info_grab_bank0_cq_index = 0;

		tb_ldu_cq_info_grab_bank1_cq_index = 0;
	    // central queue info ret
		tb_ldu_cq_info_ret_bank0_valid = 1'b0;
		tb_ldu_cq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank0_cq_index = 0;
		tb_ldu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank0_data = 32'h00000000;

		tb_ldu_cq_info_ret_bank1_valid = 1'b0;
		tb_ldu_cq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank1_cq_index = 0;
		tb_ldu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_mq_index = 0;

		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_mq_index = 0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
		tb_dcache_miss_resp_cq_index = 0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank0_cq_index = 0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_mq_index = 0;

		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank1_cq_index = 0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_mq_index = 0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h00000000;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h00000000;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h00;
		tb_ldu_CAM_launch_cq_index = 0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 0;
	    // ldu CAM return
	    // store set CAM update
	    // store set commit update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h00;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h00;
	    // ROB complete notif
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
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b0;
		expected_second_try_misaligned = 1'b0;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 22'h000000;
		expected_second_try_PO_word = 10'h000;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 0;
		expected_second_try_mq_index = 0;
	    // second try feedback
	    // data try
		expected_data_try_bank0_valid = 1'b0;
		expected_data_try_bank1_valid = 1'b0;
		expected_data_try_do_mispred = 1'b0;
		expected_data_try_data = 32'h00000000;
		expected_data_try_cq_index = 0;
	    // data try feedback
	    // misaligned queue data try req
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_mq_index = 0;
		expected_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // central queue info grab
		expected_ldu_cq_info_grab_bank0_op = 4'b0000;
		expected_ldu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank0_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank0_ROB_index = 7'h00;

		expected_ldu_cq_info_grab_bank1_op = 4'b0000;
		expected_ldu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank1_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_valid = 1'b0;
		expected_ldu_CAM_return_forward = 1'b0;
		expected_ldu_CAM_return_cq_index = 0;
		expected_ldu_CAM_return_is_mq = 1'b0;
		expected_ldu_CAM_return_mq_index = 0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h00;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h00;
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB complete notif
		expected_ldu_complete_valid = 1'b0;
		expected_ldu_complete_ROB_index = 7'h00;
	    // ROB commit
	    // ROB kill

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tcq enq: i",
			"\n\t\tmq data try: i",
			"\n\t\tmq info grab: i",
			"\n\t\tcq info grab bank0: i",
			"\n\t\tcq info grab bank1: i",
			"\n\t\tcq info ret bank0: i",
			"\n\t\tcq info ret bank1: i",
			"\n\t\tmq info ret bank0: i",
			"\n\t\tmq info ret bank1: i",
			"\n\t\tdtlb miss resp: i",
			"\n\t\tdcache miss resp: i",
			"\n\t\tstamofu CAM ret: i",
			"\n\t\tldu CAM launch: i",
			"\n\t\taq adv: i",
			"\n\t\tstamofu adv: i",
			"\n\t\tROB commit: i",
			"\n\t\tROB kill: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "9: i",
			"\n\t\t\t", "8: i",
			"\n\t\t\t", "7: i",
			"\n\t\t\t", "6: i",
			"\n\t\t\t", "5: i",
			"\n\t\t\t", "4: i",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tsecond try: i",
			"\n\t\tdata try: i",
			"\n\t\tldu CAM ret: i",
			"\n\t\tssu CAM update: i",
			"\n\t\tssu commit update: i",
			"\n\t\tROB complete: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_ldu_cq_enq_valid = 1'b0;
		tb_ldu_cq_enq_killed = 1'b0;
		tb_ldu_cq_enq_op = 4'b0000;
		tb_ldu_cq_enq_mdp_info = 8'b00000000;
		tb_ldu_cq_enq_dest_PR = 7'h00;
		tb_ldu_cq_enq_ROB_index = 7'h00;
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;

		tb_second_try_bank1_ack = 1'b0;
	    // data try
	    // data try feedback
		tb_data_try_bank0_ack = 1'b0;

		tb_data_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
		tb_ldu_mq_data_try_req_valid = 1'b0;
		tb_ldu_mq_data_try_cq_index = 0;
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_data_try_req = 1'b0;
		tb_ldu_mq_info_grab_data = 32'h00000000;
	    // central queue info grab
		tb_ldu_cq_info_grab_bank0_cq_index = 0;

		tb_ldu_cq_info_grab_bank1_cq_index = 0;
	    // central queue info ret
		tb_ldu_cq_info_ret_bank0_valid = 1'b0;
		tb_ldu_cq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank0_cq_index = 0;
		tb_ldu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank0_data = 32'h00000000;

		tb_ldu_cq_info_ret_bank1_valid = 1'b0;
		tb_ldu_cq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank1_cq_index = 0;
		tb_ldu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_mq_index = 0;

		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_mq_index = 0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
		tb_dcache_miss_resp_cq_index = 0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank0_cq_index = 0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_mq_index = 0;

		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank1_cq_index = 0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_mq_index = 0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h00000000;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h00000000;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h00;
		tb_ldu_CAM_launch_cq_index = 0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 0;
	    // ldu CAM return
	    // store set CAM update
	    // store set commit update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h00;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h00;
	    // ROB complete notif
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
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b0;
		expected_second_try_misaligned = 1'b0;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 22'h000000;
		expected_second_try_PO_word = 10'h000;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 0;
		expected_second_try_mq_index = 0;
	    // second try feedback
	    // data try
		expected_data_try_bank0_valid = 1'b0;
		expected_data_try_bank1_valid = 1'b0;
		expected_data_try_do_mispred = 1'b0;
		expected_data_try_data = 32'h00000000;
		expected_data_try_cq_index = 0;
	    // data try feedback
	    // misaligned queue data try req
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_mq_index = 0;
		expected_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // central queue info grab
		expected_ldu_cq_info_grab_bank0_op = 4'b0000;
		expected_ldu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank0_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank0_ROB_index = 7'h00;

		expected_ldu_cq_info_grab_bank1_op = 4'b0000;
		expected_ldu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank1_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_valid = 1'b0;
		expected_ldu_CAM_return_forward = 1'b0;
		expected_ldu_CAM_return_cq_index = 0;
		expected_ldu_CAM_return_is_mq = 1'b0;
		expected_ldu_CAM_return_mq_index = 0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h00;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h00;
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB complete notif
		expected_ldu_complete_valid = 1'b0;
		expected_ldu_complete_ROB_index = 7'h00;
	    // ROB commit
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tcq enq: v 0: LB dtlb hit, d$ hit",
			"\n\t\tmq data try: i",
			"\n\t\tmq info grab: i",
			"\n\t\tcq info grab bank0: i",
			"\n\t\tcq info grab bank1: i",
			"\n\t\tcq info ret bank0: i",
			"\n\t\tcq info ret bank1: i",
			"\n\t\tmq info ret bank0: i",
			"\n\t\tmq info ret bank1: i",
			"\n\t\tdtlb miss resp: i",
			"\n\t\tdcache miss resp: i",
			"\n\t\tstamofu CAM ret: i",
			"\n\t\tldu CAM launch: i",
			"\n\t\taq adv: i",
			"\n\t\tstamofu adv: i",
			"\n\t\tROB commit: i",
			"\n\t\tROB kill: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "9: i",
			"\n\t\t\t", "8: i",
			"\n\t\t\t", "7: i",
			"\n\t\t\t", "6: i",
			"\n\t\t\t", "5: i",
			"\n\t\t\t", "4: i",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tsecond try: i",
			"\n\t\tdata try: i",
			"\n\t\tldu CAM ret: i",
			"\n\t\tssu CAM update: i",
			"\n\t\tssu commit update: i",
			"\n\t\tROB complete: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_ldu_cq_enq_valid = 1'b1;
		tb_ldu_cq_enq_killed = 1'b0;
		tb_ldu_cq_enq_op = 4'b0000;
		tb_ldu_cq_enq_mdp_info = 8'b00000000;
		tb_ldu_cq_enq_dest_PR = 7'hf0;
		tb_ldu_cq_enq_ROB_index = 7'h00;
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;

		tb_second_try_bank1_ack = 1'b0;
	    // data try
	    // data try feedback
		tb_data_try_bank0_ack = 1'b0;

		tb_data_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
		tb_ldu_mq_data_try_req_valid = 1'b0;
		tb_ldu_mq_data_try_cq_index = 0;
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_data_try_req = 1'b0;
		tb_ldu_mq_info_grab_data = 32'h00000000;
	    // central queue info grab
		tb_ldu_cq_info_grab_bank0_cq_index = 0;

		tb_ldu_cq_info_grab_bank1_cq_index = 0;
	    // central queue info ret
		tb_ldu_cq_info_ret_bank0_valid = 1'b0;
		tb_ldu_cq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank0_cq_index = 0;
		tb_ldu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank0_data = 32'h00000000;

		tb_ldu_cq_info_ret_bank1_valid = 1'b0;
		tb_ldu_cq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank1_cq_index = 0;
		tb_ldu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_mq_index = 0;

		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_mq_index = 0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
		tb_dcache_miss_resp_cq_index = 0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank0_cq_index = 0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_mq_index = 0;

		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank1_cq_index = 0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_mq_index = 0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h00000000;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h00000000;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h00;
		tb_ldu_CAM_launch_cq_index = 0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 0;
	    // ldu CAM return
	    // store set CAM update
	    // store set commit update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h00;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h00;
	    // ROB complete notif
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
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b0;
		expected_second_try_misaligned = 1'b0;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 22'h000000;
		expected_second_try_PO_word = 10'h000;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 0;
		expected_second_try_mq_index = 0;
	    // second try feedback
	    // data try
		expected_data_try_bank0_valid = 1'b0;
		expected_data_try_bank1_valid = 1'b0;
		expected_data_try_do_mispred = 1'b0;
		expected_data_try_data = 32'h00000000;
		expected_data_try_cq_index = 0;
	    // data try feedback
	    // misaligned queue data try req
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_mq_index = 0;
		expected_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // central queue info grab
		expected_ldu_cq_info_grab_bank0_op = 4'b0000;
		expected_ldu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank0_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank0_ROB_index = 7'h00;

		expected_ldu_cq_info_grab_bank1_op = 4'b0000;
		expected_ldu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank1_dest_PR = 7'h00;
		expected_ldu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_valid = 1'b0;
		expected_ldu_CAM_return_forward = 1'b0;
		expected_ldu_CAM_return_cq_index = 0;
		expected_ldu_CAM_return_is_mq = 1'b0;
		expected_ldu_CAM_return_mq_index = 0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h00;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h00;
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB complete notif
		expected_ldu_complete_valid = 1'b0;
		expected_ldu_complete_ROB_index = 7'h00;
	    // ROB commit
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tcq enq: v 1: LH dtlb hit, d$ hit, mdp",
			"\n\t\tmq data try: i",
			"\n\t\tmq info grab: i",
			"\n\t\tcq info grab bank0: i",
			"\n\t\tcq info grab bank1: i",
			"\n\t\tcq info ret bank0: v 0: LB dtlb hit, d$ hit",
			"\n\t\tcq info ret bank1: i",
			"\n\t\tmq info ret bank0: i",
			"\n\t\tmq info ret bank1: i",
			"\n\t\tdtlb miss resp: i",
			"\n\t\tdcache miss resp: i",
			"\n\t\tstamofu CAM ret: i",
			"\n\t\tldu CAM launch: i",
			"\n\t\taq adv: i",
			"\n\t\tstamofu adv: i",
			"\n\t\tROB commit: i",
			"\n\t\tROB kill: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "9: i",
			"\n\t\t\t", "8: i",
			"\n\t\t\t", "7: i",
			"\n\t\t\t", "6: i",
			"\n\t\t\t", "5: i",
			"\n\t\t\t", "4: i",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v 0: LB dtlb hit, d$ hit",
			"\n\t\tsecond try: i",
			"\n\t\tdata try: i",
			"\n\t\tldu CAM ret: i",
			"\n\t\tssu CAM update: i",
			"\n\t\tssu commit update: i",
			"\n\t\tROB complete: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_ldu_cq_enq_valid = 1'b1;
		tb_ldu_cq_enq_killed = 1'b0;
		tb_ldu_cq_enq_op = 4'b0001;
		tb_ldu_cq_enq_mdp_info = 8'b01010101;
		tb_ldu_cq_enq_dest_PR = 7'he1;
		tb_ldu_cq_enq_ROB_index = 7'h01;
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;

		tb_second_try_bank1_ack = 1'b0;
	    // data try
	    // data try feedback
		tb_data_try_bank0_ack = 1'b0;

		tb_data_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
		tb_ldu_mq_data_try_req_valid = 1'b0;
		tb_ldu_mq_data_try_cq_index = 0;
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_data_try_req = 1'b0;
		tb_ldu_mq_info_grab_data = 32'h00000000;
	    // central queue info grab
		tb_ldu_cq_info_grab_bank0_cq_index = 0;

		tb_ldu_cq_info_grab_bank1_cq_index = 0;
	    // central queue info ret
		tb_ldu_cq_info_ret_bank0_valid = 1'b1;
		tb_ldu_cq_info_ret_bank0_WB_sent = 1'b1;
		tb_ldu_cq_info_ret_bank0_cq_index = 0;
		tb_ldu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank0_dtlb_hit = 1'b1;
		tb_ldu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_dcache_hit = 1'b1;
		tb_ldu_cq_info_ret_bank0_is_mem = 1'b1;
		tb_ldu_cq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank0_PA_word = 32'hffff0000;
		tb_ldu_cq_info_ret_bank0_byte_mask = 4'b0001;
		tb_ldu_cq_info_ret_bank0_data = 32'hf0f0f0f0;

		tb_ldu_cq_info_ret_bank1_valid = 1'b0;
		tb_ldu_cq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank1_cq_index = 0;
		tb_ldu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank1_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank1_data = 32'h00000000;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_mq_index = 0;

		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_mq_index = 0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
		tb_dcache_miss_resp_cq_index = 0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank0_cq_index = 0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_mq_index = 0;

		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank1_cq_index = 0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_mq_index = 0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h00000000;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h00000000;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h00;
		tb_ldu_CAM_launch_cq_index = 0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 0;
	    // ldu CAM return
	    // store set CAM update
	    // store set commit update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h00;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h00;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h00;
	    // ROB complete notif
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
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b0;
		expected_second_try_misaligned = 1'b0;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 22'h000000;
		expected_second_try_PO_word = 10'h000;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 0;
		expected_second_try_mq_index = 0;
	    // second try feedback
	    // data try
		expected_data_try_bank0_valid = 1'b0;
		expected_data_try_bank1_valid = 1'b0;
		expected_data_try_do_mispred = 1'b0;
		expected_data_try_data = 32'h00000000;
		expected_data_try_cq_index = 0;
	    // data try feedback
	    // misaligned queue data try req
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_mq_index = 0;
		expected_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // central queue info grab
		expected_ldu_cq_info_grab_bank0_op = 4'b0000;
		expected_ldu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank0_dest_PR = 7'hf0;
		expected_ldu_cq_info_grab_bank0_ROB_index = 7'h00;

		expected_ldu_cq_info_grab_bank1_op = 4'b0000;
		expected_ldu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank1_dest_PR = 7'hf0;
		expected_ldu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_valid = 1'b0;
		expected_ldu_CAM_return_forward = 1'b0;
		expected_ldu_CAM_return_cq_index = 0;
		expected_ldu_CAM_return_is_mq = 1'b0;
		expected_ldu_CAM_return_mq_index = 0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h00;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h00;
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB complete notif
		expected_ldu_complete_valid = 1'b0;
		expected_ldu_complete_ROB_index = 7'h00;
	    // ROB commit
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tcq enq: v 2: LW dtlb hit, d$ hit, aq_blocking",
			"\n\t\tmq data try: i",
			"\n\t\tmq info grab: i",
			"\n\t\tcq info grab bank0: i",
			"\n\t\tcq info grab bank1: i",
			"\n\t\tcq info ret bank0: i",
			"\n\t\tcq info ret bank1: v 1: LH dtlb hit, d$ hit, mdp",
			"\n\t\tmq info ret bank0: i",
			"\n\t\tmq info ret bank1: i",
			"\n\t\tdtlb miss resp: i",
			"\n\t\tdcache miss resp: i",
			"\n\t\tstamofu CAM ret: i",
			"\n\t\tldu CAM launch: i",
			"\n\t\taq adv: mem aq >1, io aq >8",
			"\n\t\tstamofu adv: i",
			"\n\t\tROB commit: i",
			"\n\t\tROB kill: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "9: i",
			"\n\t\t\t", "8: i",
			"\n\t\t\t", "7: i",
			"\n\t\t\t", "6: i",
			"\n\t\t\t", "5: i",
			"\n\t\t\t", "4: i",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v 1: LH dtlb hit, d$ hit, mdp",
			"\n\t\t\t", "0: v 0: LB dtlb hit, d$ hit",
			"\n\t\tsecond try: i",
			"\n\t\tdata try: i",
			"\n\t\tldu CAM ret: i",
			"\n\t\tssu CAM update: i",
			"\n\t\tssu commit update: i",
			"\n\t\tROB complete: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_ldu_cq_enq_valid = 1'b1;
		tb_ldu_cq_enq_killed = 1'b0;
		tb_ldu_cq_enq_op = 4'b0010;
		tb_ldu_cq_enq_mdp_info = 8'b00111111;
		tb_ldu_cq_enq_dest_PR = 7'hd2;
		tb_ldu_cq_enq_ROB_index = 7'h02;
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;

		tb_second_try_bank1_ack = 1'b0;
	    // data try
	    // data try feedback
		tb_data_try_bank0_ack = 1'b0;

		tb_data_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
		tb_ldu_mq_data_try_req_valid = 1'b0;
		tb_ldu_mq_data_try_cq_index = 0;
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_data_try_req = 1'b0;
		tb_ldu_mq_info_grab_data = 32'h00000000;
	    // central queue info grab
		tb_ldu_cq_info_grab_bank0_cq_index = 0;

		tb_ldu_cq_info_grab_bank1_cq_index = 0;
	    // central queue info ret
		tb_ldu_cq_info_ret_bank0_valid = 1'b0;
		tb_ldu_cq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank0_cq_index = 0;
		tb_ldu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank0_PA_word = 32'h00000000;
		tb_ldu_cq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_cq_info_ret_bank0_data = 32'h00000000;

		tb_ldu_cq_info_ret_bank1_valid = 1'b1;
		tb_ldu_cq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank1_cq_index = 1;
		tb_ldu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank1_dtlb_hit = 1'b1;
		tb_ldu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_dcache_hit = 1'b1;
		tb_ldu_cq_info_ret_bank1_is_mem = 1'b1;
		tb_ldu_cq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank1_PA_word = 32'heeee1111;
		tb_ldu_cq_info_ret_bank1_byte_mask = 4'b0110;
		tb_ldu_cq_info_ret_bank1_data = 32'he1e1e1e1;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_mq_index = 0;

		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_mq_index = 0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
		tb_dcache_miss_resp_cq_index = 0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank0_cq_index = 0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_mq_index = 0;

		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank1_cq_index = 0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_mq_index = 0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h00000000;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h00000000;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h00;
		tb_ldu_CAM_launch_cq_index = 0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 0;
	    // ldu CAM return
	    // store set CAM update
	    // store set commit update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h01;
		tb_stamofu_aq_io_aq_active = 1'b1;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h08;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h00;
	    // ROB complete notif
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
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b1;
		expected_second_try_is_mq = 1'b0;
		expected_second_try_misaligned = 1'b0;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b1;
		expected_second_try_PPN = 22'hffff0 << 2;
		expected_second_try_PO_word = 10'h000;
		expected_second_try_byte_mask = 4'b0001;
		expected_second_try_cq_index = 0;
		expected_second_try_mq_index = 0;
	    // second try feedback
	    // data try
		expected_data_try_bank0_valid = 1'b0;
		expected_data_try_bank1_valid = 1'b0;
		expected_data_try_do_mispred = 1'b1;
		expected_data_try_data = 32'hf0f0f0f0;
		expected_data_try_cq_index = 0;
	    // data try feedback
	    // misaligned queue data try req
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_mq_index = 0;
		expected_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // central queue info grab
		expected_ldu_cq_info_grab_bank0_op = 4'b0000;
		expected_ldu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank0_dest_PR = 7'hf0;
		expected_ldu_cq_info_grab_bank0_ROB_index = 7'h00;

		expected_ldu_cq_info_grab_bank1_op = 4'b0000;
		expected_ldu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank1_dest_PR = 7'hf0;
		expected_ldu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_valid = 1'b0;
		expected_ldu_CAM_return_forward = 1'b0;
		expected_ldu_CAM_return_cq_index = 0;
		expected_ldu_CAM_return_is_mq = 1'b0;
		expected_ldu_CAM_return_mq_index = 0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h00;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h00;
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB complete notif
		expected_ldu_complete_valid = 1'b0;
		expected_ldu_complete_ROB_index = 7'h00;
	    // ROB commit
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tcq enq: v 3: LB dtlb hit, d$ miss",
			"\n\t\tmq data try: i",
			"\n\t\tmq info grab: i",
			"\n\t\tcq info grab bank0: i",
			"\n\t\tcq info grab bank1: i",
			"\n\t\tcq info ret bank0: v 2: LW dtlb hit, d$ hit, aq_blocking",
			"\n\t\tcq info ret bank1: i",
			"\n\t\tmq info ret bank0: i",
			"\n\t\tmq info ret bank1: i",
			"\n\t\tdtlb miss resp: i",
			"\n\t\tdcache miss resp: i",
			"\n\t\tstamofu CAM ret: i",
			"\n\t\tldu CAM launch: i",
			"\n\t\taq adv: mem aq >1, io aq >8",
			"\n\t\tstamofu adv: i",
			"\n\t\tROB commit: i",
			"\n\t\tROB kill: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "9: i",
			"\n\t\t\t", "8: i",
			"\n\t\t\t", "7: i",
			"\n\t\t\t", "6: i",
			"\n\t\t\t", "5: i",
			"\n\t\t\t", "4: i",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 2: LW dtlb hit, d$ hit, aq_blocking",
			"\n\t\t\t", "1: v 1: LH dtlb hit, d$ hit, mdp",
			"\n\t\t\t", "0: v 0: LB dtlb hit, d$ hit",
			"\n\t\tsecond try: i",
			"\n\t\tdata try: i",
			"\n\t\tldu CAM ret: i",
			"\n\t\tssu CAM update: i",
			"\n\t\tssu commit update: i",
			"\n\t\tROB complete: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to central queue
		tb_ldu_cq_enq_valid = 1'b1;
		tb_ldu_cq_enq_killed = 1'b0;
		tb_ldu_cq_enq_op = 4'b0010;
		tb_ldu_cq_enq_mdp_info = 8'b00111100;
		tb_ldu_cq_enq_dest_PR = 7'hc3;
		tb_ldu_cq_enq_ROB_index = 7'h03;
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;

		tb_second_try_bank1_ack = 1'b0;
	    // data try
	    // data try feedback
		tb_data_try_bank0_ack = 1'b0;

		tb_data_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
		tb_ldu_mq_data_try_req_valid = 1'b0;
		tb_ldu_mq_data_try_cq_index = 0;
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_data_try_req = 1'b0;
		tb_ldu_mq_info_grab_data = 32'h00000000;
	    // central queue info grab
		tb_ldu_cq_info_grab_bank0_cq_index = 0;

		tb_ldu_cq_info_grab_bank1_cq_index = 0;
	    // central queue info ret
		tb_ldu_cq_info_ret_bank0_valid = 1'b1;
		tb_ldu_cq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank0_cq_index = 0;
		tb_ldu_cq_info_ret_bank0_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank0_dtlb_hit = 1'b1;
		tb_ldu_cq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank0_dcache_hit = 1'b1;
		tb_ldu_cq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_cq_info_ret_bank0_aq_blocking = 1'b1;
		tb_ldu_cq_info_ret_bank0_PA_word = 32'hdddd2222;
		tb_ldu_cq_info_ret_bank0_byte_mask = 4'b1111;
		tb_ldu_cq_info_ret_bank0_data = 32'hd2d2d2d2;

		tb_ldu_cq_info_ret_bank1_valid = 1'b0;
		tb_ldu_cq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_cq_info_ret_bank1_cq_index = 1;
		tb_ldu_cq_info_ret_bank1_misaligned = 1'b0;
		tb_ldu_cq_info_ret_bank1_dtlb_hit = 1'b1;
		tb_ldu_cq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_cq_info_ret_bank1_dcache_hit = 1'b1;
		tb_ldu_cq_info_ret_bank1_is_mem = 1'b1;
		tb_ldu_cq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_cq_info_ret_bank1_PA_word = 32'heeee1111;
		tb_ldu_cq_info_ret_bank1_byte_mask = 4'b0110;
		tb_ldu_cq_info_ret_bank1_data = 32'he1e1e1e1;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_mq_index = 0;

		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_mq_index = 0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
		tb_dcache_miss_resp_cq_index = 0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank0_cq_index = 0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_mq_index = 0;

		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_updated_mdp_info = 8'b00000000;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h00;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h00000000;
		tb_stamofu_CAM_return_bank1_cq_index = 0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_mq_index = 0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h00000000;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h00000000;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h00;
		tb_ldu_CAM_launch_cq_index = 0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 0;
	    // ldu CAM return
	    // store set CAM update
	    // store set commit update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h01;
		tb_stamofu_aq_io_aq_active = 1'b1;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h08;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h00;
	    // ROB complete notif
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
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b1;
		expected_second_try_is_mq = 1'b0;
		expected_second_try_misaligned = 1'b0;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b1;
		expected_second_try_PPN = 22'hffff0 << 2;
		expected_second_try_PO_word = 10'h000;
		expected_second_try_byte_mask = 4'b0001;
		expected_second_try_cq_index = 0;
		expected_second_try_mq_index = 0;
	    // second try feedback
	    // data try
		expected_data_try_bank0_valid = 1'b0;
		expected_data_try_bank1_valid = 1'b0;
		expected_data_try_do_mispred = 1'b1;
		expected_data_try_data = 32'hf0f0f0f0;
		expected_data_try_cq_index = 0;
	    // data try feedback
	    // misaligned queue data try req
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_mq_index = 0;
		expected_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // central queue info grab
		expected_ldu_cq_info_grab_bank0_op = 4'b0000;
		expected_ldu_cq_info_grab_bank0_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank0_dest_PR = 7'hf0;
		expected_ldu_cq_info_grab_bank0_ROB_index = 7'h00;

		expected_ldu_cq_info_grab_bank1_op = 4'b0000;
		expected_ldu_cq_info_grab_bank1_mdp_info = 8'b00000000;
		expected_ldu_cq_info_grab_bank1_dest_PR = 7'hf0;
		expected_ldu_cq_info_grab_bank1_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_valid = 1'b0;
		expected_ldu_CAM_return_forward = 1'b0;
		expected_ldu_CAM_return_cq_index = 0;
		expected_ldu_CAM_return_is_mq = 1'b0;
		expected_ldu_CAM_return_mq_index = 0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h00;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h00;
	    // store set commit update
		expected_ssu_commit_update_valid = 1'b0;
		expected_ssu_commit_update_mdp_info = 8'b00000000;
		expected_ssu_commit_update_ROB_index = 7'h00;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB complete notif
		expected_ldu_complete_valid = 1'b0;
		expected_ldu_complete_ROB_index = 7'h00;
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