/*
    Filename: ldu_mq_tb.sv
    Author: zlagpacan
    Description: Testbench for ldu_mq module. 
    Spec: LOROF/spec/design/ldu_mq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter LDU_MQ_ENTRIES = 4;
parameter LOG_LDU_MQ_ENTRIES = $clog2(LDU_MQ_ENTRIES);

module ldu_mq_tb ();

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

    // op enqueue to misaligned queue
	logic tb_ldu_mq_enq_valid;

    // misaligned queue enqueue feedback
	logic DUT_ldu_mq_enq_ready, expected_ldu_mq_enq_ready;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_ldu_mq_enq_index, expected_ldu_mq_enq_index;

    // second try
        // prioritize this one from mq over cq's
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

    // misaligned queue data try req
	logic DUT_ldu_mq_data_try_req_valid, expected_ldu_mq_data_try_req_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_ldu_mq_data_try_cq_index, expected_ldu_mq_data_try_cq_index;

    // misaligned queue info grab
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_ldu_mq_info_grab_mq_index;
	logic tb_ldu_mq_info_grab_data_try_ack;
	logic DUT_ldu_mq_info_grab_data_try_req, expected_ldu_mq_info_grab_data_try_req;
	logic [31:0] DUT_ldu_mq_info_grab_data, expected_ldu_mq_info_grab_data;

    // misaligned queue info ret
	logic tb_ldu_mq_info_ret_bank0_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_mq_info_ret_bank0_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_ldu_mq_info_ret_bank0_mq_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_mq_info_ret_bank0_ROB_index;
	logic tb_ldu_mq_info_ret_bank0_WB_sent;
	logic tb_ldu_mq_info_ret_bank0_dtlb_hit;
	logic tb_ldu_mq_info_ret_bank0_page_fault;
	logic tb_ldu_mq_info_ret_bank0_access_fault;
	logic tb_ldu_mq_info_ret_bank0_dcache_hit;
	logic tb_ldu_mq_info_ret_bank0_is_mem;
	logic tb_ldu_mq_info_ret_bank0_aq_blocking;
	logic [PA_WIDTH-2-1:0] tb_ldu_mq_info_ret_bank0_PA_word;
	logic [3:0] tb_ldu_mq_info_ret_bank0_byte_mask;
	logic [31:0] tb_ldu_mq_info_ret_bank0_data;

	logic tb_ldu_mq_info_ret_bank1_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_mq_info_ret_bank1_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_ldu_mq_info_ret_bank1_mq_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_mq_info_ret_bank1_ROB_index;
	logic tb_ldu_mq_info_ret_bank1_WB_sent;
	logic tb_ldu_mq_info_ret_bank1_dtlb_hit;
	logic tb_ldu_mq_info_ret_bank1_page_fault;
	logic tb_ldu_mq_info_ret_bank1_access_fault;
	logic tb_ldu_mq_info_ret_bank1_dcache_hit;
	logic tb_ldu_mq_info_ret_bank1_is_mem;
	logic tb_ldu_mq_info_ret_bank1_aq_blocking;
	logic [PA_WIDTH-2-1:0] tb_ldu_mq_info_ret_bank1_PA_word;
	logic [3:0] tb_ldu_mq_info_ret_bank1_byte_mask;
	logic [31:0] tb_ldu_mq_info_ret_bank1_data;

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
	logic tb_stamofu_CAM_return_bank0_is_mq;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank0_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank0_mq_index;
	logic tb_stamofu_CAM_return_bank0_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank0_stall_count;
	logic [3:0] tb_stamofu_CAM_return_bank0_forward;
	logic tb_stamofu_CAM_return_bank0_nasty_forward;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_CAM_return_bank0_forward_ROB_index;
	logic [31:0] tb_stamofu_CAM_return_bank0_forward_data;

	logic tb_stamofu_CAM_return_bank1_valid;
	logic tb_stamofu_CAM_return_bank1_is_mq;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank1_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank1_mq_index;
	logic tb_stamofu_CAM_return_bank1_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_CAM_return_bank1_stall_count;
	logic [3:0] tb_stamofu_CAM_return_bank1_forward;
	logic tb_stamofu_CAM_return_bank1_nasty_forward;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_CAM_return_bank1_forward_ROB_index;
	logic [31:0] tb_stamofu_CAM_return_bank1_forward_data;

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
	logic DUT_ldu_CAM_return_forward, expected_ldu_CAM_return_forward;

    // ldu_mq commit
	logic tb_ldu_cq_commit_mq_valid;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_ldu_cq_commit_mq_index;
	logic DUT_ldu_cq_commit_mq_has_forward, expected_ldu_cq_commit_mq_has_forward;

    // store set CAM update
        // implied dep
        // prioritize this one from mq over cq's
	logic DUT_ssu_CAM_update_valid, expected_ssu_CAM_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ssu_CAM_update_ld_mdp_info, expected_ssu_CAM_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ssu_CAM_update_ld_ROB_index, expected_ssu_CAM_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ssu_CAM_update_stamo_mdp_info, expected_ssu_CAM_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ssu_CAM_update_stamo_ROB_index, expected_ssu_CAM_update_stamo_ROB_index;

    // acquire advertisement
	logic tb_stamofu_aq_mem_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_mem_aq_oldest_abs_ROB_index;
	logic tb_stamofu_aq_io_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_io_aq_oldest_abs_ROB_index;

    // oldest stamofu advertisement
	logic tb_stamofu_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_oldest_ROB_index;

    // ROB kill
	logic tb_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ldu_mq #(
		.LDU_MQ_ENTRIES(LDU_MQ_ENTRIES),
		.LOG_LDU_MQ_ENTRIES(LOG_LDU_MQ_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to misaligned queue
		.ldu_mq_enq_valid(tb_ldu_mq_enq_valid),

	    // misaligned queue enqueue feedback
		.ldu_mq_enq_ready(DUT_ldu_mq_enq_ready),
		.ldu_mq_enq_index(DUT_ldu_mq_enq_index),

	    // second try
	        // prioritize this one from mq over cq's
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

	    // misaligned queue data try req
		.ldu_mq_data_try_req_valid(DUT_ldu_mq_data_try_req_valid),
		.ldu_mq_data_try_cq_index(DUT_ldu_mq_data_try_cq_index),

	    // misaligned queue info grab
		.ldu_mq_info_grab_mq_index(tb_ldu_mq_info_grab_mq_index),
		.ldu_mq_info_grab_data_try_ack(tb_ldu_mq_info_grab_data_try_ack),
		.ldu_mq_info_grab_data_try_req(DUT_ldu_mq_info_grab_data_try_req),
		.ldu_mq_info_grab_data(DUT_ldu_mq_info_grab_data),

	    // misaligned queue info ret
		.ldu_mq_info_ret_bank0_valid(tb_ldu_mq_info_ret_bank0_valid),
		.ldu_mq_info_ret_bank0_cq_index(tb_ldu_mq_info_ret_bank0_cq_index),
		.ldu_mq_info_ret_bank0_mq_index(tb_ldu_mq_info_ret_bank0_mq_index),
		.ldu_mq_info_ret_bank0_ROB_index(tb_ldu_mq_info_ret_bank0_ROB_index),
		.ldu_mq_info_ret_bank0_WB_sent(tb_ldu_mq_info_ret_bank0_WB_sent),
		.ldu_mq_info_ret_bank0_dtlb_hit(tb_ldu_mq_info_ret_bank0_dtlb_hit),
		.ldu_mq_info_ret_bank0_page_fault(tb_ldu_mq_info_ret_bank0_page_fault),
		.ldu_mq_info_ret_bank0_access_fault(tb_ldu_mq_info_ret_bank0_access_fault),
		.ldu_mq_info_ret_bank0_dcache_hit(tb_ldu_mq_info_ret_bank0_dcache_hit),
		.ldu_mq_info_ret_bank0_is_mem(tb_ldu_mq_info_ret_bank0_is_mem),
		.ldu_mq_info_ret_bank0_aq_blocking(tb_ldu_mq_info_ret_bank0_aq_blocking),
		.ldu_mq_info_ret_bank0_PA_word(tb_ldu_mq_info_ret_bank0_PA_word),
		.ldu_mq_info_ret_bank0_byte_mask(tb_ldu_mq_info_ret_bank0_byte_mask),
		.ldu_mq_info_ret_bank0_data(tb_ldu_mq_info_ret_bank0_data),

		.ldu_mq_info_ret_bank1_valid(tb_ldu_mq_info_ret_bank1_valid),
		.ldu_mq_info_ret_bank1_cq_index(tb_ldu_mq_info_ret_bank1_cq_index),
		.ldu_mq_info_ret_bank1_mq_index(tb_ldu_mq_info_ret_bank1_mq_index),
		.ldu_mq_info_ret_bank1_ROB_index(tb_ldu_mq_info_ret_bank1_ROB_index),
		.ldu_mq_info_ret_bank1_WB_sent(tb_ldu_mq_info_ret_bank1_WB_sent),
		.ldu_mq_info_ret_bank1_dtlb_hit(tb_ldu_mq_info_ret_bank1_dtlb_hit),
		.ldu_mq_info_ret_bank1_page_fault(tb_ldu_mq_info_ret_bank1_page_fault),
		.ldu_mq_info_ret_bank1_access_fault(tb_ldu_mq_info_ret_bank1_access_fault),
		.ldu_mq_info_ret_bank1_dcache_hit(tb_ldu_mq_info_ret_bank1_dcache_hit),
		.ldu_mq_info_ret_bank1_is_mem(tb_ldu_mq_info_ret_bank1_is_mem),
		.ldu_mq_info_ret_bank1_aq_blocking(tb_ldu_mq_info_ret_bank1_aq_blocking),
		.ldu_mq_info_ret_bank1_PA_word(tb_ldu_mq_info_ret_bank1_PA_word),
		.ldu_mq_info_ret_bank1_byte_mask(tb_ldu_mq_info_ret_bank1_byte_mask),
		.ldu_mq_info_ret_bank1_data(tb_ldu_mq_info_ret_bank1_data),

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
		.stamofu_CAM_return_bank0_cq_index(tb_stamofu_CAM_return_bank0_cq_index),
		.stamofu_CAM_return_bank0_is_mq(tb_stamofu_CAM_return_bank0_is_mq),
		.stamofu_CAM_return_bank0_mq_index(tb_stamofu_CAM_return_bank0_mq_index),
		.stamofu_CAM_return_bank0_stall(tb_stamofu_CAM_return_bank0_stall),
		.stamofu_CAM_return_bank0_stall_count(tb_stamofu_CAM_return_bank0_stall_count),
		.stamofu_CAM_return_bank0_forward(tb_stamofu_CAM_return_bank0_forward),
		.stamofu_CAM_return_bank0_nasty_forward(tb_stamofu_CAM_return_bank0_nasty_forward),
		.stamofu_CAM_return_bank0_forward_ROB_index(tb_stamofu_CAM_return_bank0_forward_ROB_index),
		.stamofu_CAM_return_bank0_forward_data(tb_stamofu_CAM_return_bank0_forward_data),

		.stamofu_CAM_return_bank1_valid(tb_stamofu_CAM_return_bank1_valid),
		.stamofu_CAM_return_bank1_cq_index(tb_stamofu_CAM_return_bank1_cq_index),
		.stamofu_CAM_return_bank1_is_mq(tb_stamofu_CAM_return_bank1_is_mq),
		.stamofu_CAM_return_bank1_mq_index(tb_stamofu_CAM_return_bank1_mq_index),
		.stamofu_CAM_return_bank1_stall(tb_stamofu_CAM_return_bank1_stall),
		.stamofu_CAM_return_bank1_stall_count(tb_stamofu_CAM_return_bank1_stall_count),
		.stamofu_CAM_return_bank1_forward(tb_stamofu_CAM_return_bank1_forward),
		.stamofu_CAM_return_bank1_nasty_forward(tb_stamofu_CAM_return_bank1_nasty_forward),
		.stamofu_CAM_return_bank1_forward_ROB_index(tb_stamofu_CAM_return_bank1_forward_ROB_index),
		.stamofu_CAM_return_bank1_forward_data(tb_stamofu_CAM_return_bank1_forward_data),

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
		.ldu_CAM_return_forward(DUT_ldu_CAM_return_forward),

	    // ldu_mq commit
		.ldu_cq_commit_mq_valid(tb_ldu_cq_commit_mq_valid),
		.ldu_cq_commit_mq_index(tb_ldu_cq_commit_mq_index),
		.ldu_cq_commit_mq_has_forward(DUT_ldu_cq_commit_mq_has_forward),

	    // store set CAM update
	        // implied dep
		.ssu_CAM_update_valid(DUT_ssu_CAM_update_valid),
		.ssu_CAM_update_ld_mdp_info(DUT_ssu_CAM_update_ld_mdp_info),
		.ssu_CAM_update_ld_ROB_index(DUT_ssu_CAM_update_ld_ROB_index),
		.ssu_CAM_update_stamo_mdp_info(DUT_ssu_CAM_update_stamo_mdp_info),
		.ssu_CAM_update_stamo_ROB_index(DUT_ssu_CAM_update_stamo_ROB_index),

	    // acquire advertisement
		.stamofu_aq_mem_aq_active(tb_stamofu_aq_mem_aq_active),
		.stamofu_aq_mem_aq_oldest_abs_ROB_index(tb_stamofu_aq_mem_aq_oldest_abs_ROB_index),
		.stamofu_aq_io_aq_active(tb_stamofu_aq_io_aq_active),
		.stamofu_aq_io_aq_oldest_abs_ROB_index(tb_stamofu_aq_io_aq_oldest_abs_ROB_index),

	    // oldest stamofu advertisement
		.stamofu_active(tb_stamofu_active),
		.stamofu_oldest_ROB_index(tb_stamofu_oldest_ROB_index),

	    // ROB kill
		.rob_kill_valid(tb_rob_kill_valid),
		.rob_kill_abs_head_index(tb_rob_kill_abs_head_index),
		.rob_kill_rel_kill_younger_index(tb_rob_kill_rel_kill_younger_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ldu_mq_enq_ready !== DUT_ldu_mq_enq_ready) begin
			$display("TB ERROR: expected_ldu_mq_enq_ready (%h) != DUT_ldu_mq_enq_ready (%h)",
				expected_ldu_mq_enq_ready, DUT_ldu_mq_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_enq_index !== DUT_ldu_mq_enq_index) begin
			$display("TB ERROR: expected_ldu_mq_enq_index (%h) != DUT_ldu_mq_enq_index (%h)",
				expected_ldu_mq_enq_index, DUT_ldu_mq_enq_index);
			num_errors++;
			tb_error = 1'b1;
		end

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

		if (expected_ldu_mq_data_try_req_valid !== DUT_ldu_mq_data_try_req_valid) begin
			$display("TB ERROR: expected_ldu_mq_data_try_req_valid (%h) != DUT_ldu_mq_data_try_req_valid (%h)",
				expected_ldu_mq_data_try_req_valid, DUT_ldu_mq_data_try_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_data_try_cq_index !== DUT_ldu_mq_data_try_cq_index) begin
			$display("TB ERROR: expected_ldu_mq_data_try_cq_index (%h) != DUT_ldu_mq_data_try_cq_index (%h)",
				expected_ldu_mq_data_try_cq_index, DUT_ldu_mq_data_try_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_grab_data_try_req !== DUT_ldu_mq_info_grab_data_try_req) begin
			$display("TB ERROR: expected_ldu_mq_info_grab_data_try_req (%h) != DUT_ldu_mq_info_grab_data_try_req (%h)",
				expected_ldu_mq_info_grab_data_try_req, DUT_ldu_mq_info_grab_data_try_req);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_grab_data !== DUT_ldu_mq_info_grab_data) begin
			$display("TB ERROR: expected_ldu_mq_info_grab_data (%h) != DUT_ldu_mq_info_grab_data (%h)",
				expected_ldu_mq_info_grab_data, DUT_ldu_mq_info_grab_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_return_forward !== DUT_ldu_CAM_return_forward) begin
			$display("TB ERROR: expected_ldu_CAM_return_forward (%h) != DUT_ldu_CAM_return_forward (%h)",
				expected_ldu_CAM_return_forward, DUT_ldu_CAM_return_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_commit_mq_has_forward !== DUT_ldu_cq_commit_mq_has_forward) begin
			$display("TB ERROR: expected_ldu_cq_commit_mq_has_forward (%h) != DUT_ldu_cq_commit_mq_has_forward (%h)",
				expected_ldu_cq_commit_mq_has_forward, DUT_ldu_cq_commit_mq_has_forward);
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
	    // op enqueue to misaligned queue
		tb_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;
		tb_second_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_mq_index = 2'h0;
		tb_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_cq_index = 'h0;
		tb_ldu_mq_info_ret_bank0_mq_index = 2'h0;
		tb_ldu_mq_info_ret_bank0_ROB_index = 7'h0;
		tb_ldu_mq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_mq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_mq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_mq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_mq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_mq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_mq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_mq_info_ret_bank0_PA_word = 32'h0;
		tb_ldu_mq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_mq_info_ret_bank0_data = 32'h0;
		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_cq_index = 'h0;
		tb_ldu_mq_info_ret_bank1_mq_index = 2'h0;
		tb_ldu_mq_info_ret_bank1_ROB_index = 7'h0;
		tb_ldu_mq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_mq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_mq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_mq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_mq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_mq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_mq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_mq_info_ret_bank1_PA_word = 32'h0;
		tb_ldu_mq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_mq_info_ret_bank1_data = 32'h0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 2'h0;
		tb_dtlb_miss_resp_PPN = 22'h0;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 'h0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 2'h0;
		tb_dcache_miss_resp_data = 32'h0;
		tb_dcache_miss_resp_cq_index = 'h0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_cq_index = 'h0;
		tb_stamofu_CAM_return_bank0_mq_index = 2'h0;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 'h0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h0;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h0;
		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_cq_index = 'h0;
		tb_stamofu_CAM_return_bank1_mq_index = 2'h0;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 'h0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h0;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h0;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h0;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h0;
		tb_ldu_CAM_launch_cq_index = 'h0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 2'h0;
	    // ldu CAM return
	    // ldu_mq commit
		tb_ldu_cq_commit_mq_valid = 1'b0;
		tb_ldu_cq_commit_mq_index = 'h0;
	    // store set CAM update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		expected_ldu_mq_enq_ready = 1'b1;
		expected_ldu_mq_enq_index = 2'h0;
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b1;
		expected_second_try_misaligned = 1'b1;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 32'h0;
		expected_second_try_PO_word = 10'h0;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 'h0;
		expected_second_try_mq_index = 2'h0;
	    // second try feedback
	    // misaligned queue data try req
		expected_ldu_mq_data_try_req_valid = 1'b0;
		expected_ldu_mq_data_try_cq_index = 'h0;
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_data_try_req = 1'b0;
		expected_ldu_mq_info_grab_data = 32'h0;
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_forward = 1'b0;
	    // ldu_mq commit
		expected_ldu_cq_commit_mq_has_forward = 1'b0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h0;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h0;
	    // acquire advertisement
	    // oldest stamofu advertisement
	    // ROB kill

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to misaligned queue
		tb_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;
		tb_second_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_mq_index = 2'h0;
		tb_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_cq_index = 'h0;
		tb_ldu_mq_info_ret_bank0_mq_index = 2'h0;
		tb_ldu_mq_info_ret_bank0_ROB_index = 7'h0;
		tb_ldu_mq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_mq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_mq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_mq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_mq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_mq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_mq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_mq_info_ret_bank0_PA_word = 32'h0;
		tb_ldu_mq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_mq_info_ret_bank0_data = 32'h0;
		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_cq_index = 'h0;
		tb_ldu_mq_info_ret_bank1_mq_index = 2'h0;
		tb_ldu_mq_info_ret_bank1_ROB_index = 7'h0;
		tb_ldu_mq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_mq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_mq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_mq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_mq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_mq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_mq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_mq_info_ret_bank1_PA_word = 32'h0;
		tb_ldu_mq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_mq_info_ret_bank1_data = 32'h0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 2'h0;
		tb_dtlb_miss_resp_PPN = 22'h0;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 'h0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 2'h0;
		tb_dcache_miss_resp_data = 32'h0;
		tb_dcache_miss_resp_cq_index = 'h0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_cq_index = 'h0;
		tb_stamofu_CAM_return_bank0_mq_index = 2'h0;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 'h0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h0;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h0;
		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_cq_index = 'h0;
		tb_stamofu_CAM_return_bank1_mq_index = 2'h0;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 'h0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h0;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h0;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h0;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h0;
		tb_ldu_CAM_launch_cq_index = 'h0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 2'h0;
	    // ldu CAM return
	    // ldu_mq commit
		tb_ldu_cq_commit_mq_valid = 1'b0;
		tb_ldu_cq_commit_mq_index = 'h0;
	    // store set CAM update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		expected_ldu_mq_enq_ready = 1'b1;
		expected_ldu_mq_enq_index = 2'h0;
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b1;
		expected_second_try_misaligned = 1'b1;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 32'h0;
		expected_second_try_PO_word = 10'h0;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 'h0;
		expected_second_try_mq_index = 2'h0;
	    // second try feedback
	    // misaligned queue data try req
		expected_ldu_mq_data_try_req_valid = 1'b0;
		expected_ldu_mq_data_try_cq_index = 'h0;
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_data_try_req = 1'b0;
		expected_ldu_mq_info_grab_data = 32'h0;
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_forward = 1'b0;
	    // ldu_mq commit
		expected_ldu_cq_commit_mq_has_forward = 1'b0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h0;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h0;
	    // acquire advertisement
	    // oldest stamofu advertisement
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
	    // op enqueue to misaligned queue
		tb_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // second try
	    // second try feedback
		tb_second_try_bank0_ack = 1'b0;
		tb_second_try_bank1_ack = 1'b0;
	    // misaligned queue data try req
	    // misaligned queue info grab
		tb_ldu_mq_info_grab_mq_index = 2'h0;
		tb_ldu_mq_info_grab_data_try_ack = 1'b0;
	    // misaligned queue info ret
		tb_ldu_mq_info_ret_bank0_valid = 1'b0;
		tb_ldu_mq_info_ret_bank0_cq_index = 'h0;
		tb_ldu_mq_info_ret_bank0_mq_index = 2'h0;
		tb_ldu_mq_info_ret_bank0_ROB_index = 7'h0;
		tb_ldu_mq_info_ret_bank0_WB_sent = 1'b0;
		tb_ldu_mq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_ldu_mq_info_ret_bank0_page_fault = 1'b0;
		tb_ldu_mq_info_ret_bank0_access_fault = 1'b0;
		tb_ldu_mq_info_ret_bank0_dcache_hit = 1'b0;
		tb_ldu_mq_info_ret_bank0_is_mem = 1'b0;
		tb_ldu_mq_info_ret_bank0_aq_blocking = 1'b0;
		tb_ldu_mq_info_ret_bank0_PA_word = 32'h0;
		tb_ldu_mq_info_ret_bank0_byte_mask = 4'b0000;
		tb_ldu_mq_info_ret_bank0_data = 32'h0;
		tb_ldu_mq_info_ret_bank1_valid = 1'b0;
		tb_ldu_mq_info_ret_bank1_cq_index = 'h0;
		tb_ldu_mq_info_ret_bank1_mq_index = 2'h0;
		tb_ldu_mq_info_ret_bank1_ROB_index = 7'h0;
		tb_ldu_mq_info_ret_bank1_WB_sent = 1'b0;
		tb_ldu_mq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_ldu_mq_info_ret_bank1_page_fault = 1'b0;
		tb_ldu_mq_info_ret_bank1_access_fault = 1'b0;
		tb_ldu_mq_info_ret_bank1_dcache_hit = 1'b0;
		tb_ldu_mq_info_ret_bank1_is_mem = 1'b0;
		tb_ldu_mq_info_ret_bank1_aq_blocking = 1'b0;
		tb_ldu_mq_info_ret_bank1_PA_word = 32'h0;
		tb_ldu_mq_info_ret_bank1_byte_mask = 4'b0000;
		tb_ldu_mq_info_ret_bank1_data = 32'h0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 2'h0;
		tb_dtlb_miss_resp_PPN = 22'h0;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
		tb_dtlb_miss_resp_cq_index = 'h0;
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 2'h0;
		tb_dcache_miss_resp_data = 32'h0;
		tb_dcache_miss_resp_cq_index = 'h0;
	    // stamofu CAM return
		tb_stamofu_CAM_return_bank0_valid = 1'b0;
		tb_stamofu_CAM_return_bank0_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank0_cq_index = 'h0;
		tb_stamofu_CAM_return_bank0_mq_index = 2'h0;
		tb_stamofu_CAM_return_bank0_stall = 1'b0;
		tb_stamofu_CAM_return_bank0_stall_count = 'h0;
		tb_stamofu_CAM_return_bank0_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank0_forward_ROB_index = 7'h0;
		tb_stamofu_CAM_return_bank0_forward_data = 32'h0;
		tb_stamofu_CAM_return_bank1_valid = 1'b0;
		tb_stamofu_CAM_return_bank1_is_mq = 1'b0;
		tb_stamofu_CAM_return_bank1_cq_index = 'h0;
		tb_stamofu_CAM_return_bank1_mq_index = 2'h0;
		tb_stamofu_CAM_return_bank1_stall = 1'b0;
		tb_stamofu_CAM_return_bank1_stall_count = 'h0;
		tb_stamofu_CAM_return_bank1_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_nasty_forward = 1'b0;
		tb_stamofu_CAM_return_bank1_forward_ROB_index = 7'h0;
		tb_stamofu_CAM_return_bank1_forward_data = 32'h0;
	    // ldu CAM launch
		tb_ldu_CAM_launch_valid = 1'b0;
		tb_ldu_CAM_launch_is_amo = 1'b0;
		tb_ldu_CAM_launch_PA_word = 32'h0;
		tb_ldu_CAM_launch_byte_mask = 4'b0000;
		tb_ldu_CAM_launch_write_data = 32'h0;
		tb_ldu_CAM_launch_mdp_info = 8'b00000000;
		tb_ldu_CAM_launch_ROB_index = 7'h0;
		tb_ldu_CAM_launch_cq_index = 'h0;
		tb_ldu_CAM_launch_is_mq = 1'b0;
		tb_ldu_CAM_launch_mq_index = 2'h0;
	    // ldu CAM return
	    // ldu_mq commit
		tb_ldu_cq_commit_mq_valid = 1'b0;
		tb_ldu_cq_commit_mq_index = 'h0;
	    // store set CAM update
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // oldest stamofu advertisement
		tb_stamofu_active = 1'b0;
		tb_stamofu_oldest_ROB_index = 7'h0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(negedge CLK);

		// outputs:

	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		expected_ldu_mq_enq_ready = 1'b1;
		expected_ldu_mq_enq_index = 2'h0;
	    // second try
		expected_second_try_bank0_valid = 1'b0;
		expected_second_try_bank1_valid = 1'b0;
		expected_second_try_do_mispred = 1'b0;
		expected_second_try_is_mq = 1'b1;
		expected_second_try_misaligned = 1'b1;
		expected_second_try_page_fault = 1'b0;
		expected_second_try_access_fault = 1'b0;
		expected_second_try_is_mem = 1'b0;
		expected_second_try_PPN = 32'h0;
		expected_second_try_PO_word = 10'h0;
		expected_second_try_byte_mask = 4'b0000;
		expected_second_try_cq_index = 'h0;
		expected_second_try_mq_index = 2'h0;
	    // second try feedback
	    // misaligned queue data try req
		expected_ldu_mq_data_try_req_valid = 1'b0;
		expected_ldu_mq_data_try_cq_index = 'h0;
	    // misaligned queue info grab
		expected_ldu_mq_info_grab_data_try_req = 1'b0;
		expected_ldu_mq_info_grab_data = 32'h0;
	    // misaligned queue info ret
	    // dtlb miss resp
	    // dcache miss resp
	    // stamofu CAM return
	    // ldu CAM launch
	    // ldu CAM return
		expected_ldu_CAM_return_forward = 1'b0;
	    // ldu_mq commit
		expected_ldu_cq_commit_mq_has_forward = 1'b0;
	    // store set CAM update
		expected_ssu_CAM_update_valid = 1'b0;
		expected_ssu_CAM_update_ld_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_ld_ROB_index = 7'h0;
		expected_ssu_CAM_update_stamo_mdp_info = 8'b00000000;
		expected_ssu_CAM_update_stamo_ROB_index = 7'h0;
	    // acquire advertisement
	    // oldest stamofu advertisement
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