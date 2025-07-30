/*
    Filename: stamofu_mq_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_mq module. 
    Spec: LOROF/spec/design/stamofu_mq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter STAMOFU_MQ_ENTRIES = 4;
parameter LOG_STAMOFU_MQ_ENTRIES = $clog2(STAMOFU_MQ_ENTRIES);

module stamofu_mq_tb ();

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
	logic tb_stamofu_mq_enq_valid;

    // misaligned queue enqueue feedback
	logic DUT_stamofu_mq_enq_ready, expected_stamofu_mq_enq_ready;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] DUT_stamofu_mq_enq_index, expected_stamofu_mq_enq_index;

    // misaligned queue info ret
	logic tb_stamofu_mq_info_ret_bank0_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank0_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank0_mq_index;
	logic tb_stamofu_mq_info_ret_bank0_dtlb_hit;
	logic tb_stamofu_mq_info_ret_bank0_page_fault;
	logic tb_stamofu_mq_info_ret_bank0_access_fault;
	logic tb_stamofu_mq_info_ret_bank0_is_mem;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_mq_info_ret_bank0_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank0_ROB_index;
	logic [PA_WIDTH-2-1:0] tb_stamofu_mq_info_ret_bank0_PA_word;
	logic [3:0] tb_stamofu_mq_info_ret_bank0_byte_mask;
	logic [31:0] tb_stamofu_mq_info_ret_bank0_data;

	logic tb_stamofu_mq_info_ret_bank1_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank1_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank1_mq_index;
	logic tb_stamofu_mq_info_ret_bank1_dtlb_hit;
	logic tb_stamofu_mq_info_ret_bank1_page_fault;
	logic tb_stamofu_mq_info_ret_bank1_access_fault;
	logic tb_stamofu_mq_info_ret_bank1_is_mem;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_mq_info_ret_bank1_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_mq_info_ret_bank1_ROB_index;
	logic [PA_WIDTH-2-1:0] tb_stamofu_mq_info_ret_bank1_PA_word;
	logic [3:0] tb_stamofu_mq_info_ret_bank1_byte_mask;
	logic [31:0] tb_stamofu_mq_info_ret_bank1_data;

    // dtlb miss resp
	logic tb_dtlb_miss_resp_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_dtlb_miss_resp_cq_index;
	logic tb_dtlb_miss_resp_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_dtlb_miss_resp_mq_index;
	logic [PPN_WIDTH-1:0] tb_dtlb_miss_resp_PPN;
	logic tb_dtlb_miss_resp_is_mem;
	logic tb_dtlb_miss_resp_page_fault;
	logic tb_dtlb_miss_resp_access_fault;

    // ldu CAM launch from stamofu_mq
	logic DUT_stamofu_mq_ldu_CAM_launch_valid, expected_stamofu_mq_ldu_CAM_launch_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_mq_ldu_CAM_launch_cq_index, expected_stamofu_mq_ldu_CAM_launch_cq_index;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] DUT_stamofu_mq_ldu_CAM_launch_mq_index, expected_stamofu_mq_ldu_CAM_launch_mq_index;
	logic [PA_WIDTH-2-1:0] DUT_stamofu_mq_ldu_CAM_launch_PA_word, expected_stamofu_mq_ldu_CAM_launch_PA_word;
	logic [3:0] DUT_stamofu_mq_ldu_CAM_launch_byte_mask, expected_stamofu_mq_ldu_CAM_launch_byte_mask;
	logic [31:0] DUT_stamofu_mq_ldu_CAM_launch_write_data, expected_stamofu_mq_ldu_CAM_launch_write_data;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_mq_ldu_CAM_launch_mdp_info, expected_stamofu_mq_ldu_CAM_launch_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_mq_ldu_CAM_launch_ROB_index, expected_stamofu_mq_ldu_CAM_launch_ROB_index;

    // ldu CAM return
	logic tb_ldu_CAM_return_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_ldu_CAM_return_cq_index;
	logic tb_ldu_CAM_return_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_ldu_CAM_return_mq_index;
	logic tb_ldu_CAM_return_forward;

    // stamofu CAM launch
	logic tb_stamofu_CAM_launch_bank0_valid;
	logic [PA_WIDTH-2-1:0] tb_stamofu_CAM_launch_bank0_PA_word;
	logic [3:0] tb_stamofu_CAM_launch_bank0_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_CAM_launch_bank0_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_CAM_launch_bank0_mdp_info;

	logic tb_stamofu_CAM_launch_bank1_valid;
	logic [PA_WIDTH-2-1:0] tb_stamofu_CAM_launch_bank1_PA_word;
	logic [3:0] tb_stamofu_CAM_launch_bank1_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_CAM_launch_bank1_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_CAM_launch_bank1_mdp_info;

    // stamofu_mq CAM stage 2 info
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_mq_CAM_return_bank0_cq_index, expected_stamofu_mq_CAM_return_bank0_cq_index;
	logic DUT_stamofu_mq_CAM_return_bank0_stall, expected_stamofu_mq_CAM_return_bank0_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_mq_CAM_return_bank0_stall_count, expected_stamofu_mq_CAM_return_bank0_stall_count;
	logic [3:0] DUT_stamofu_mq_CAM_return_bank0_forward, expected_stamofu_mq_CAM_return_bank0_forward;
	logic DUT_stamofu_mq_CAM_return_bank0_nasty_forward, expected_stamofu_mq_CAM_return_bank0_nasty_forward;
	logic DUT_stamofu_mq_CAM_return_bank0_forward_ROB_index, expected_stamofu_mq_CAM_return_bank0_forward_ROB_index;
	logic [31:0] DUT_stamofu_mq_CAM_return_bank0_forward_data, expected_stamofu_mq_CAM_return_bank0_forward_data;

	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_mq_CAM_return_bank1_cq_index, expected_stamofu_mq_CAM_return_bank1_cq_index;
	logic DUT_stamofu_mq_CAM_return_bank1_stall, expected_stamofu_mq_CAM_return_bank1_stall;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_mq_CAM_return_bank1_stall_count, expected_stamofu_mq_CAM_return_bank1_stall_count;
	logic [3:0] DUT_stamofu_mq_CAM_return_bank1_forward, expected_stamofu_mq_CAM_return_bank1_forward;
	logic DUT_stamofu_mq_CAM_return_bank1_nasty_forward, expected_stamofu_mq_CAM_return_bank1_nasty_forward;
	logic DUT_stamofu_mq_CAM_return_bank1_forward_ROB_index, expected_stamofu_mq_CAM_return_bank1_forward_ROB_index;
	logic [31:0] DUT_stamofu_mq_CAM_return_bank1_forward_data, expected_stamofu_mq_CAM_return_bank1_forward_data;

    // misaligned queue info grab
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_stamofu_mq_info_grab_mq_index;
	logic tb_stamofu_mq_info_grab_clear_entry;
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
	logic DUT_stamofu_mq_info_grab_is_mem, expected_stamofu_mq_info_grab_is_mem;
	logic [PA_WIDTH-2-1:0] DUT_stamofu_mq_info_grab_PA_word, expected_stamofu_mq_info_grab_PA_word;
	logic [3:0] DUT_stamofu_mq_info_grab_byte_mask, expected_stamofu_mq_info_grab_byte_mask;
	logic [31:0] DUT_stamofu_mq_info_grab_data, expected_stamofu_mq_info_grab_data;

    // stamofu mq complete notif
	logic DUT_stamofu_mq_complete_valid, expected_stamofu_mq_complete_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_mq_complete_cq_index, expected_stamofu_mq_complete_cq_index;

    // ROB kill
        // this doesn't affect behavior (for now), but track anyway
	logic tb_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_mq #(
		.STAMOFU_MQ_ENTRIES(STAMOFU_MQ_ENTRIES),
		.LOG_STAMOFU_MQ_ENTRIES(LOG_STAMOFU_MQ_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to misaligned queue
		.stamofu_mq_enq_valid(tb_stamofu_mq_enq_valid),

	    // misaligned queue enqueue feedback
		.stamofu_mq_enq_ready(DUT_stamofu_mq_enq_ready),
		.stamofu_mq_enq_index(DUT_stamofu_mq_enq_index),

	    // misaligned queue info ret
		.stamofu_mq_info_ret_bank0_valid(tb_stamofu_mq_info_ret_bank0_valid),
		.stamofu_mq_info_ret_bank0_cq_index(tb_stamofu_mq_info_ret_bank0_cq_index),
		.stamofu_mq_info_ret_bank0_mq_index(tb_stamofu_mq_info_ret_bank0_mq_index),
		.stamofu_mq_info_ret_bank0_dtlb_hit(tb_stamofu_mq_info_ret_bank0_dtlb_hit),
		.stamofu_mq_info_ret_bank0_page_fault(tb_stamofu_mq_info_ret_bank0_page_fault),
		.stamofu_mq_info_ret_bank0_access_fault(tb_stamofu_mq_info_ret_bank0_access_fault),
		.stamofu_mq_info_ret_bank0_is_mem(tb_stamofu_mq_info_ret_bank0_is_mem),
		.stamofu_mq_info_ret_bank0_mdp_info(tb_stamofu_mq_info_ret_bank0_mdp_info),
		.stamofu_mq_info_ret_bank0_ROB_index(tb_stamofu_mq_info_ret_bank0_ROB_index),
		.stamofu_mq_info_ret_bank0_PA_word(tb_stamofu_mq_info_ret_bank0_PA_word),
		.stamofu_mq_info_ret_bank0_byte_mask(tb_stamofu_mq_info_ret_bank0_byte_mask),
		.stamofu_mq_info_ret_bank0_data(tb_stamofu_mq_info_ret_bank0_data),

		.stamofu_mq_info_ret_bank1_valid(tb_stamofu_mq_info_ret_bank1_valid),
		.stamofu_mq_info_ret_bank1_cq_index(tb_stamofu_mq_info_ret_bank1_cq_index),
		.stamofu_mq_info_ret_bank1_mq_index(tb_stamofu_mq_info_ret_bank1_mq_index),
		.stamofu_mq_info_ret_bank1_dtlb_hit(tb_stamofu_mq_info_ret_bank1_dtlb_hit),
		.stamofu_mq_info_ret_bank1_page_fault(tb_stamofu_mq_info_ret_bank1_page_fault),
		.stamofu_mq_info_ret_bank1_access_fault(tb_stamofu_mq_info_ret_bank1_access_fault),
		.stamofu_mq_info_ret_bank1_is_mem(tb_stamofu_mq_info_ret_bank1_is_mem),
		.stamofu_mq_info_ret_bank1_mdp_info(tb_stamofu_mq_info_ret_bank1_mdp_info),
		.stamofu_mq_info_ret_bank1_ROB_index(tb_stamofu_mq_info_ret_bank1_ROB_index),
		.stamofu_mq_info_ret_bank1_PA_word(tb_stamofu_mq_info_ret_bank1_PA_word),
		.stamofu_mq_info_ret_bank1_byte_mask(tb_stamofu_mq_info_ret_bank1_byte_mask),
		.stamofu_mq_info_ret_bank1_data(tb_stamofu_mq_info_ret_bank1_data),

	    // dtlb miss resp
		.dtlb_miss_resp_valid(tb_dtlb_miss_resp_valid),
		.dtlb_miss_resp_cq_index(tb_dtlb_miss_resp_cq_index),
		.dtlb_miss_resp_is_mq(tb_dtlb_miss_resp_is_mq),
		.dtlb_miss_resp_mq_index(tb_dtlb_miss_resp_mq_index),
		.dtlb_miss_resp_PPN(tb_dtlb_miss_resp_PPN),
		.dtlb_miss_resp_is_mem(tb_dtlb_miss_resp_is_mem),
		.dtlb_miss_resp_page_fault(tb_dtlb_miss_resp_page_fault),
		.dtlb_miss_resp_access_fault(tb_dtlb_miss_resp_access_fault),

	    // ldu CAM launch from stamofu_mq
		.stamofu_mq_ldu_CAM_launch_valid(DUT_stamofu_mq_ldu_CAM_launch_valid),
		.stamofu_mq_ldu_CAM_launch_cq_index(DUT_stamofu_mq_ldu_CAM_launch_cq_index),
		.stamofu_mq_ldu_CAM_launch_mq_index(DUT_stamofu_mq_ldu_CAM_launch_mq_index),
		.stamofu_mq_ldu_CAM_launch_PA_word(DUT_stamofu_mq_ldu_CAM_launch_PA_word),
		.stamofu_mq_ldu_CAM_launch_byte_mask(DUT_stamofu_mq_ldu_CAM_launch_byte_mask),
		.stamofu_mq_ldu_CAM_launch_write_data(DUT_stamofu_mq_ldu_CAM_launch_write_data),
		.stamofu_mq_ldu_CAM_launch_mdp_info(DUT_stamofu_mq_ldu_CAM_launch_mdp_info),
		.stamofu_mq_ldu_CAM_launch_ROB_index(DUT_stamofu_mq_ldu_CAM_launch_ROB_index),

	    // ldu CAM return
		.ldu_CAM_return_valid(tb_ldu_CAM_return_valid),
		.ldu_CAM_return_cq_index(tb_ldu_CAM_return_cq_index),
		.ldu_CAM_return_is_mq(tb_ldu_CAM_return_is_mq),
		.ldu_CAM_return_mq_index(tb_ldu_CAM_return_mq_index),
		.ldu_CAM_return_forward(tb_ldu_CAM_return_forward),

	    // stamofu CAM launch
		.stamofu_CAM_launch_bank0_valid(tb_stamofu_CAM_launch_bank0_valid),
		.stamofu_CAM_launch_bank0_PA_word(tb_stamofu_CAM_launch_bank0_PA_word),
		.stamofu_CAM_launch_bank0_byte_mask(tb_stamofu_CAM_launch_bank0_byte_mask),
		.stamofu_CAM_launch_bank0_ROB_index(tb_stamofu_CAM_launch_bank0_ROB_index),
		.stamofu_CAM_launch_bank0_mdp_info(tb_stamofu_CAM_launch_bank0_mdp_info),

		.stamofu_CAM_launch_bank1_valid(tb_stamofu_CAM_launch_bank1_valid),
		.stamofu_CAM_launch_bank1_PA_word(tb_stamofu_CAM_launch_bank1_PA_word),
		.stamofu_CAM_launch_bank1_byte_mask(tb_stamofu_CAM_launch_bank1_byte_mask),
		.stamofu_CAM_launch_bank1_ROB_index(tb_stamofu_CAM_launch_bank1_ROB_index),
		.stamofu_CAM_launch_bank1_mdp_info(tb_stamofu_CAM_launch_bank1_mdp_info),

	    // stamofu_mq CAM stage 2 info
		.stamofu_mq_CAM_return_bank0_cq_index(DUT_stamofu_mq_CAM_return_bank0_cq_index),
		.stamofu_mq_CAM_return_bank0_stall(DUT_stamofu_mq_CAM_return_bank0_stall),
		.stamofu_mq_CAM_return_bank0_stall_count(DUT_stamofu_mq_CAM_return_bank0_stall_count),
		.stamofu_mq_CAM_return_bank0_forward(DUT_stamofu_mq_CAM_return_bank0_forward),
		.stamofu_mq_CAM_return_bank0_nasty_forward(DUT_stamofu_mq_CAM_return_bank0_nasty_forward),
		.stamofu_mq_CAM_return_bank0_forward_ROB_index(DUT_stamofu_mq_CAM_return_bank0_forward_ROB_index),
		.stamofu_mq_CAM_return_bank0_forward_data(DUT_stamofu_mq_CAM_return_bank0_forward_data),

		.stamofu_mq_CAM_return_bank1_cq_index(DUT_stamofu_mq_CAM_return_bank1_cq_index),
		.stamofu_mq_CAM_return_bank1_stall(DUT_stamofu_mq_CAM_return_bank1_stall),
		.stamofu_mq_CAM_return_bank1_stall_count(DUT_stamofu_mq_CAM_return_bank1_stall_count),
		.stamofu_mq_CAM_return_bank1_forward(DUT_stamofu_mq_CAM_return_bank1_forward),
		.stamofu_mq_CAM_return_bank1_nasty_forward(DUT_stamofu_mq_CAM_return_bank1_nasty_forward),
		.stamofu_mq_CAM_return_bank1_forward_ROB_index(DUT_stamofu_mq_CAM_return_bank1_forward_ROB_index),
		.stamofu_mq_CAM_return_bank1_forward_data(DUT_stamofu_mq_CAM_return_bank1_forward_data),

	    // misaligned queue info grab
		.stamofu_mq_info_grab_mq_index(tb_stamofu_mq_info_grab_mq_index),
		.stamofu_mq_info_grab_clear_entry(tb_stamofu_mq_info_grab_clear_entry),
	        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
		.stamofu_mq_info_grab_is_mem(DUT_stamofu_mq_info_grab_is_mem),
		.stamofu_mq_info_grab_PA_word(DUT_stamofu_mq_info_grab_PA_word),
		.stamofu_mq_info_grab_byte_mask(DUT_stamofu_mq_info_grab_byte_mask),
		.stamofu_mq_info_grab_data(DUT_stamofu_mq_info_grab_data),

	    // stamofu mq complete notif
		.stamofu_mq_complete_valid(DUT_stamofu_mq_complete_valid),
		.stamofu_mq_complete_cq_index(DUT_stamofu_mq_complete_cq_index),

	    // ROB kill
	        // this doesn't affect behavior (for now), but track anyway
		.rob_kill_valid(tb_rob_kill_valid),
		.rob_kill_abs_head_index(tb_rob_kill_abs_head_index),
		.rob_kill_rel_kill_younger_index(tb_rob_kill_rel_kill_younger_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_stamofu_mq_enq_ready !== DUT_stamofu_mq_enq_ready) begin
			$display("TB ERROR: expected_stamofu_mq_enq_ready (%h) != DUT_stamofu_mq_enq_ready (%h)",
				expected_stamofu_mq_enq_ready, DUT_stamofu_mq_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_enq_index !== DUT_stamofu_mq_enq_index) begin
			$display("TB ERROR: expected_stamofu_mq_enq_index (%h) != DUT_stamofu_mq_enq_index (%h)",
				expected_stamofu_mq_enq_index, DUT_stamofu_mq_enq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_valid !== DUT_stamofu_mq_ldu_CAM_launch_valid) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_valid (%h) != DUT_stamofu_mq_ldu_CAM_launch_valid (%h)",
				expected_stamofu_mq_ldu_CAM_launch_valid, DUT_stamofu_mq_ldu_CAM_launch_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_cq_index !== DUT_stamofu_mq_ldu_CAM_launch_cq_index) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_cq_index (%h) != DUT_stamofu_mq_ldu_CAM_launch_cq_index (%h)",
				expected_stamofu_mq_ldu_CAM_launch_cq_index, DUT_stamofu_mq_ldu_CAM_launch_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_mq_index !== DUT_stamofu_mq_ldu_CAM_launch_mq_index) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_mq_index (%h) != DUT_stamofu_mq_ldu_CAM_launch_mq_index (%h)",
				expected_stamofu_mq_ldu_CAM_launch_mq_index, DUT_stamofu_mq_ldu_CAM_launch_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_PA_word !== DUT_stamofu_mq_ldu_CAM_launch_PA_word) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_PA_word (%h) != DUT_stamofu_mq_ldu_CAM_launch_PA_word (%h)",
				expected_stamofu_mq_ldu_CAM_launch_PA_word, DUT_stamofu_mq_ldu_CAM_launch_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_byte_mask !== DUT_stamofu_mq_ldu_CAM_launch_byte_mask) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_byte_mask (%h) != DUT_stamofu_mq_ldu_CAM_launch_byte_mask (%h)",
				expected_stamofu_mq_ldu_CAM_launch_byte_mask, DUT_stamofu_mq_ldu_CAM_launch_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_write_data !== DUT_stamofu_mq_ldu_CAM_launch_write_data) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_write_data (%h) != DUT_stamofu_mq_ldu_CAM_launch_write_data (%h)",
				expected_stamofu_mq_ldu_CAM_launch_write_data, DUT_stamofu_mq_ldu_CAM_launch_write_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_mdp_info !== DUT_stamofu_mq_ldu_CAM_launch_mdp_info) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_mdp_info (%h) != DUT_stamofu_mq_ldu_CAM_launch_mdp_info (%h)",
				expected_stamofu_mq_ldu_CAM_launch_mdp_info, DUT_stamofu_mq_ldu_CAM_launch_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_ldu_CAM_launch_ROB_index !== DUT_stamofu_mq_ldu_CAM_launch_ROB_index) begin
			$display("TB ERROR: expected_stamofu_mq_ldu_CAM_launch_ROB_index (%h) != DUT_stamofu_mq_ldu_CAM_launch_ROB_index (%h)",
				expected_stamofu_mq_ldu_CAM_launch_ROB_index, DUT_stamofu_mq_ldu_CAM_launch_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank0_cq_index !== DUT_stamofu_mq_CAM_return_bank0_cq_index) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank0_cq_index (%h) != DUT_stamofu_mq_CAM_return_bank0_cq_index (%h)",
				expected_stamofu_mq_CAM_return_bank0_cq_index, DUT_stamofu_mq_CAM_return_bank0_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank0_stall !== DUT_stamofu_mq_CAM_return_bank0_stall) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank0_stall (%h) != DUT_stamofu_mq_CAM_return_bank0_stall (%h)",
				expected_stamofu_mq_CAM_return_bank0_stall, DUT_stamofu_mq_CAM_return_bank0_stall);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank0_stall_count !== DUT_stamofu_mq_CAM_return_bank0_stall_count) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank0_stall_count (%h) != DUT_stamofu_mq_CAM_return_bank0_stall_count (%h)",
				expected_stamofu_mq_CAM_return_bank0_stall_count, DUT_stamofu_mq_CAM_return_bank0_stall_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank0_forward !== DUT_stamofu_mq_CAM_return_bank0_forward) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank0_forward (%h) != DUT_stamofu_mq_CAM_return_bank0_forward (%h)",
				expected_stamofu_mq_CAM_return_bank0_forward, DUT_stamofu_mq_CAM_return_bank0_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank0_nasty_forward !== DUT_stamofu_mq_CAM_return_bank0_nasty_forward) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank0_nasty_forward (%h) != DUT_stamofu_mq_CAM_return_bank0_nasty_forward (%h)",
				expected_stamofu_mq_CAM_return_bank0_nasty_forward, DUT_stamofu_mq_CAM_return_bank0_nasty_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank0_forward_ROB_index !== DUT_stamofu_mq_CAM_return_bank0_forward_ROB_index) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank0_forward_ROB_index (%h) != DUT_stamofu_mq_CAM_return_bank0_forward_ROB_index (%h)",
				expected_stamofu_mq_CAM_return_bank0_forward_ROB_index, DUT_stamofu_mq_CAM_return_bank0_forward_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank0_forward_data !== DUT_stamofu_mq_CAM_return_bank0_forward_data) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank0_forward_data (%h) != DUT_stamofu_mq_CAM_return_bank0_forward_data (%h)",
				expected_stamofu_mq_CAM_return_bank0_forward_data, DUT_stamofu_mq_CAM_return_bank0_forward_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank1_cq_index !== DUT_stamofu_mq_CAM_return_bank1_cq_index) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank1_cq_index (%h) != DUT_stamofu_mq_CAM_return_bank1_cq_index (%h)",
				expected_stamofu_mq_CAM_return_bank1_cq_index, DUT_stamofu_mq_CAM_return_bank1_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank1_stall !== DUT_stamofu_mq_CAM_return_bank1_stall) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank1_stall (%h) != DUT_stamofu_mq_CAM_return_bank1_stall (%h)",
				expected_stamofu_mq_CAM_return_bank1_stall, DUT_stamofu_mq_CAM_return_bank1_stall);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank1_stall_count !== DUT_stamofu_mq_CAM_return_bank1_stall_count) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank1_stall_count (%h) != DUT_stamofu_mq_CAM_return_bank1_stall_count (%h)",
				expected_stamofu_mq_CAM_return_bank1_stall_count, DUT_stamofu_mq_CAM_return_bank1_stall_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank1_forward !== DUT_stamofu_mq_CAM_return_bank1_forward) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank1_forward (%h) != DUT_stamofu_mq_CAM_return_bank1_forward (%h)",
				expected_stamofu_mq_CAM_return_bank1_forward, DUT_stamofu_mq_CAM_return_bank1_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank1_nasty_forward !== DUT_stamofu_mq_CAM_return_bank1_nasty_forward) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank1_nasty_forward (%h) != DUT_stamofu_mq_CAM_return_bank1_nasty_forward (%h)",
				expected_stamofu_mq_CAM_return_bank1_nasty_forward, DUT_stamofu_mq_CAM_return_bank1_nasty_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank1_forward_ROB_index !== DUT_stamofu_mq_CAM_return_bank1_forward_ROB_index) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank1_forward_ROB_index (%h) != DUT_stamofu_mq_CAM_return_bank1_forward_ROB_index (%h)",
				expected_stamofu_mq_CAM_return_bank1_forward_ROB_index, DUT_stamofu_mq_CAM_return_bank1_forward_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_CAM_return_bank1_forward_data !== DUT_stamofu_mq_CAM_return_bank1_forward_data) begin
			$display("TB ERROR: expected_stamofu_mq_CAM_return_bank1_forward_data (%h) != DUT_stamofu_mq_CAM_return_bank1_forward_data (%h)",
				expected_stamofu_mq_CAM_return_bank1_forward_data, DUT_stamofu_mq_CAM_return_bank1_forward_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_grab_is_mem !== DUT_stamofu_mq_info_grab_is_mem) begin
			$display("TB ERROR: expected_stamofu_mq_info_grab_is_mem (%h) != DUT_stamofu_mq_info_grab_is_mem (%h)",
				expected_stamofu_mq_info_grab_is_mem, DUT_stamofu_mq_info_grab_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_grab_PA_word !== DUT_stamofu_mq_info_grab_PA_word) begin
			$display("TB ERROR: expected_stamofu_mq_info_grab_PA_word (%h) != DUT_stamofu_mq_info_grab_PA_word (%h)",
				expected_stamofu_mq_info_grab_PA_word, DUT_stamofu_mq_info_grab_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_grab_byte_mask !== DUT_stamofu_mq_info_grab_byte_mask) begin
			$display("TB ERROR: expected_stamofu_mq_info_grab_byte_mask (%h) != DUT_stamofu_mq_info_grab_byte_mask (%h)",
				expected_stamofu_mq_info_grab_byte_mask, DUT_stamofu_mq_info_grab_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_grab_data !== DUT_stamofu_mq_info_grab_data) begin
			$display("TB ERROR: expected_stamofu_mq_info_grab_data (%h) != DUT_stamofu_mq_info_grab_data (%h)",
				expected_stamofu_mq_info_grab_data, DUT_stamofu_mq_info_grab_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_complete_valid !== DUT_stamofu_mq_complete_valid) begin
			$display("TB ERROR: expected_stamofu_mq_complete_valid (%h) != DUT_stamofu_mq_complete_valid (%h)",
				expected_stamofu_mq_complete_valid, DUT_stamofu_mq_complete_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_complete_cq_index !== DUT_stamofu_mq_complete_cq_index) begin
			$display("TB ERROR: expected_stamofu_mq_complete_cq_index (%h) != DUT_stamofu_mq_complete_cq_index (%h)",
				expected_stamofu_mq_complete_cq_index, DUT_stamofu_mq_complete_cq_index);
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
		tb_stamofu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // misaligned queue info ret
		tb_stamofu_mq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank0_cq_index = 0;
		tb_stamofu_mq_info_ret_bank0_mq_index = 0;
		tb_stamofu_mq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_stamofu_mq_info_ret_bank0_page_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank0_access_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank0_is_mem = 1'b0;
		tb_stamofu_mq_info_ret_bank0_mdp_info = 8'h00;
		tb_stamofu_mq_info_ret_bank0_ROB_index = 7'h00;
		tb_stamofu_mq_info_ret_bank0_PA_word = 32'h00000000;
		tb_stamofu_mq_info_ret_bank0_byte_mask = 4'b0000;
		tb_stamofu_mq_info_ret_bank0_data = 32'h00000000;
		tb_stamofu_mq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank1_cq_index = 0;
		tb_stamofu_mq_info_ret_bank1_mq_index = 0;
		tb_stamofu_mq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_stamofu_mq_info_ret_bank1_page_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank1_access_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank1_is_mem = 1'b0;
		tb_stamofu_mq_info_ret_bank1_mdp_info = 8'h00;
		tb_stamofu_mq_info_ret_bank1_ROB_index = 7'h00;
		tb_stamofu_mq_info_ret_bank1_PA_word = 32'h00000000;
		tb_stamofu_mq_info_ret_bank1_byte_mask = 4'b0000;
		tb_stamofu_mq_info_ret_bank1_data = 32'h00000000;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // ldu CAM launch from stamofu_mq
	    // ldu CAM return
		tb_ldu_CAM_return_valid = 1'b0;
		tb_ldu_CAM_return_cq_index = 0;
		tb_ldu_CAM_return_is_mq = 1'b0;
		tb_ldu_CAM_return_mq_index = 0;
		tb_ldu_CAM_return_forward = 1'b0;
	    // stamofu CAM launch
		tb_stamofu_CAM_launch_bank0_valid = 1'b0;
		tb_stamofu_CAM_launch_bank0_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank0_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank0_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank0_mdp_info = 8'h00;
		tb_stamofu_CAM_launch_bank1_valid = 1'b0;
		tb_stamofu_CAM_launch_bank1_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank1_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank1_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank1_mdp_info = 8'h00;
	    // stamofu_mq CAM stage 2 info
	    // misaligned queue info grab
		tb_stamofu_mq_info_grab_mq_index = 0;
		tb_stamofu_mq_info_grab_clear_entry = 1'b0;
	    // stamofu mq complete notif
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		expected_stamofu_mq_enq_ready = 1'b1;
		expected_stamofu_mq_enq_index = 0;
	    // misaligned queue info ret
	    // dtlb miss resp
	    // ldu CAM launch from stamofu_mq
		expected_stamofu_mq_ldu_CAM_launch_valid = 1'b0;
		expected_stamofu_mq_ldu_CAM_launch_cq_index = 0;
		expected_stamofu_mq_ldu_CAM_launch_mq_index = 0;
		expected_stamofu_mq_ldu_CAM_launch_PA_word = 32'h00000000;
		expected_stamofu_mq_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_mq_ldu_CAM_launch_write_data = 32'h00000000;
		expected_stamofu_mq_ldu_CAM_launch_mdp_info = 8'h00;
		expected_stamofu_mq_ldu_CAM_launch_ROB_index = 7'h00;
	    // ldu CAM return
	    // stamofu CAM launch
	    // stamofu_mq CAM stage 2 info
		expected_stamofu_mq_CAM_return_bank0_cq_index = 0;
		expected_stamofu_mq_CAM_return_bank0_stall = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_stall_count = 0;
		expected_stamofu_mq_CAM_return_bank0_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_nasty_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_forward_ROB_index = 7'h00;
		expected_stamofu_mq_CAM_return_bank0_forward_data = 32'h00000000;
		expected_stamofu_mq_CAM_return_bank1_cq_index = 0;
		expected_stamofu_mq_CAM_return_bank1_stall = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_stall_count = 0;
		expected_stamofu_mq_CAM_return_bank1_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_nasty_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_forward_ROB_index = 7'h00;
		expected_stamofu_mq_CAM_return_bank1_forward_data = 32'h00000000;
	    // misaligned queue info grab
		expected_stamofu_mq_info_grab_is_mem = 1'b0;
		expected_stamofu_mq_info_grab_PA_word = 32'h00000000;
		expected_stamofu_mq_info_grab_byte_mask = 4'b0000;
		expected_stamofu_mq_info_grab_data = 32'h00000000;
	    // stamofu mq complete notif
		expected_stamofu_mq_complete_valid = 1'b0;
		expected_stamofu_mq_complete_cq_index = 0;
	    // ROB kill

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to misaligned queue
		tb_stamofu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // misaligned queue info ret
		tb_stamofu_mq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank0_cq_index = 0;
		tb_stamofu_mq_info_ret_bank0_mq_index = 0;
		tb_stamofu_mq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_stamofu_mq_info_ret_bank0_page_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank0_access_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank0_is_mem = 1'b0;
		tb_stamofu_mq_info_ret_bank0_mdp_info = 8'h00;
		tb_stamofu_mq_info_ret_bank0_ROB_index = 7'h00;
		tb_stamofu_mq_info_ret_bank0_PA_word = 32'h00000000;
		tb_stamofu_mq_info_ret_bank0_byte_mask = 4'b0000;
		tb_stamofu_mq_info_ret_bank0_data = 32'h00000000;
		tb_stamofu_mq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank1_cq_index = 0;
		tb_stamofu_mq_info_ret_bank1_mq_index = 0;
		tb_stamofu_mq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_stamofu_mq_info_ret_bank1_page_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank1_access_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank1_is_mem = 1'b0;
		tb_stamofu_mq_info_ret_bank1_mdp_info = 8'h00;
		tb_stamofu_mq_info_ret_bank1_ROB_index = 7'h00;
		tb_stamofu_mq_info_ret_bank1_PA_word = 32'h00000000;
		tb_stamofu_mq_info_ret_bank1_byte_mask = 4'b0000;
		tb_stamofu_mq_info_ret_bank1_data = 32'h00000000;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // ldu CAM launch from stamofu_mq
	    // ldu CAM return
		tb_ldu_CAM_return_valid = 1'b0;
		tb_ldu_CAM_return_cq_index = 0;
		tb_ldu_CAM_return_is_mq = 1'b0;
		tb_ldu_CAM_return_mq_index = 0;
		tb_ldu_CAM_return_forward = 1'b0;
	    // stamofu CAM launch
		tb_stamofu_CAM_launch_bank0_valid = 1'b0;
		tb_stamofu_CAM_launch_bank0_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank0_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank0_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank0_mdp_info = 8'h00;
		tb_stamofu_CAM_launch_bank1_valid = 1'b0;
		tb_stamofu_CAM_launch_bank1_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank1_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank1_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank1_mdp_info = 8'h00;
	    // stamofu_mq CAM stage 2 info
	    // misaligned queue info grab
		tb_stamofu_mq_info_grab_mq_index = 0;
		tb_stamofu_mq_info_grab_clear_entry = 1'b0;
	    // stamofu mq complete notif
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		expected_stamofu_mq_enq_ready = 1'b1;
		expected_stamofu_mq_enq_index = 0;
	    // misaligned queue info ret
	    // dtlb miss resp
	    // ldu CAM launch from stamofu_mq
		expected_stamofu_mq_ldu_CAM_launch_valid = 1'b0;
		expected_stamofu_mq_ldu_CAM_launch_cq_index = 0;
		expected_stamofu_mq_ldu_CAM_launch_mq_index = 0;
		expected_stamofu_mq_ldu_CAM_launch_PA_word = 32'h00000000;
		expected_stamofu_mq_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_mq_ldu_CAM_launch_write_data = 32'h00000000;
		expected_stamofu_mq_ldu_CAM_launch_mdp_info = 8'h00;
		expected_stamofu_mq_ldu_CAM_launch_ROB_index = 7'h00;
	    // ldu CAM return
	    // stamofu CAM launch
	    // stamofu_mq CAM stage 2 info
		expected_stamofu_mq_CAM_return_bank0_cq_index = 0;
		expected_stamofu_mq_CAM_return_bank0_stall = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_stall_count = 0;
		expected_stamofu_mq_CAM_return_bank0_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_nasty_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_forward_ROB_index = 7'h00;
		expected_stamofu_mq_CAM_return_bank0_forward_data = 32'h00000000;
		expected_stamofu_mq_CAM_return_bank1_cq_index = 0;
		expected_stamofu_mq_CAM_return_bank1_stall = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_stall_count = 0;
		expected_stamofu_mq_CAM_return_bank1_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_nasty_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_forward_ROB_index = 7'h00;
		expected_stamofu_mq_CAM_return_bank1_forward_data = 32'h00000000;
	    // misaligned queue info grab
		expected_stamofu_mq_info_grab_is_mem = 1'b0;
		expected_stamofu_mq_info_grab_PA_word = 32'h00000000;
		expected_stamofu_mq_info_grab_byte_mask = 4'b0000;
		expected_stamofu_mq_info_grab_data = 32'h00000000;
	    // stamofu mq complete notif
		expected_stamofu_mq_complete_valid = 1'b0;
		expected_stamofu_mq_complete_cq_index = 0;
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
		tb_stamofu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // misaligned queue info ret
		tb_stamofu_mq_info_ret_bank0_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank0_cq_index = 0;
		tb_stamofu_mq_info_ret_bank0_mq_index = 0;
		tb_stamofu_mq_info_ret_bank0_dtlb_hit = 1'b0;
		tb_stamofu_mq_info_ret_bank0_page_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank0_access_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank0_is_mem = 1'b0;
		tb_stamofu_mq_info_ret_bank0_mdp_info = 8'h00;
		tb_stamofu_mq_info_ret_bank0_ROB_index = 7'h00;
		tb_stamofu_mq_info_ret_bank0_PA_word = 32'h00000000;
		tb_stamofu_mq_info_ret_bank0_byte_mask = 4'b0000;
		tb_stamofu_mq_info_ret_bank0_data = 32'h00000000;
		tb_stamofu_mq_info_ret_bank1_valid = 1'b0;
		tb_stamofu_mq_info_ret_bank1_cq_index = 0;
		tb_stamofu_mq_info_ret_bank1_mq_index = 0;
		tb_stamofu_mq_info_ret_bank1_dtlb_hit = 1'b0;
		tb_stamofu_mq_info_ret_bank1_page_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank1_access_fault = 1'b0;
		tb_stamofu_mq_info_ret_bank1_is_mem = 1'b0;
		tb_stamofu_mq_info_ret_bank1_mdp_info = 8'h00;
		tb_stamofu_mq_info_ret_bank1_ROB_index = 7'h00;
		tb_stamofu_mq_info_ret_bank1_PA_word = 32'h00000000;
		tb_stamofu_mq_info_ret_bank1_byte_mask = 4'b0000;
		tb_stamofu_mq_info_ret_bank1_data = 32'h00000000;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // ldu CAM launch from stamofu_mq
	    // ldu CAM return
		tb_ldu_CAM_return_valid = 1'b0;
		tb_ldu_CAM_return_cq_index = 0;
		tb_ldu_CAM_return_is_mq = 1'b0;
		tb_ldu_CAM_return_mq_index = 0;
		tb_ldu_CAM_return_forward = 1'b0;
	    // stamofu CAM launch
		tb_stamofu_CAM_launch_bank0_valid = 1'b0;
		tb_stamofu_CAM_launch_bank0_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank0_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank0_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank0_mdp_info = 8'h00;
		tb_stamofu_CAM_launch_bank1_valid = 1'b0;
		tb_stamofu_CAM_launch_bank1_PA_word = 32'h00000000;
		tb_stamofu_CAM_launch_bank1_byte_mask = 4'b0000;
		tb_stamofu_CAM_launch_bank1_ROB_index = 7'h00;
		tb_stamofu_CAM_launch_bank1_mdp_info = 8'h00;
	    // stamofu_mq CAM stage 2 info
	    // misaligned queue info grab
		tb_stamofu_mq_info_grab_mq_index = 0;
		tb_stamofu_mq_info_grab_clear_entry = 1'b0;
	    // stamofu mq complete notif
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(negedge CLK);

		// outputs:

	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		expected_stamofu_mq_enq_ready = 1'b1;
		expected_stamofu_mq_enq_index = 0;
	    // misaligned queue info ret
	    // dtlb miss resp
	    // ldu CAM launch from stamofu_mq
		expected_stamofu_mq_ldu_CAM_launch_valid = 1'b0;
		expected_stamofu_mq_ldu_CAM_launch_cq_index = 0;
		expected_stamofu_mq_ldu_CAM_launch_mq_index = 0;
		expected_stamofu_mq_ldu_CAM_launch_PA_word = 32'h00000000;
		expected_stamofu_mq_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_mq_ldu_CAM_launch_write_data = 32'h00000000;
		expected_stamofu_mq_ldu_CAM_launch_mdp_info = 8'h00;
		expected_stamofu_mq_ldu_CAM_launch_ROB_index = 7'h00;
	    // ldu CAM return
	    // stamofu CAM launch
	    // stamofu_mq CAM stage 2 info
		expected_stamofu_mq_CAM_return_bank0_cq_index = 0;
		expected_stamofu_mq_CAM_return_bank0_stall = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_stall_count = 0;
		expected_stamofu_mq_CAM_return_bank0_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_nasty_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank0_forward_ROB_index = 7'h00;
		expected_stamofu_mq_CAM_return_bank0_forward_data = 32'h00000000;
		expected_stamofu_mq_CAM_return_bank1_cq_index = 0;
		expected_stamofu_mq_CAM_return_bank1_stall = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_stall_count = 0;
		expected_stamofu_mq_CAM_return_bank1_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_nasty_forward = 1'b0;
		expected_stamofu_mq_CAM_return_bank1_forward_ROB_index = 7'h00;
		expected_stamofu_mq_CAM_return_bank1_forward_data = 32'h00000000;
	    // misaligned queue info grab
		expected_stamofu_mq_info_grab_is_mem = 1'b0;
		expected_stamofu_mq_info_grab_PA_word = 32'h00000000;
		expected_stamofu_mq_info_grab_byte_mask = 4'b0000;
		expected_stamofu_mq_info_grab_data = 32'h00000000;
	    // stamofu mq complete notif
		expected_stamofu_mq_complete_valid = 1'b0;
		expected_stamofu_mq_complete_cq_index = 0;
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