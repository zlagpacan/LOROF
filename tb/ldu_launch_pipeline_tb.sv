/*
    Filename: ldu_launch_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for ldu_launch_pipeline module. 
    Spec: LOROF/spec/design/ldu_launch_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module ldu_launch_pipeline_tb ();

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


    // first try
	logic tb_first_try_valid;
	logic tb_first_try_is_mq;
	logic tb_first_try_misaligned;
	logic [VPN_WIDTH-1:0] tb_first_try_VPN;
	logic [PO_WIDTH-3:0] tb_first_try_PO_word;
	logic [3:0] tb_first_try_byte_mask;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_first_try_cq_index;

    // first try feedback
	logic DUT_first_try_ack, expected_first_try_ack;

    // op enqueue to misaligned queue
	logic DUT_ldu_mq_enq_valid, expected_ldu_mq_enq_valid;

    // misaligned queue enqueue feedback
	logic tb_ldu_mq_enq_ready;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_ldu_mq_enq_index;

    // ROB info
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_abs_head_index;

    // acquire advertisement
	logic tb_stamofu_aq_mem_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_mem_aq_oldest_abs_ROB_index;
	logic tb_stamofu_aq_io_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_io_aq_oldest_abs_ROB_index;

    // second try
	logic tb_second_try_valid;
	logic tb_second_try_is_mq;
	logic tb_second_try_misaligned;
	logic tb_second_try_page_fault;
	logic tb_second_try_access_fault;
	logic tb_second_try_is_mem;
	logic [PPN_WIDTH-1:0] tb_second_try_PPN;
	logic [PO_WIDTH-3:0] tb_second_try_PO_word;
	logic [3:0] tb_second_try_byte_mask;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_second_try_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_second_try_mq_index;

    // second try feedback
	logic DUT_second_try_ack, expected_second_try_ack;

    // data try
	logic tb_data_try_valid;
	logic tb_data_try_do_mispred;
	logic [31:0] tb_data_try_data;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_data_try_cq_index;

    // data try feedback
	logic DUT_data_try_ack, expected_data_try_ack;

    // dtlb req
	logic DUT_dtlb_req_valid, expected_dtlb_req_valid;
	logic [1:0] DUT_dtlb_req_exec_mode, expected_dtlb_req_exec_mode;
	logic DUT_dtlb_req_virtual_mode, expected_dtlb_req_virtual_mode;
	logic [ASID_WIDTH-1:0] DUT_dtlb_req_ASID, expected_dtlb_req_ASID;
	logic DUT_dtlb_req_MXR, expected_dtlb_req_MXR;
	logic DUT_dtlb_req_SUM, expected_dtlb_req_SUM;
	logic [VPN_WIDTH-1:0] DUT_dtlb_req_VPN, expected_dtlb_req_VPN;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_dtlb_req_cq_index, expected_dtlb_req_cq_index;
	logic DUT_dtlb_req_is_mq, expected_dtlb_req_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_dtlb_req_mq_index, expected_dtlb_req_mq_index;

    // dtlb req feedback
	logic tb_dtlb_req_ready;

    // dtlb resp
	logic tb_dtlb_resp_hit;
	logic [PPN_WIDTH-1:0] tb_dtlb_resp_PPN;
	logic tb_dtlb_resp_is_mem;
	logic tb_dtlb_resp_page_fault;
	logic tb_dtlb_resp_access_fault;

    // dcache req
	logic DUT_dcache_req_valid, expected_dcache_req_valid;
	logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] DUT_dcache_req_block_offset, expected_dcache_req_block_offset;
	logic [DCACHE_INDEX_WIDTH-1:0] DUT_dcache_req_index, expected_dcache_req_index;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_dcache_req_cq_index, expected_dcache_req_cq_index;
	logic DUT_dcache_req_is_mq, expected_dcache_req_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_dcache_req_mq_index, expected_dcache_req_mq_index;

    // dcache req feedback
	logic tb_dcache_req_ready;

    // dcache resp
	logic [1:0] tb_dcache_resp_valid_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] tb_dcache_resp_tag_by_way;
	logic [1:0][31:0] tb_dcache_resp_data_by_way;

    // dcache resp feedback
	logic DUT_dcache_resp_hit_valid, expected_dcache_resp_hit_valid;
	logic DUT_dcache_resp_hit_way, expected_dcache_resp_hit_way;
	logic DUT_dcache_resp_miss_valid, expected_dcache_resp_miss_valid;
	logic [DCACHE_TAG_WIDTH-1:0] DUT_dcache_resp_miss_tag, expected_dcache_resp_miss_tag;

    // writeback data to PRF
	logic DUT_WB_valid, expected_WB_valid;
	logic [31:0] DUT_WB_data, expected_WB_data;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR, expected_WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_WB_ROB_index, expected_WB_ROB_index;

    // writeback backpressure from PRF
	logic tb_WB_ready;

    // CAM launch
	logic DUT_stamofu_CAM_launch_valid, expected_stamofu_CAM_launch_valid;
	logic [PA_WIDTH-2-1:0] DUT_stamofu_CAM_launch_PA_word, expected_stamofu_CAM_launch_PA_word;
	logic [3:0] DUT_stamofu_CAM_launch_byte_mask, expected_stamofu_CAM_launch_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_CAM_launch_ROB_index, expected_stamofu_CAM_launch_ROB_index;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_stamofu_CAM_launch_cq_index, expected_stamofu_CAM_launch_cq_index;
	logic DUT_stamofu_CAM_launch_is_mq, expected_stamofu_CAM_launch_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_stamofu_CAM_launch_mq_index, expected_stamofu_CAM_launch_mq_index;

    // central queue info grab
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_ldu_cq_info_grab_cq_index, expected_ldu_cq_info_grab_cq_index;
	logic [3:0] tb_ldu_cq_info_grab_op;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_cq_info_grab_mdp_info;
	logic [LOG_PR_COUNT-1:0] tb_ldu_cq_info_grab_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_cq_info_grab_ROB_index;

    // central queue info ret
	logic DUT_ldu_cq_info_ret_valid, expected_ldu_cq_info_ret_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_ldu_cq_info_ret_cq_index, expected_ldu_cq_info_ret_cq_index;
	logic DUT_ldu_cq_info_ret_misaligned, expected_ldu_cq_info_ret_misaligned;
	logic DUT_ldu_cq_info_ret_dtlb_hit, expected_ldu_cq_info_ret_dtlb_hit;
	logic DUT_ldu_cq_info_ret_page_fault, expected_ldu_cq_info_ret_page_fault;
	logic DUT_ldu_cq_info_ret_access_fault, expected_ldu_cq_info_ret_access_fault;
	logic DUT_ldu_cq_info_ret_dcache_hit, expected_ldu_cq_info_ret_dcache_hit;
	logic DUT_ldu_cq_info_ret_is_mem, expected_ldu_cq_info_ret_is_mem;
	logic DUT_ldu_cq_info_ret_aq_blocking, expected_ldu_cq_info_ret_aq_blocking;
	logic [PA_WIDTH-2-1:0] DUT_ldu_cq_info_ret_PA_word, expected_ldu_cq_info_ret_PA_word;
	logic [3:0] DUT_ldu_cq_info_ret_byte_mask, expected_ldu_cq_info_ret_byte_mask;
	logic [31:0] DUT_ldu_cq_info_ret_data, expected_ldu_cq_info_ret_data;

    // misaligned queue info ret
	logic DUT_ldu_mq_info_ret_valid, expected_ldu_mq_info_ret_valid;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_ldu_mq_info_ret_mq_index, expected_ldu_mq_info_ret_mq_index;
	logic DUT_ldu_mq_info_ret_dtlb_hit, expected_ldu_mq_info_ret_dtlb_hit;
	logic DUT_ldu_mq_info_ret_page_fault, expected_ldu_mq_info_ret_page_fault;
	logic DUT_ldu_mq_info_ret_access_fault, expected_ldu_mq_info_ret_access_fault;
	logic DUT_ldu_mq_info_ret_dcache_hit, expected_ldu_mq_info_ret_dcache_hit;
	logic DUT_ldu_mq_info_ret_is_mem, expected_ldu_mq_info_ret_is_mem;
	logic DUT_ldu_mq_info_ret_aq_blocking, expected_ldu_mq_info_ret_aq_blocking;
	logic [PA_WIDTH-2-1:0] DUT_ldu_mq_info_ret_PA_word, expected_ldu_mq_info_ret_PA_word;
	logic [3:0] DUT_ldu_mq_info_ret_byte_mask, expected_ldu_mq_info_ret_byte_mask;
	logic [31:0] DUT_ldu_mq_info_ret_data, expected_ldu_mq_info_ret_data;

    // misprediction notification to ROB
	logic DUT_mispred_notif_valid, expected_mispred_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] DUT_mispred_notif_ROB_index, expected_mispred_notif_ROB_index;

    // misprediction notification backpressure from ROB
	logic tb_mispred_notif_ready;

    // exception to ROB
	logic DUT_rob_exception_valid, expected_rob_exception_valid;
	logic [VA_WIDTH-1:0] DUT_rob_exception_VA, expected_rob_exception_VA;
	logic DUT_rob_exception_page_fault, expected_rob_exception_page_fault;
	logic DUT_rob_exception_access_fault, expected_rob_exception_access_fault;
	logic [LOG_ROB_ENTRIES-1:0] DUT_rob_exception_ROB_index, expected_rob_exception_ROB_index;

    // exception backpressure from ROB
	logic tb_rob_exception_ready;

    // restart from ROB
	logic tb_rob_restart_valid;
	logic [8:0] tb_rob_restart_ASID;
	logic [1:0] tb_rob_restart_exec_mode;
	logic tb_rob_restart_virtual_mode;
	logic tb_rob_restart_MXR;
	logic tb_rob_restart_SUM;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ldu_launch_pipeline #(
		.INIT_ASID(9'h0),
		.INIT_EXEC_MODE(M_MODE),
		.INIT_VIRTUAL_MODE(1'b0),
		.INIT_MXR(1'b0),
		.INIT_SUM(1'b0)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // first try
		.first_try_valid(tb_first_try_valid),
		.first_try_is_mq(tb_first_try_is_mq),
		.first_try_misaligned(tb_first_try_misaligned),
		.first_try_VPN(tb_first_try_VPN),
		.first_try_PO_word(tb_first_try_PO_word),
		.first_try_byte_mask(tb_first_try_byte_mask),
		.first_try_cq_index(tb_first_try_cq_index),

	    // first try feedback
		.first_try_ack(DUT_first_try_ack),

	    // op enqueue to misaligned queue
		.ldu_mq_enq_valid(DUT_ldu_mq_enq_valid),

	    // misaligned queue enqueue feedback
		.ldu_mq_enq_ready(tb_ldu_mq_enq_ready),
		.ldu_mq_enq_index(tb_ldu_mq_enq_index),

	    // ROB info
		.rob_abs_head_index(tb_rob_abs_head_index),

	    // acquire advertisement
		.stamofu_aq_mem_aq_active(tb_stamofu_aq_mem_aq_active),
		.stamofu_aq_mem_aq_oldest_abs_ROB_index(tb_stamofu_aq_mem_aq_oldest_abs_ROB_index),
		.stamofu_aq_io_aq_active(tb_stamofu_aq_io_aq_active),
		.stamofu_aq_io_aq_oldest_abs_ROB_index(tb_stamofu_aq_io_aq_oldest_abs_ROB_index),

	    // second try
		.second_try_valid(tb_second_try_valid),
		.second_try_is_mq(tb_second_try_is_mq),
		.second_try_misaligned(tb_second_try_misaligned),
		.second_try_page_fault(tb_second_try_page_fault),
		.second_try_access_fault(tb_second_try_access_fault),
		.second_try_is_mem(tb_second_try_is_mem),
		.second_try_PPN(tb_second_try_PPN),
		.second_try_PO_word(tb_second_try_PO_word),
		.second_try_byte_mask(tb_second_try_byte_mask),
		.second_try_cq_index(tb_second_try_cq_index),
		.second_try_mq_index(tb_second_try_mq_index),

	    // second try feedback
		.second_try_ack(DUT_second_try_ack),

	    // data try
		.data_try_valid(tb_data_try_valid),
		.data_try_do_mispred(tb_data_try_do_mispred),
		.data_try_data(tb_data_try_data),
		.data_try_cq_index(tb_data_try_cq_index),

	    // data try feedback
		.data_try_ack(DUT_data_try_ack),

	    // dtlb req
		.dtlb_req_valid(DUT_dtlb_req_valid),
		.dtlb_req_exec_mode(DUT_dtlb_req_exec_mode),
		.dtlb_req_virtual_mode(DUT_dtlb_req_virtual_mode),
		.dtlb_req_ASID(DUT_dtlb_req_ASID),
		.dtlb_req_MXR(DUT_dtlb_req_MXR),
		.dtlb_req_SUM(DUT_dtlb_req_SUM),
		.dtlb_req_VPN(DUT_dtlb_req_VPN),
		.dtlb_req_cq_index(DUT_dtlb_req_cq_index),
		.dtlb_req_is_mq(DUT_dtlb_req_is_mq),
		.dtlb_req_mq_index(DUT_dtlb_req_mq_index),

	    // dtlb req feedback
		.dtlb_req_ready(tb_dtlb_req_ready),

	    // dtlb resp
		.dtlb_resp_hit(tb_dtlb_resp_hit),
		.dtlb_resp_PPN(tb_dtlb_resp_PPN),
		.dtlb_resp_is_mem(tb_dtlb_resp_is_mem),
		.dtlb_resp_page_fault(tb_dtlb_resp_page_fault),
		.dtlb_resp_access_fault(tb_dtlb_resp_access_fault),

	    // dcache req
		.dcache_req_valid(DUT_dcache_req_valid),
		.dcache_req_block_offset(DUT_dcache_req_block_offset),
		.dcache_req_index(DUT_dcache_req_index),
		.dcache_req_cq_index(DUT_dcache_req_cq_index),
		.dcache_req_is_mq(DUT_dcache_req_is_mq),
		.dcache_req_mq_index(DUT_dcache_req_mq_index),

	    // dcache req feedback
		.dcache_req_ready(tb_dcache_req_ready),

	    // dcache resp
		.dcache_resp_valid_by_way(tb_dcache_resp_valid_by_way),
		.dcache_resp_tag_by_way(tb_dcache_resp_tag_by_way),
		.dcache_resp_data_by_way(tb_dcache_resp_data_by_way),

	    // dcache resp feedback
		.dcache_resp_hit_valid(DUT_dcache_resp_hit_valid),
		.dcache_resp_hit_way(DUT_dcache_resp_hit_way),
		.dcache_resp_miss_valid(DUT_dcache_resp_miss_valid),
		.dcache_resp_miss_tag(DUT_dcache_resp_miss_tag),

	    // writeback data to PRF
		.WB_valid(DUT_WB_valid),
		.WB_data(DUT_WB_data),
		.WB_PR(DUT_WB_PR),
		.WB_ROB_index(DUT_WB_ROB_index),

	    // writeback backpressure from PRF
		.WB_ready(tb_WB_ready),

	    // CAM launch
		.stamofu_CAM_launch_valid(DUT_stamofu_CAM_launch_valid),
		.stamofu_CAM_launch_PA_word(DUT_stamofu_CAM_launch_PA_word),
		.stamofu_CAM_launch_byte_mask(DUT_stamofu_CAM_launch_byte_mask),
		.stamofu_CAM_launch_ROB_index(DUT_stamofu_CAM_launch_ROB_index),
		.stamofu_CAM_launch_cq_index(DUT_stamofu_CAM_launch_cq_index),
		.stamofu_CAM_launch_is_mq(DUT_stamofu_CAM_launch_is_mq),
		.stamofu_CAM_launch_mq_index(DUT_stamofu_CAM_launch_mq_index),

	    // central queue info grab
		.ldu_cq_info_grab_cq_index(DUT_ldu_cq_info_grab_cq_index),
		.ldu_cq_info_grab_op(tb_ldu_cq_info_grab_op),
		.ldu_cq_info_grab_mdp_info(tb_ldu_cq_info_grab_mdp_info),
		.ldu_cq_info_grab_dest_PR(tb_ldu_cq_info_grab_dest_PR),
		.ldu_cq_info_grab_ROB_index(tb_ldu_cq_info_grab_ROB_index),

	    // central queue info ret
		.ldu_cq_info_ret_valid(DUT_ldu_cq_info_ret_valid),
		.ldu_cq_info_ret_cq_index(DUT_ldu_cq_info_ret_cq_index),
		.ldu_cq_info_ret_misaligned(DUT_ldu_cq_info_ret_misaligned),
		.ldu_cq_info_ret_dtlb_hit(DUT_ldu_cq_info_ret_dtlb_hit),
		.ldu_cq_info_ret_page_fault(DUT_ldu_cq_info_ret_page_fault),
		.ldu_cq_info_ret_access_fault(DUT_ldu_cq_info_ret_access_fault),
		.ldu_cq_info_ret_dcache_hit(DUT_ldu_cq_info_ret_dcache_hit),
		.ldu_cq_info_ret_is_mem(DUT_ldu_cq_info_ret_is_mem),
		.ldu_cq_info_ret_aq_blocking(DUT_ldu_cq_info_ret_aq_blocking),
		.ldu_cq_info_ret_PA_word(DUT_ldu_cq_info_ret_PA_word),
		.ldu_cq_info_ret_byte_mask(DUT_ldu_cq_info_ret_byte_mask),
		.ldu_cq_info_ret_data(DUT_ldu_cq_info_ret_data),

	    // misaligned queue info ret
		.ldu_mq_info_ret_valid(DUT_ldu_mq_info_ret_valid),
		.ldu_mq_info_ret_mq_index(DUT_ldu_mq_info_ret_mq_index),
		.ldu_mq_info_ret_dtlb_hit(DUT_ldu_mq_info_ret_dtlb_hit),
		.ldu_mq_info_ret_page_fault(DUT_ldu_mq_info_ret_page_fault),
		.ldu_mq_info_ret_access_fault(DUT_ldu_mq_info_ret_access_fault),
		.ldu_mq_info_ret_dcache_hit(DUT_ldu_mq_info_ret_dcache_hit),
		.ldu_mq_info_ret_is_mem(DUT_ldu_mq_info_ret_is_mem),
		.ldu_mq_info_ret_aq_blocking(DUT_ldu_mq_info_ret_aq_blocking),
		.ldu_mq_info_ret_PA_word(DUT_ldu_mq_info_ret_PA_word),
		.ldu_mq_info_ret_byte_mask(DUT_ldu_mq_info_ret_byte_mask),
		.ldu_mq_info_ret_data(DUT_ldu_mq_info_ret_data),

	    // misprediction notification to ROB
		.mispred_notif_valid(DUT_mispred_notif_valid),
		.mispred_notif_ROB_index(DUT_mispred_notif_ROB_index),

	    // misprediction notification backpressure from ROB
		.mispred_notif_ready(tb_mispred_notif_ready),

	    // exception to ROB
		.rob_exception_valid(DUT_rob_exception_valid),
		.rob_exception_VA(DUT_rob_exception_VA),
		.rob_exception_page_fault(DUT_rob_exception_page_fault),
		.rob_exception_access_fault(DUT_rob_exception_access_fault),
		.rob_exception_ROB_index(DUT_rob_exception_ROB_index),

	    // exception backpressure from ROB
		.rob_exception_ready(tb_rob_exception_ready),

	    // restart from ROB
		.rob_restart_valid(tb_rob_restart_valid),
		.rob_restart_ASID(tb_rob_restart_ASID),
		.rob_restart_exec_mode(tb_rob_restart_exec_mode),
		.rob_restart_virtual_mode(tb_rob_restart_virtual_mode),
		.rob_restart_MXR(tb_rob_restart_MXR),
		.rob_restart_SUM(tb_rob_restart_SUM)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_first_try_ack !== DUT_first_try_ack) begin
			$display("TB ERROR: expected_first_try_ack (%h) != DUT_first_try_ack (%h)",
				expected_first_try_ack, DUT_first_try_ack);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_enq_valid !== DUT_ldu_mq_enq_valid) begin
			$display("TB ERROR: expected_ldu_mq_enq_valid (%h) != DUT_ldu_mq_enq_valid (%h)",
				expected_ldu_mq_enq_valid, DUT_ldu_mq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_try_ack !== DUT_second_try_ack) begin
			$display("TB ERROR: expected_second_try_ack (%h) != DUT_second_try_ack (%h)",
				expected_second_try_ack, DUT_second_try_ack);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_data_try_ack !== DUT_data_try_ack) begin
			$display("TB ERROR: expected_data_try_ack (%h) != DUT_data_try_ack (%h)",
				expected_data_try_ack, DUT_data_try_ack);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_valid !== DUT_dtlb_req_valid) begin
			$display("TB ERROR: expected_dtlb_req_valid (%h) != DUT_dtlb_req_valid (%h)",
				expected_dtlb_req_valid, DUT_dtlb_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_exec_mode !== DUT_dtlb_req_exec_mode) begin
			$display("TB ERROR: expected_dtlb_req_exec_mode (%h) != DUT_dtlb_req_exec_mode (%h)",
				expected_dtlb_req_exec_mode, DUT_dtlb_req_exec_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_virtual_mode !== DUT_dtlb_req_virtual_mode) begin
			$display("TB ERROR: expected_dtlb_req_virtual_mode (%h) != DUT_dtlb_req_virtual_mode (%h)",
				expected_dtlb_req_virtual_mode, DUT_dtlb_req_virtual_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_ASID !== DUT_dtlb_req_ASID) begin
			$display("TB ERROR: expected_dtlb_req_ASID (%h) != DUT_dtlb_req_ASID (%h)",
				expected_dtlb_req_ASID, DUT_dtlb_req_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_MXR !== DUT_dtlb_req_MXR) begin
			$display("TB ERROR: expected_dtlb_req_MXR (%h) != DUT_dtlb_req_MXR (%h)",
				expected_dtlb_req_MXR, DUT_dtlb_req_MXR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_SUM !== DUT_dtlb_req_SUM) begin
			$display("TB ERROR: expected_dtlb_req_SUM (%h) != DUT_dtlb_req_SUM (%h)",
				expected_dtlb_req_SUM, DUT_dtlb_req_SUM);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_VPN !== DUT_dtlb_req_VPN) begin
			$display("TB ERROR: expected_dtlb_req_VPN (%h) != DUT_dtlb_req_VPN (%h)",
				expected_dtlb_req_VPN, DUT_dtlb_req_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_cq_index !== DUT_dtlb_req_cq_index) begin
			$display("TB ERROR: expected_dtlb_req_cq_index (%h) != DUT_dtlb_req_cq_index (%h)",
				expected_dtlb_req_cq_index, DUT_dtlb_req_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_is_mq !== DUT_dtlb_req_is_mq) begin
			$display("TB ERROR: expected_dtlb_req_is_mq (%h) != DUT_dtlb_req_is_mq (%h)",
				expected_dtlb_req_is_mq, DUT_dtlb_req_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_mq_index !== DUT_dtlb_req_mq_index) begin
			$display("TB ERROR: expected_dtlb_req_mq_index (%h) != DUT_dtlb_req_mq_index (%h)",
				expected_dtlb_req_mq_index, DUT_dtlb_req_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_valid !== DUT_dcache_req_valid) begin
			$display("TB ERROR: expected_dcache_req_valid (%h) != DUT_dcache_req_valid (%h)",
				expected_dcache_req_valid, DUT_dcache_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_block_offset !== DUT_dcache_req_block_offset) begin
			$display("TB ERROR: expected_dcache_req_block_offset (%h) != DUT_dcache_req_block_offset (%h)",
				expected_dcache_req_block_offset, DUT_dcache_req_block_offset);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_index !== DUT_dcache_req_index) begin
			$display("TB ERROR: expected_dcache_req_index (%h) != DUT_dcache_req_index (%h)",
				expected_dcache_req_index, DUT_dcache_req_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_cq_index !== DUT_dcache_req_cq_index) begin
			$display("TB ERROR: expected_dcache_req_cq_index (%h) != DUT_dcache_req_cq_index (%h)",
				expected_dcache_req_cq_index, DUT_dcache_req_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_is_mq !== DUT_dcache_req_is_mq) begin
			$display("TB ERROR: expected_dcache_req_is_mq (%h) != DUT_dcache_req_is_mq (%h)",
				expected_dcache_req_is_mq, DUT_dcache_req_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_mq_index !== DUT_dcache_req_mq_index) begin
			$display("TB ERROR: expected_dcache_req_mq_index (%h) != DUT_dcache_req_mq_index (%h)",
				expected_dcache_req_mq_index, DUT_dcache_req_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_hit_valid !== DUT_dcache_resp_hit_valid) begin
			$display("TB ERROR: expected_dcache_resp_hit_valid (%h) != DUT_dcache_resp_hit_valid (%h)",
				expected_dcache_resp_hit_valid, DUT_dcache_resp_hit_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_hit_way !== DUT_dcache_resp_hit_way) begin
			$display("TB ERROR: expected_dcache_resp_hit_way (%h) != DUT_dcache_resp_hit_way (%h)",
				expected_dcache_resp_hit_way, DUT_dcache_resp_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_miss_valid !== DUT_dcache_resp_miss_valid) begin
			$display("TB ERROR: expected_dcache_resp_miss_valid (%h) != DUT_dcache_resp_miss_valid (%h)",
				expected_dcache_resp_miss_valid, DUT_dcache_resp_miss_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_miss_tag !== DUT_dcache_resp_miss_tag) begin
			$display("TB ERROR: expected_dcache_resp_miss_tag (%h) != DUT_dcache_resp_miss_tag (%h)",
				expected_dcache_resp_miss_tag, DUT_dcache_resp_miss_tag);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_valid !== DUT_WB_valid) begin
			$display("TB ERROR: expected_WB_valid (%h) != DUT_WB_valid (%h)",
				expected_WB_valid, DUT_WB_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_data !== DUT_WB_data) begin
			$display("TB ERROR: expected_WB_data (%h) != DUT_WB_data (%h)",
				expected_WB_data, DUT_WB_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_PR !== DUT_WB_PR) begin
			$display("TB ERROR: expected_WB_PR (%h) != DUT_WB_PR (%h)",
				expected_WB_PR, DUT_WB_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_ROB_index !== DUT_WB_ROB_index) begin
			$display("TB ERROR: expected_WB_ROB_index (%h) != DUT_WB_ROB_index (%h)",
				expected_WB_ROB_index, DUT_WB_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_valid !== DUT_stamofu_CAM_launch_valid) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_valid (%h) != DUT_stamofu_CAM_launch_valid (%h)",
				expected_stamofu_CAM_launch_valid, DUT_stamofu_CAM_launch_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_PA_word !== DUT_stamofu_CAM_launch_PA_word) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_PA_word (%h) != DUT_stamofu_CAM_launch_PA_word (%h)",
				expected_stamofu_CAM_launch_PA_word, DUT_stamofu_CAM_launch_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_byte_mask !== DUT_stamofu_CAM_launch_byte_mask) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_byte_mask (%h) != DUT_stamofu_CAM_launch_byte_mask (%h)",
				expected_stamofu_CAM_launch_byte_mask, DUT_stamofu_CAM_launch_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_ROB_index !== DUT_stamofu_CAM_launch_ROB_index) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_ROB_index (%h) != DUT_stamofu_CAM_launch_ROB_index (%h)",
				expected_stamofu_CAM_launch_ROB_index, DUT_stamofu_CAM_launch_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_cq_index !== DUT_stamofu_CAM_launch_cq_index) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_cq_index (%h) != DUT_stamofu_CAM_launch_cq_index (%h)",
				expected_stamofu_CAM_launch_cq_index, DUT_stamofu_CAM_launch_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_is_mq !== DUT_stamofu_CAM_launch_is_mq) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_is_mq (%h) != DUT_stamofu_CAM_launch_is_mq (%h)",
				expected_stamofu_CAM_launch_is_mq, DUT_stamofu_CAM_launch_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_mq_index !== DUT_stamofu_CAM_launch_mq_index) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_mq_index (%h) != DUT_stamofu_CAM_launch_mq_index (%h)",
				expected_stamofu_CAM_launch_mq_index, DUT_stamofu_CAM_launch_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_grab_cq_index !== DUT_ldu_cq_info_grab_cq_index) begin
			$display("TB ERROR: expected_ldu_cq_info_grab_cq_index (%h) != DUT_ldu_cq_info_grab_cq_index (%h)",
				expected_ldu_cq_info_grab_cq_index, DUT_ldu_cq_info_grab_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_valid !== DUT_ldu_cq_info_ret_valid) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_valid (%h) != DUT_ldu_cq_info_ret_valid (%h)",
				expected_ldu_cq_info_ret_valid, DUT_ldu_cq_info_ret_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_cq_index !== DUT_ldu_cq_info_ret_cq_index) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_cq_index (%h) != DUT_ldu_cq_info_ret_cq_index (%h)",
				expected_ldu_cq_info_ret_cq_index, DUT_ldu_cq_info_ret_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_misaligned !== DUT_ldu_cq_info_ret_misaligned) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_misaligned (%h) != DUT_ldu_cq_info_ret_misaligned (%h)",
				expected_ldu_cq_info_ret_misaligned, DUT_ldu_cq_info_ret_misaligned);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_dtlb_hit !== DUT_ldu_cq_info_ret_dtlb_hit) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_dtlb_hit (%h) != DUT_ldu_cq_info_ret_dtlb_hit (%h)",
				expected_ldu_cq_info_ret_dtlb_hit, DUT_ldu_cq_info_ret_dtlb_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_page_fault !== DUT_ldu_cq_info_ret_page_fault) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_page_fault (%h) != DUT_ldu_cq_info_ret_page_fault (%h)",
				expected_ldu_cq_info_ret_page_fault, DUT_ldu_cq_info_ret_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_access_fault !== DUT_ldu_cq_info_ret_access_fault) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_access_fault (%h) != DUT_ldu_cq_info_ret_access_fault (%h)",
				expected_ldu_cq_info_ret_access_fault, DUT_ldu_cq_info_ret_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_dcache_hit !== DUT_ldu_cq_info_ret_dcache_hit) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_dcache_hit (%h) != DUT_ldu_cq_info_ret_dcache_hit (%h)",
				expected_ldu_cq_info_ret_dcache_hit, DUT_ldu_cq_info_ret_dcache_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_is_mem !== DUT_ldu_cq_info_ret_is_mem) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_is_mem (%h) != DUT_ldu_cq_info_ret_is_mem (%h)",
				expected_ldu_cq_info_ret_is_mem, DUT_ldu_cq_info_ret_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_aq_blocking !== DUT_ldu_cq_info_ret_aq_blocking) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_aq_blocking (%h) != DUT_ldu_cq_info_ret_aq_blocking (%h)",
				expected_ldu_cq_info_ret_aq_blocking, DUT_ldu_cq_info_ret_aq_blocking);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_PA_word !== DUT_ldu_cq_info_ret_PA_word) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_PA_word (%h) != DUT_ldu_cq_info_ret_PA_word (%h)",
				expected_ldu_cq_info_ret_PA_word, DUT_ldu_cq_info_ret_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_byte_mask !== DUT_ldu_cq_info_ret_byte_mask) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_byte_mask (%h) != DUT_ldu_cq_info_ret_byte_mask (%h)",
				expected_ldu_cq_info_ret_byte_mask, DUT_ldu_cq_info_ret_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_info_ret_data !== DUT_ldu_cq_info_ret_data) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_data (%h) != DUT_ldu_cq_info_ret_data (%h)",
				expected_ldu_cq_info_ret_data, DUT_ldu_cq_info_ret_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_valid !== DUT_ldu_mq_info_ret_valid) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_valid (%h) != DUT_ldu_mq_info_ret_valid (%h)",
				expected_ldu_mq_info_ret_valid, DUT_ldu_mq_info_ret_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_mq_index !== DUT_ldu_mq_info_ret_mq_index) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_mq_index (%h) != DUT_ldu_mq_info_ret_mq_index (%h)",
				expected_ldu_mq_info_ret_mq_index, DUT_ldu_mq_info_ret_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_dtlb_hit !== DUT_ldu_mq_info_ret_dtlb_hit) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_dtlb_hit (%h) != DUT_ldu_mq_info_ret_dtlb_hit (%h)",
				expected_ldu_mq_info_ret_dtlb_hit, DUT_ldu_mq_info_ret_dtlb_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_page_fault !== DUT_ldu_mq_info_ret_page_fault) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_page_fault (%h) != DUT_ldu_mq_info_ret_page_fault (%h)",
				expected_ldu_mq_info_ret_page_fault, DUT_ldu_mq_info_ret_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_access_fault !== DUT_ldu_mq_info_ret_access_fault) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_access_fault (%h) != DUT_ldu_mq_info_ret_access_fault (%h)",
				expected_ldu_mq_info_ret_access_fault, DUT_ldu_mq_info_ret_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_dcache_hit !== DUT_ldu_mq_info_ret_dcache_hit) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_dcache_hit (%h) != DUT_ldu_mq_info_ret_dcache_hit (%h)",
				expected_ldu_mq_info_ret_dcache_hit, DUT_ldu_mq_info_ret_dcache_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_is_mem !== DUT_ldu_mq_info_ret_is_mem) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_is_mem (%h) != DUT_ldu_mq_info_ret_is_mem (%h)",
				expected_ldu_mq_info_ret_is_mem, DUT_ldu_mq_info_ret_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_aq_blocking !== DUT_ldu_mq_info_ret_aq_blocking) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_aq_blocking (%h) != DUT_ldu_mq_info_ret_aq_blocking (%h)",
				expected_ldu_mq_info_ret_aq_blocking, DUT_ldu_mq_info_ret_aq_blocking);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_PA_word !== DUT_ldu_mq_info_ret_PA_word) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_PA_word (%h) != DUT_ldu_mq_info_ret_PA_word (%h)",
				expected_ldu_mq_info_ret_PA_word, DUT_ldu_mq_info_ret_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_byte_mask !== DUT_ldu_mq_info_ret_byte_mask) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_byte_mask (%h) != DUT_ldu_mq_info_ret_byte_mask (%h)",
				expected_ldu_mq_info_ret_byte_mask, DUT_ldu_mq_info_ret_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_data !== DUT_ldu_mq_info_ret_data) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_data (%h) != DUT_ldu_mq_info_ret_data (%h)",
				expected_ldu_mq_info_ret_data, DUT_ldu_mq_info_ret_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_mispred_notif_valid !== DUT_mispred_notif_valid) begin
			$display("TB ERROR: expected_mispred_notif_valid (%h) != DUT_mispred_notif_valid (%h)",
				expected_mispred_notif_valid, DUT_mispred_notif_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_mispred_notif_ROB_index !== DUT_mispred_notif_ROB_index) begin
			$display("TB ERROR: expected_mispred_notif_ROB_index (%h) != DUT_mispred_notif_ROB_index (%h)",
				expected_mispred_notif_ROB_index, DUT_mispred_notif_ROB_index);
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

		if (expected_rob_exception_ROB_index !== DUT_rob_exception_ROB_index) begin
			$display("TB ERROR: expected_rob_exception_ROB_index (%h) != DUT_rob_exception_ROB_index (%h)",
				expected_rob_exception_ROB_index, DUT_rob_exception_ROB_index);
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
	    // first try
		tb_first_try_valid = 1'b0;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b0;
		tb_first_try_VPN = 20'h00000;
		tb_first_try_PO_word = 10'h000;
		tb_first_try_byte_mask = 4'b0000;
		tb_first_try_cq_index = 'h0;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h0;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h000000;
		tb_second_try_PO_word = 10'h000;
		tb_second_try_byte_mask = 4'b0000;
		tb_second_try_cq_index = 'h0;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'h0;
		tb_data_try_cq_index = 'h0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b0;
		tb_dtlb_resp_PPN = 22'h000000;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b00;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_data_by_way = {32'h0, 32'h0};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0000;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h0;
		tb_ldu_cq_info_grab_ROB_index = 7'h0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h00000;
		expected_dtlb_req_cq_index = 'h0;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 5'h00;
		expected_dcache_req_index = 6'h00;
		expected_dcache_req_cq_index = 'h0;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = 32'h0;
		expected_stamofu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_CAM_launch_ROB_index = 7'h0;
		expected_stamofu_CAM_launch_cq_index = 'h0;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h0;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_page_fault = 1'b0;
		expected_ldu_cq_info_ret_access_fault = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = 32'h00000000;
		expected_ldu_cq_info_ret_byte_mask = 4'b0000;
		expected_ldu_cq_info_ret_data = 32'h0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_page_fault = 1'b0;
		expected_ldu_mq_info_ret_access_fault = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = 32'h00000000;
		expected_ldu_mq_info_ret_byte_mask = 4'b0000;
		expected_ldu_mq_info_ret_data = 32'h0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b0;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b0;
		tb_first_try_VPN = 20'h00000;
		tb_first_try_PO_word = 10'h000;
		tb_first_try_byte_mask = 4'b0000;
		tb_first_try_cq_index = 'h0;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h0;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h000000;
		tb_second_try_PO_word = 10'h000;
		tb_second_try_byte_mask = 4'b0000;
		tb_second_try_cq_index = 'h0;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'h0;
		tb_data_try_cq_index = 'h0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b0;
		tb_dtlb_resp_PPN = 22'h000000;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b00;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_data_by_way = {32'h0, 32'h0};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0000;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h0;
		tb_ldu_cq_info_grab_ROB_index = 7'h0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h00000;
		expected_dtlb_req_cq_index = 'h0;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 5'h00;
		expected_dcache_req_index = 6'h00;
		expected_dcache_req_cq_index = 'h0;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = 32'h0;
		expected_stamofu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_CAM_launch_ROB_index = 7'h0;
		expected_stamofu_CAM_launch_cq_index = 'h0;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h0;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_data = 32'h0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_data = 32'h0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: i",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: i",
			"\n\t\tRET: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b0;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b0;
		tb_first_try_VPN = 20'h00000;
		tb_first_try_PO_word = 10'h000;
		tb_first_try_byte_mask = 4'b0000;
		tb_first_try_cq_index = 'h0;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h000000;
		tb_second_try_PO_word = 10'h000;
		tb_second_try_byte_mask = 4'b0000;
		tb_second_try_cq_index = 'h0;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'h0;
		tb_data_try_cq_index = 'h0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b0;
		tb_dtlb_resp_PPN = 22'h000000;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b00;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_data_by_way = {32'h0, 32'h0};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0000;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h0;
		tb_ldu_cq_info_grab_ROB_index = 7'h0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h00000;
		expected_dtlb_req_cq_index = 'h0;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 5'h00;
		expected_dcache_req_index = 6'h00;
		expected_dcache_req_cq_index = 'h0;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = 32'h0;
		expected_stamofu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_CAM_launch_ROB_index = 7'h0;
		expected_stamofu_CAM_launch_cq_index = 'h0;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h0;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_data = 32'h0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_data = 32'h0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 1: LW 01234,012,1111 -> 234567,012,1111 mem (missing dtlb ready)",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: i",
			"\n\t\tRET: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b0;
		tb_first_try_VPN = 20'h01234;
		tb_first_try_PO_word = 10'h012;
		tb_first_try_byte_mask = 4'b1111;
		tb_first_try_cq_index = 'h1;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h000000;
		tb_second_try_PO_word = 10'h000;
		tb_second_try_byte_mask = 4'b0000;
		tb_second_try_cq_index = 'h0;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'h0;
		tb_data_try_cq_index = 'h0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b0;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b0;
		tb_dtlb_resp_PPN = 22'h000000;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b00;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_data_by_way = {32'h0, 32'h0};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0000;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h0;
		tb_ldu_cq_info_grab_ROB_index = 7'h0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h01234;
		expected_dtlb_req_cq_index = 'h1;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 5'h00;
		expected_dcache_req_index = 6'h00;
		expected_dcache_req_cq_index = 'h0;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = 32'h0;
		expected_stamofu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_CAM_launch_ROB_index = 7'h0;
		expected_stamofu_CAM_launch_cq_index = 'h0;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h0;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_data = 32'h0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_data = 32'h0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 1: LW 01234,012,1111 -> 234567,012,1111 mem (missing dcache ready)",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: i",
			"\n\t\tRET: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b0;
		tb_first_try_VPN = 20'h01234;
		tb_first_try_PO_word = 10'h012;
		tb_first_try_byte_mask = 4'b1111;
		tb_first_try_cq_index = 'h1;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h000000;
		tb_second_try_PO_word = 10'h000;
		tb_second_try_byte_mask = 4'b0000;
		tb_second_try_cq_index = 'h0;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'h0;
		tb_data_try_cq_index = 'h0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b0;
		tb_dtlb_resp_PPN = 22'h000000;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b00;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_data_by_way = {32'h0, 32'h0};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0000;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h0;
		tb_ldu_cq_info_grab_ROB_index = 7'h0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h01234;
		expected_dtlb_req_cq_index = 'h1;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 5'h00;
		expected_dcache_req_index = 6'h00;
		expected_dcache_req_cq_index = 'h0;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = 32'h0;
		expected_stamofu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_CAM_launch_ROB_index = 7'h0;
		expected_stamofu_CAM_launch_cq_index = 'h0;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h0;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_data = 32'h0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_data = 32'h0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 1: LW 01234,012,1111 -> 234567,012,1111 mem (ack)",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: i",
			"\n\t\tRET: i",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b0;
		tb_first_try_VPN = 20'h01234;
		tb_first_try_PO_word = 10'h012;
		tb_first_try_byte_mask = 4'b1111;
		tb_first_try_cq_index = 'h1;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h000000;
		tb_second_try_PO_word = 10'h000;
		tb_second_try_byte_mask = 4'b0000;
		tb_second_try_cq_index = 'h0;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'h0;
		tb_data_try_cq_index = 'h0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b0;
		tb_dtlb_resp_PPN = 22'h000000;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b00;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_data_by_way = {32'h0, 32'h0};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0000;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h0;
		tb_ldu_cq_info_grab_ROB_index = 7'h0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b1;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b1;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h01234;
		expected_dtlb_req_cq_index = 'h1;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b1;
		expected_dcache_req_block_offset = 'h012 << 2;
		expected_dcache_req_index = 'h012 >> 4;
		expected_dcache_req_cq_index = 'h1;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = 32'h0;
		expected_stamofu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_CAM_launch_ROB_index = 7'h0;
		expected_stamofu_CAM_launch_cq_index = 'h0;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h0;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_data = 32'h0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_data = 32'h0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 7,f: LHU p3b 89abc,def,0001 -> 102030,def,0001 io,mq (mq enq not ready)",
				"\n\t\t\tsecond: 3,s: LBU p11 00500,050,0100 -> 055055,050,0100 mem,cq (ack)",
				"\n\t\t\tdata: 8,d: p26 <= 1a2b3c4d mispred (second)",
			"\n\t\tRESP: 1,f: LW p5 01234,012,1111 -> 234567,012,1111 mem,cq (dtlb hit, dcache hit)",
			"\n\t\tRET: i",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b1;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h89abc;
		tb_first_try_PO_word = 10'hdef;
		tb_first_try_byte_mask = 4'b0001;
		tb_first_try_cq_index = 'h7;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b1;
		tb_second_try_PPN = 22'h055055;
		tb_second_try_PO_word = 10'h050;
		tb_second_try_byte_mask = 4'b0100;
		tb_second_try_cq_index = 'h3;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b1;
		tb_data_try_do_mispred = 1'b1;
		tb_data_try_data = 32'h1a2b3c4d;
		tb_data_try_cq_index = 'h8;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'h234567;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b11;
		tb_dcache_resp_tag_by_way = {22'h234567, 22'h234568};
		tb_dcache_resp_data_by_way = {32'h01234012, 32'hffffdead};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0010;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h5;
		tb_ldu_cq_info_grab_ROB_index = 7'h1;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b1;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h89abc;
		expected_dtlb_req_cq_index = 'h7;
		expected_dtlb_req_is_mq = 1'b1;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b1;
		expected_dcache_req_block_offset = 'h050 << 2;
		expected_dcache_req_index = 'h050 >> 4;
		expected_dcache_req_cq_index = 'h3;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b1;
		expected_dcache_resp_hit_way = 1'b1;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h234567;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = 32'h0;
		expected_stamofu_CAM_launch_byte_mask = 4'b0000;
		expected_stamofu_CAM_launch_ROB_index = 7'h0;
		expected_stamofu_CAM_launch_cq_index = 'h0;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h1;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h0;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_page_fault = 1'b0;
		expected_ldu_cq_info_ret_access_fault = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = 32'h0;
		expected_ldu_cq_info_ret_byte_mask = 4'b0000;
		expected_ldu_cq_info_ret_data = 32'h0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_page_fault = 1'b0;
		expected_ldu_mq_info_ret_access_fault = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = 32'h0;
		expected_ldu_mq_info_ret_byte_mask = 4'b0000;
		expected_ldu_mq_info_ret_data = 32'h0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = 32'h00000000;
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 7,f: LHU p3b 89abc,def,0001 -> 102030,def,0001 io,mq (dcache not ready)",
				"\n\t\t\tsecond: 9,s: LH p66 606060,606,0110 -> 222222,606,0110 mem,cq (dcache not ready)",
				"\n\t\t\tdata: 8,d: p26 <= 1a2b3c4d mispred (ack)",
			"\n\t\tRESP: 3,s: LBU p11 00500,050,0100 -> 055055,050,0100 mem,cq (dcache miss)",
			"\n\t\tRET: 1,f: LW p5 01234,012,1111 -> 234567,012,1111 mem,cq (dtlb hit, dcache hit)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b1;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h89abc;
		tb_first_try_PO_word = 10'hdef;
		tb_first_try_byte_mask = 4'b0001;
		tb_first_try_cq_index = 'h7;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b1;
		tb_second_try_PPN = 22'h222222;
		tb_second_try_PO_word = 10'h606;
		tb_second_try_byte_mask = 4'b0110;
		tb_second_try_cq_index = 'h9;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b1;
		tb_data_try_do_mispred = 1'b1;
		tb_data_try_data = 32'h1a2b3c4d;
		tb_data_try_cq_index = 'h8;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'h234567;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b01;
		tb_dcache_resp_tag_by_way = {22'h222222, 22'h222221};
		tb_dcache_resp_data_by_way = {32'h00500050, 32'hdeadbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b1100;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h11;
		tb_ldu_cq_info_grab_ROB_index = 7'h3;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b1;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h89abc;
		expected_dtlb_req_cq_index = 'h7;
		expected_dtlb_req_is_mq = 1'b1;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h606 << 2;
		expected_dcache_req_index = 'h606 >> 4;
		expected_dcache_req_cq_index = 'h9;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b1;
		expected_dcache_resp_miss_tag = 22'h055055;
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h01234012;
		expected_WB_PR = 7'h5;
		expected_WB_ROB_index = 7'h1;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b1;
		expected_stamofu_CAM_launch_PA_word = {22'h234567, 10'h012};
		expected_stamofu_CAM_launch_byte_mask = 4'b1111;
		expected_stamofu_CAM_launch_ROB_index = 7'h1;
		expected_stamofu_CAM_launch_cq_index = 'h1;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h3;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b1;
		expected_ldu_cq_info_ret_cq_index = 'h1;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_page_fault = 1'b0;
		expected_ldu_cq_info_ret_access_fault = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b1;
		expected_ldu_cq_info_ret_is_mem = 1'b1;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = {22'h234567, 10'h012};
		expected_ldu_cq_info_ret_byte_mask = 4'b1111;
		expected_ldu_cq_info_ret_data = 32'h01234012;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_page_fault = 1'b0;
		expected_ldu_mq_info_ret_access_fault = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b1;
		expected_ldu_mq_info_ret_is_mem = 1'b1;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'h234567, 10'h012};
		expected_ldu_mq_info_ret_byte_mask = 4'b1111;
		expected_ldu_mq_info_ret_data = 32'h01234012;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h1;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h34567, 10'h012, 2'h0};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h1;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 7,f: LHU p3b 89abc,def,0001 -> 102030,def,0001 io,mq (dtlb not ready)",
				"\n\t\t\tsecond: 9,s: LH p66 xxxxx,606,0110 -> 222222,606,0110 mem,cq (ack)",
				"\n\t\t\tdata: b,d: pf <= ffffffff (second)",
			"\n\t\tRESP: 8,d: p26 <= 1a2b3c4d mispred",
			"\n\t\tRET: 3,s: LBU p11 00500,050,0100 -> 055055,050,0100 mem,cq (dcache miss)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b1;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h89abc;
		tb_first_try_PO_word = 10'hdef;
		tb_first_try_byte_mask = 4'b0001;
		tb_first_try_cq_index = 'h7;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b0;
		tb_second_try_misaligned = 1'b0;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b0;
		tb_second_try_is_mem = 1'b1;
		tb_second_try_PPN = 22'h222222;
		tb_second_try_PO_word = 10'h606;
		tb_second_try_byte_mask = 4'b0110;
		tb_second_try_cq_index = 'h9;
		tb_second_try_mq_index = 'h0;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b1;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b0;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'h234567;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b01;
		tb_dcache_resp_tag_by_way = {22'h222222, 22'h222221};
		tb_dcache_resp_data_by_way = {32'h00500050, 32'hdeadbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0011;
		tb_ldu_cq_info_grab_mdp_info = 8'b11001100;
		tb_ldu_cq_info_grab_dest_PR = 7'h26;
		tb_ldu_cq_info_grab_ROB_index = 7'h8;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b1;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h89abc;
		expected_dtlb_req_cq_index = 'h7;
		expected_dtlb_req_is_mq = 1'b1;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b1;
		expected_dcache_req_block_offset = 'h606 << 2;
		expected_dcache_req_index = 'h606 >> 4;
		expected_dcache_req_cq_index = 'h9;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h222222;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h000000ad;
		expected_WB_PR = 7'h11;
		expected_WB_ROB_index = 7'h3;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b1;
		expected_stamofu_CAM_launch_PA_word = {22'h055055, 10'h050};
		expected_stamofu_CAM_launch_byte_mask = 4'b0100;
		expected_stamofu_CAM_launch_ROB_index = 7'h3;
		expected_stamofu_CAM_launch_cq_index = 'h3;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h8;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b1;
		expected_ldu_cq_info_ret_cq_index = 'h3;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_page_fault = 1'b0;
		expected_ldu_cq_info_ret_access_fault = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b1;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = {22'h055055, 10'h050};
		expected_ldu_cq_info_ret_byte_mask = 4'b0100;
		expected_ldu_cq_info_ret_data = 32'hdeadbeef;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_page_fault = 1'b0;
		expected_ldu_mq_info_ret_access_fault = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b1;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'h055055, 10'h050};
		expected_ldu_mq_info_ret_byte_mask = 4'b0100;
		expected_ldu_mq_info_ret_data = 32'hdeadbeef;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h3;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h055055, 10'h050, 2'h2};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h3;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 7,f: LHU p3b 89abc,def,0001 -> 102030,def,0001 io,mq (stall)",
				"\n\t\t\tsecond: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq (stall)",
				"\n\t\t\tdata: b,d: pf <= ffffffff (stall)",
			"\n\t\tRESP: 9,s: LH p66 xxxxx,606,0110 -> 222222,606,0110 mem,cq (dcache hit, aq block)",
			"\n\t\tRET: 8,d: p26 <= 1a2b3c4d mispred (mispred not ready)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b1;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h89abc;
		tb_first_try_PO_word = 10'hdef;
		tb_first_try_byte_mask = 4'b0001;
		tb_first_try_cq_index = 'h7;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b0111;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b1;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'h234567;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b10;
		tb_dcache_resp_tag_by_way = {22'h222222, 22'h222222};
		tb_dcache_resp_data_by_way = {32'h06060606, 32'hdeadbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0001;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h66;
		tb_ldu_cq_info_grab_ROB_index = 7'h9;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h89abc;
		expected_dtlb_req_cq_index = 'h7;
		expected_dtlb_req_is_mq = 1'b1;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h777 << 2;
		expected_dcache_req_index = 'h777 >> 4;
		expected_dcache_req_cq_index = 'he;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h2;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b1;
		expected_dcache_resp_hit_way = 1'b1;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h222222;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h1a2b3c4d;
		expected_WB_PR = 7'h26;
		expected_WB_ROB_index = 7'h8;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h222222, 10'h606};
		expected_stamofu_CAM_launch_byte_mask = 4'b0110;
		expected_stamofu_CAM_launch_ROB_index = 7'h8;
		expected_stamofu_CAM_launch_cq_index = 'h8;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h9;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h8;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_page_fault = 1'b0;
		expected_ldu_cq_info_ret_access_fault = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b1;
		expected_ldu_cq_info_ret_aq_blocking = 1'b1;
		expected_ldu_cq_info_ret_PA_word = {22'h222222, 10'h606};
		expected_ldu_cq_info_ret_byte_mask = 4'b0110;
		expected_ldu_cq_info_ret_data = 32'h1a2b3c4d;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h8;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_page_fault = 1'b0;
		expected_ldu_mq_info_ret_access_fault = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b1;
		expected_ldu_mq_info_ret_aq_blocking = 1'b1;
		expected_ldu_mq_info_ret_PA_word = {22'h222222, 10'h606};
		expected_ldu_mq_info_ret_byte_mask = 4'b0110;
		expected_ldu_mq_info_ret_data = 32'h1a2b3c4d;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h8;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h222222, 10'h606, 2'h1};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h8;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 7,f: LHU p3b 89abc,def,0001 -> 102030,def,0001 io,mq (ack)",
				"\n\t\t\tsecond: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq (first)",
				"\n\t\t\tdata: b,d: pf <= ffffffff (first)",
			"\n\t\tRESP: 9,s: LH p66 xxxxx,606,0110 -> 222222,606,0110 mem,cq (dcache hit, aq block)",
			"\n\t\tRET: 8,d: p26 <= 1a2b3c4d mispred",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b1;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h89abc;
		tb_first_try_PO_word = 10'hdef;
		tb_first_try_byte_mask = 4'b0001;
		tb_first_try_cq_index = 'h7;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h0;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b0111;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b1;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'h234567;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b01;
		tb_dcache_resp_tag_by_way = {22'h222222, 22'h222222};
		tb_dcache_resp_data_by_way = {32'hdeadbeef, 32'hdeadbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0001;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h66;
		tb_ldu_cq_info_grab_ROB_index = 7'h9;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b1;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b1;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b1;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b1;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h89abc;
		expected_dtlb_req_cq_index = 'h7;
		expected_dtlb_req_is_mq = 1'b1;
		expected_dtlb_req_mq_index = 'h0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b1;
		expected_dcache_req_block_offset = 'hdef << 2;
		expected_dcache_req_index = 'hdef >> 4;
		expected_dcache_req_cq_index = 'h7;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b1;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h222222;
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h1a2b3c4d;
		expected_WB_PR = 7'h26;
		expected_WB_ROB_index = 7'h8;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h222222, 10'h606};
		expected_stamofu_CAM_launch_byte_mask = 4'b0110;
		expected_stamofu_CAM_launch_ROB_index = 7'h8;
		expected_stamofu_CAM_launch_cq_index = 'h8;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h9;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h8;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b1;
		expected_ldu_cq_info_ret_aq_blocking = 1'b1;
		expected_ldu_cq_info_ret_data = 32'h1a2b3c4d;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h8;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b1;
		expected_ldu_mq_info_ret_aq_blocking = 1'b1;
		expected_ldu_mq_info_ret_data = 32'h1a2b3c4d;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b1;
		expected_mispred_notif_ROB_index = 7'h8;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h222222, 10'h606, 2'h1};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h8;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: 4,f: LB p44 11111,111,1000 -> ffffff,111,1000 mem,cq (ack)",
				"\n\t\t\tsecond: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq (first)",
				"\n\t\t\tdata: b,d: pf <= ffffffff (first)",
			"\n\t\tRESP: 7,f: LHU p3b 89abc,def,0001 -> 102030,def,0001 io,mq (dtlb hit, dcache miss)",
			"\n\t\tRET: 9,s: LH p66 xxxxx,606,0110 -> 222222,606,0110 mem,cq (dcache hit, aq block)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h11111;
		tb_first_try_PO_word = 10'h111;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'h4;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b0111;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b1;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'h102030;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b00;
		tb_dcache_resp_tag_by_way = {22'h102030, 22'h123456};
		tb_dcache_resp_data_by_way = {32'h89abcdef, 32'hffbeef00};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b1101;
		tb_ldu_cq_info_grab_mdp_info = 8'b00111111;
		tb_ldu_cq_info_grab_dest_PR = 7'h3b;
		tb_ldu_cq_info_grab_ROB_index = 7'h7;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b1;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b1;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h11111;
		expected_dtlb_req_cq_index = 'h4;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b1;
		expected_dcache_req_block_offset = 'h111 << 2;
		expected_dcache_req_index = 'h111 >> 4;
		expected_dcache_req_cq_index = 'h4;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h1;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b1;
		expected_dcache_resp_miss_tag = 22'h102030;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000606;
		expected_WB_PR = 7'h66;
		expected_WB_ROB_index = 7'h9;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h222222, 10'h606};
		expected_stamofu_CAM_launch_byte_mask = 4'b0110;
		expected_stamofu_CAM_launch_ROB_index = 7'h9;
		expected_stamofu_CAM_launch_cq_index = 'h9;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h7;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b1;
		expected_ldu_cq_info_ret_cq_index = 'h9;
		expected_ldu_cq_info_ret_misaligned = 1'b0;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_dcache_hit = 1'b1;
		expected_ldu_cq_info_ret_is_mem = 1'b1;
		expected_ldu_cq_info_ret_aq_blocking = 1'b1;
		expected_ldu_cq_info_ret_data = 32'h06060606;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b1;
		expected_ldu_mq_info_ret_is_mem = 1'b1;
		expected_ldu_mq_info_ret_aq_blocking = 1'b1;
		expected_ldu_mq_info_ret_data = 32'h06060606;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h9;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h222222, 10'h606, 2'h1};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h9;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: f,f: LH p1 1f05d,abe,1000 -> deadbe,abe,1000 mem,pf,cq (dcache not ready)",
				"\n\t\t\tsecond: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq (dcache not ready)",
				"\n\t\t\tdata: b,d: pf <= ffffffff (ack)",
			"\n\t\tRESP: 4,f: LB p44 11111,111,1000 -> ffffff,111,1000 mem,cq (dtlb hit, dcache hit, mdp present)",
			"\n\t\tRET: 7,f: LHU p3b 89abc,def,0001 -> 102030,def,0001 io,mq (dtlb hit, dcache miss)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h1f05d;
		tb_first_try_PO_word = 10'habe;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'hf;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b0111;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b1;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'hffffff;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b11;
		tb_dcache_resp_tag_by_way = {22'h102030, 22'hffffff};
		tb_dcache_resp_data_by_way = {32'h89abcdef, 32'hf1e2d3c4};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0000;
		tb_ldu_cq_info_grab_mdp_info = 8'b01000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h44;
		tb_ldu_cq_info_grab_ROB_index = 7'h4;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b1;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h1f05d;
		expected_dtlb_req_cq_index = 'hf;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h777 << 2;
		expected_dcache_req_index = 'h777 >> 4;
		expected_dcache_req_cq_index = 'he;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h2;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b1;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'hffffff;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0000ffbe;
		expected_WB_PR = 7'h3b;
		expected_WB_ROB_index = 7'h7;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b1;
		expected_stamofu_CAM_launch_PA_word = {22'h102030, 10'hdef};
		expected_stamofu_CAM_launch_byte_mask = 4'b0001;
		expected_stamofu_CAM_launch_ROB_index = 7'h7;
		expected_stamofu_CAM_launch_cq_index = 'h7;
		expected_stamofu_CAM_launch_is_mq = 1'b1;
		expected_stamofu_CAM_launch_mq_index = 'h0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'h4;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'h7;
		expected_ldu_cq_info_ret_misaligned = 1'b1;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = {22'h102030, 10'hdef};
		expected_ldu_cq_info_ret_byte_mask = 4'b0001;
		expected_ldu_cq_info_ret_data = 32'hffbeef00;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b1;
		expected_ldu_mq_info_ret_mq_index = 'h0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'h102030, 10'hdef};
		expected_ldu_mq_info_ret_byte_mask = 4'b0001;
		expected_ldu_mq_info_ret_data = 32'hffbeef00;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h7;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h102030, 10'hdef, 2'h0};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h7;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: f,f: LH p1 1f05d,abe,1000 -> deadbe,abe,1000 mem,pf,cq (dtlb not ready)",
				"\n\t\t\tsecond: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq (ack)",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: b,d: pf <= ffffffff",
			"\n\t\tRET: 4,f: LB p44 11111,111,1000 -> ffffff,111,1000 mem,cq (dtlb hit, dcache hit, mdp present)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h1f05d;
		tb_first_try_PO_word = 10'habe;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'hf;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b1;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b0111;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b0;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'hffffff;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b11;
		tb_dcache_resp_tag_by_way = {22'h102030, 22'hffffff};
		tb_dcache_resp_data_by_way = {32'h89abcdef, 32'hf1e2d3c4};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0011;
		tb_ldu_cq_info_grab_mdp_info = 8'b11001100;
		tb_ldu_cq_info_grab_dest_PR = 7'hf;
		tb_ldu_cq_info_grab_ROB_index = 7'hb;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b1;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h1f05d;
		expected_dtlb_req_cq_index = 'hf;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b1;
		expected_dcache_req_block_offset = 'h777 << 2;
		expected_dcache_req_index = 'h777 >> 4;
		expected_dcache_req_cq_index = 'he;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h2;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h111111;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'hfffffff1;
		expected_WB_PR = 7'h44;
		expected_WB_ROB_index = 7'h4;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b1;
		expected_stamofu_CAM_launch_PA_word = {22'hffffff, 10'h111};
		expected_stamofu_CAM_launch_byte_mask = 4'b1000;
		expected_stamofu_CAM_launch_ROB_index = 7'h4;
		expected_stamofu_CAM_launch_cq_index = 'h4;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h1;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'hb;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b1;
		expected_ldu_cq_info_ret_cq_index = 'h4;
		expected_ldu_cq_info_ret_misaligned = 1'b1;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_dcache_hit = 1'b1;
		expected_ldu_cq_info_ret_is_mem = 1'b1;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = {22'hffffff, 10'h111};
		expected_ldu_cq_info_ret_byte_mask = 4'b1000;
		expected_ldu_cq_info_ret_data = 32'hf1e2d3c4;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h1;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b1;
		expected_ldu_mq_info_ret_is_mem = 1'b1;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'hffffff, 10'h111};
		expected_ldu_mq_info_ret_byte_mask = 4'b1000;
		expected_ldu_mq_info_ret_data = 32'hf1e2d3c4;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'h4;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'hffffff, 10'h111, 2'h3};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'h4;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: f,f: LH p1 1f05d,abe,1000 -> deadbe,abe,1000 mem,pf,cq (ack)",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq",
			"\n\t\tRET: b,d: pf <= ffffffff",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b1;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h1f05d;
		tb_first_try_PO_word = 10'habe;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'hf;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b1;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b1110;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'hffffff;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b11;
		tb_dcache_resp_tag_by_way = {22'h111111, 22'h000000};
		tb_dcache_resp_data_by_way = {32'hbeefdead, 32'h00000000};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b1010;
		tb_ldu_cq_info_grab_mdp_info = 8'b00000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h77;
		tb_ldu_cq_info_grab_ROB_index = 7'he;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b1;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b1;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h1f05d;
		expected_dtlb_req_cq_index = 'hf;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b1;
		expected_dcache_req_block_offset = 'habe << 2;
		expected_dcache_req_index = 'habe >> 4;
		expected_dcache_req_cq_index = 'hf;
		expected_dcache_req_is_mq = 1'b0;
		expected_dcache_req_mq_index = 'h1;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b1;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h111111;
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hffffffff;
		expected_WB_PR = 7'hf;
		expected_WB_ROB_index = 7'hb;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h111111, 10'h777};
		expected_stamofu_CAM_launch_byte_mask = 4'b0111;
		expected_stamofu_CAM_launch_ROB_index = 7'hb;
		expected_stamofu_CAM_launch_cq_index = 'hb;
		expected_stamofu_CAM_launch_is_mq = 1'b1;
		expected_stamofu_CAM_launch_mq_index = 'he;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'he;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'hb;
		expected_ldu_cq_info_ret_misaligned = 1'b1;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_page_fault = 1'b0;
		expected_ldu_cq_info_ret_access_fault = 1'b1;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = {22'h111111, 10'h777};
		expected_ldu_cq_info_ret_byte_mask = 4'b0111;
		expected_ldu_cq_info_ret_data = 32'hffffffff;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h2;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_page_fault = 1'b0;
		expected_ldu_mq_info_ret_access_fault = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'h111111, 10'h777};
		expected_ldu_mq_info_ret_byte_mask = 4'b0111;
		expected_ldu_mq_info_ret_data = 32'hffffffff;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'hb;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h111111, 10'h777, 2'h0};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b1;
		expected_rob_exception_ROB_index = 7'hb;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: i",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: f,f: LH p1 1f05d,abe,1000 -> deadbe,abe,1000 mem,pf,cq (dtlb hit pf, stall)",
			"\n\t\tRET: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq (exception not ready)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b0;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h1f05d;
		tb_first_try_PO_word = 10'habe;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'hf;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b1110;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b0;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'hdeadbe;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b1;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b01;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'hdeadbe};
		tb_dcache_resp_data_by_way = {32'h00000000, 32'hbeefbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0001;
		tb_ldu_cq_info_grab_mdp_info = 8'b11000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h1;
		tb_ldu_cq_info_grab_ROB_index = 7'hf;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b0;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h1f05d;
		expected_dtlb_req_cq_index = 'hf;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h777 << 2;
		expected_dcache_req_index = 'h777 >> 4;
		expected_dcache_req_cq_index = 'he;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h2;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h1f05d;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'hbeefdead;
		expected_WB_PR = 7'h77;
		expected_WB_ROB_index = 7'he;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h111111, 10'h777};
		expected_stamofu_CAM_launch_byte_mask = 4'b0111;
		expected_stamofu_CAM_launch_ROB_index = 7'he;
		expected_stamofu_CAM_launch_cq_index = 'he;
		expected_stamofu_CAM_launch_is_mq = 1'b1;
		expected_stamofu_CAM_launch_mq_index = 'he;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'hf;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'he;
		expected_ldu_cq_info_ret_misaligned = 1'b1;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_dcache_hit = 1'b1;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_data = 32'hbeefdead;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'he;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b1;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'h111111, 10'h777};
		expected_ldu_mq_info_ret_data = 32'hbeefdead;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'he;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {20'h111111, 10'h777, 2'h0};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b1;
		expected_rob_exception_ROB_index = 7'he;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: i",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: f,f: LH p1 1f05d,abe,1000 -> deadbe,abe,1000 mem,pf,cq (dtlb hit pf)",
			"\n\t\tRET: e,s: LW p77 77777,777,0111 -> 111111,777,0111 io,af,mq",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b0;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h1f05d;
		tb_first_try_PO_word = 10'habe;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'hf;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b1110;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b0;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b0;
		tb_dtlb_resp_PPN = 22'h000000;
		tb_dtlb_resp_is_mem = 1'b0;
		tb_dtlb_resp_page_fault = 1'b0;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b10;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'hdeadbe};
		tb_dcache_resp_data_by_way = {32'h00000000, 32'hbeefbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0001;
		tb_ldu_cq_info_grab_mdp_info = 8'b11000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h1;
		tb_ldu_cq_info_grab_ROB_index = 7'hf;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h1f05d;
		expected_dtlb_req_cq_index = 'hf;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h777 << 2;
		expected_dcache_req_index = 'h777 >> 4;
		expected_dcache_req_cq_index = 'he;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h2;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h1f05d;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'hbeefdead;
		expected_WB_PR = 7'h77;
		expected_WB_ROB_index = 7'he;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h111111, 10'h777};
		expected_stamofu_CAM_launch_byte_mask = 4'b0111;
		expected_stamofu_CAM_launch_ROB_index = 7'he;
		expected_stamofu_CAM_launch_cq_index = 'he;
		expected_stamofu_CAM_launch_is_mq = 1'b1;
		expected_stamofu_CAM_launch_mq_index = 'he;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'hf;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'he;
		expected_ldu_cq_info_ret_misaligned = 1'b1;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_dcache_hit = 1'b1;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_data = 32'hbeefdead;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b1;
		expected_ldu_mq_info_ret_mq_index = 'he;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b1;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'h111111, 10'h777};
		expected_ldu_mq_info_ret_data = 32'hbeefdead;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'he;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b1;
		expected_rob_exception_VA = {20'h111111, 10'h777, 2'h0};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b1;
		expected_rob_exception_ROB_index = 7'he;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: i",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: i",
			"\n\t\tRET: f,f: LH p1 1f05d,abe,1000 -> deadbe,abe,1000 mem,pf,cq (dtlb hit pf)",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b0;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h1f05d;
		tb_first_try_PO_word = 10'habe;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'hf;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b1110;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b0;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'hdeadbe;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b1;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b01;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'hdeadbe};
		tb_dcache_resp_data_by_way = {32'h00000000, 32'hbeefbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0001;
		tb_ldu_cq_info_grab_mdp_info = 8'b11000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h1;
		tb_ldu_cq_info_grab_ROB_index = 7'hf;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h1f05d;
		expected_dtlb_req_cq_index = 'hf;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h777 << 2;
		expected_dcache_req_index = 'h777 >> 4;
		expected_dcache_req_cq_index = 'he;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h2;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h111111;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'hffffbeef;
		expected_WB_PR = 7'h1;
		expected_WB_ROB_index = 7'hf;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h01f05d, 10'habe};
		expected_stamofu_CAM_launch_byte_mask = 4'b1000;
		expected_stamofu_CAM_launch_ROB_index = 7'hf;
		expected_stamofu_CAM_launch_cq_index = 'hf;
		expected_stamofu_CAM_launch_is_mq = 1'b0;
		expected_stamofu_CAM_launch_mq_index = 'h1;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'hb;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b1;
		expected_ldu_cq_info_ret_cq_index = 'hf;
		expected_ldu_cq_info_ret_misaligned = 1'b1;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_cq_info_ret_page_fault = 1'b1;
		expected_ldu_cq_info_ret_access_fault = 1'b0;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b1;
		expected_ldu_cq_info_ret_aq_blocking = 1'b1;
		expected_ldu_cq_info_ret_PA_word = {22'h01f05d, 10'habe};
		expected_ldu_cq_info_ret_byte_mask = 4'b1000;
		expected_ldu_cq_info_ret_data = 32'hbeefbeef;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h1;
		expected_ldu_mq_info_ret_page_fault = 1'b1;
		expected_ldu_mq_info_ret_access_fault = 1'b0;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b1;
		expected_ldu_mq_info_ret_aq_blocking = 1'b1;
		expected_ldu_mq_info_ret_PA_word = {22'h01f05d, 10'habe};
		expected_ldu_mq_info_ret_byte_mask = 4'b1000;
		expected_ldu_mq_info_ret_data = 32'hbeefbeef;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'hf;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b1;
		expected_rob_exception_VA = {22'h01f05d, 10'habe, 2'h3};
		expected_rob_exception_page_fault = 1'b1;
		expected_rob_exception_access_fault = 1'b0;
		expected_rob_exception_ROB_index = 7'hf;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ:",
				"\n\t\t\tfirst: i",
				"\n\t\t\tsecond: i",
				"\n\t\t\tdata: i",
			"\n\t\tRESP: i",
			"\n\t\tRET: i",
			"\n\t\taq: mem 6, io i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = 1'b0;
		tb_first_try_is_mq = 1'b0;
		tb_first_try_misaligned = 1'b1;
		tb_first_try_VPN = 20'h1f05d;
		tb_first_try_PO_word = 10'habe;
		tb_first_try_byte_mask = 4'b1000;
		tb_first_try_cq_index = 'hf;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = 1'b0;
		tb_ldu_mq_enq_index = 'h1;
	    // ROB info
		tb_rob_abs_head_index = 7'h3f;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = 1'b1;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h6;
		tb_stamofu_aq_io_aq_active = 1'b0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;
	    // second try
		tb_second_try_valid = 1'b0;
		tb_second_try_is_mq = 1'b1;
		tb_second_try_misaligned = 1'b1;
		tb_second_try_page_fault = 1'b0;
		tb_second_try_access_fault = 1'b1;
		tb_second_try_is_mem = 1'b0;
		tb_second_try_PPN = 22'h111111;
		tb_second_try_PO_word = 10'h777;
		tb_second_try_byte_mask = 4'b1110;
		tb_second_try_cq_index = 'he;
		tb_second_try_mq_index = 'he;
	    // second try feedback
	    // data try
		tb_data_try_valid = 1'b0;
		tb_data_try_do_mispred = 1'b0;
		tb_data_try_data = 32'hffffffff;
		tb_data_try_cq_index = 'hb;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = 1'b0;
	    // dtlb resp
		tb_dtlb_resp_hit = 1'b1;
		tb_dtlb_resp_PPN = 22'hdeadbe;
		tb_dtlb_resp_is_mem = 1'b1;
		tb_dtlb_resp_page_fault = 1'b1;
		tb_dtlb_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = 1'b0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = 2'b01;
		tb_dcache_resp_tag_by_way = {22'h000000, 22'hdeadbe};
		tb_dcache_resp_data_by_way = {32'h00000000, 32'hbeefbeef};
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = 4'b0001;
		tb_ldu_cq_info_grab_mdp_info = 8'b11000000;
		tb_ldu_cq_info_grab_dest_PR = 7'h1;
		tb_ldu_cq_info_grab_ROB_index = 7'hf;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = 1'b0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
		tb_rob_restart_MXR = 1'b0;
		tb_rob_restart_SUM = 1'b0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = 1'b0;
	    // data try
	    // data try feedback
		expected_data_try_ack = 1'b0;
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = 1'b0;
		expected_dtlb_req_ASID = 9'h0;
		expected_dtlb_req_MXR = 1'b0;
		expected_dtlb_req_SUM = 1'b0;
		expected_dtlb_req_VPN = 20'h1f05d;
		expected_dtlb_req_cq_index = 'hf;
		expected_dtlb_req_is_mq = 1'b0;
		expected_dtlb_req_mq_index = 'h1;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h777 << 2;
		expected_dcache_req_index = 'h777 >> 4;
		expected_dcache_req_cq_index = 'he;
		expected_dcache_req_is_mq = 1'b1;
		expected_dcache_req_mq_index = 'h2;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_tag = 22'h111111;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'hffffefbe;
		expected_WB_PR = 7'h1;
		expected_WB_ROB_index = 7'hf;
	    // writeback backpressure from PRF
	    // CAM launch
		expected_stamofu_CAM_launch_valid = 1'b0;
		expected_stamofu_CAM_launch_PA_word = {22'h111111, 10'h777};
		expected_stamofu_CAM_launch_byte_mask = 4'b1110;
		expected_stamofu_CAM_launch_ROB_index = 7'hf;
		expected_stamofu_CAM_launch_cq_index = 'hb;
		expected_stamofu_CAM_launch_is_mq = 1'b1;
		expected_stamofu_CAM_launch_mq_index = 'h2;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = 'hb;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = 1'b0;
		expected_ldu_cq_info_ret_cq_index = 'hb;
		expected_ldu_cq_info_ret_misaligned = 1'b1;
		expected_ldu_cq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_cq_info_ret_page_fault = 1'b0;
		expected_ldu_cq_info_ret_access_fault = 1'b1;
		expected_ldu_cq_info_ret_dcache_hit = 1'b0;
		expected_ldu_cq_info_ret_is_mem = 1'b0;
		expected_ldu_cq_info_ret_aq_blocking = 1'b0;
		expected_ldu_cq_info_ret_PA_word = {22'h111111, 10'h777};
		expected_ldu_cq_info_ret_byte_mask = 4'b1110;
		expected_ldu_cq_info_ret_data = 32'hbeefbeef;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = 1'b0;
		expected_ldu_mq_info_ret_mq_index = 'h2;
		expected_ldu_mq_info_ret_dtlb_hit = 1'b0;
		expected_ldu_mq_info_ret_page_fault = 1'b0;
		expected_ldu_mq_info_ret_access_fault = 1'b1;
		expected_ldu_mq_info_ret_dcache_hit = 1'b0;
		expected_ldu_mq_info_ret_is_mem = 1'b0;
		expected_ldu_mq_info_ret_aq_blocking = 1'b0;
		expected_ldu_mq_info_ret_PA_word = {22'h111111, 10'h777};
		expected_ldu_mq_info_ret_byte_mask = 4'b1110;
		expected_ldu_mq_info_ret_data = 32'hbeefbeef;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = 1'b0;
		expected_mispred_notif_ROB_index = 7'hf;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = 1'b0;
		expected_rob_exception_VA = {22'h111111, 10'h777, 2'h1};
		expected_rob_exception_page_fault = 1'b0;
		expected_rob_exception_access_fault = 1'b1;
		expected_rob_exception_ROB_index = 7'hf;
	    // exception backpressure from ROB
	    // restart from ROB

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