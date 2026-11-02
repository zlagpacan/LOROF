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

module ldu_launch_pipeline_tb #(
	parameter INIT_ASID = 9'h0,
	parameter INIT_EXEC_MODE = M_MODE,
	parameter INIT_VIRTUAL_MODE = 1'b0,
	parameter INIT_MXR = 1'b0,
	parameter INIT_SUM = 1'b0
) ();

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
	logic DUT_first_try_early_ready, expected_first_try_early_ready;

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
	logic tb_second_try_do_mispred;
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

    // this pipe's fast forward notif
	logic DUT_pipe_fast_forward_notif_valid, expected_pipe_fast_forward_notif_valid;
	logic [LOG_PR_COUNT-1:0] DUT_pipe_fast_forward_notif_PR, expected_pipe_fast_forward_notif_PR;

	logic DUT_pipe_fast_forward_data_valid, expected_pipe_fast_forward_data_valid;
	logic [31:0] DUT_pipe_fast_forward_data, expected_pipe_fast_forward_data;

    // CAM launch
	logic DUT_stamofu_CAM_launch_valid, expected_stamofu_CAM_launch_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_stamofu_CAM_launch_cq_index, expected_stamofu_CAM_launch_cq_index;
	logic DUT_stamofu_CAM_launch_is_mq, expected_stamofu_CAM_launch_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_stamofu_CAM_launch_mq_index, expected_stamofu_CAM_launch_mq_index;
	logic [PA_WIDTH-2-1:0] DUT_stamofu_CAM_launch_PA_word, expected_stamofu_CAM_launch_PA_word;
	logic [3:0] DUT_stamofu_CAM_launch_byte_mask, expected_stamofu_CAM_launch_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_CAM_launch_ROB_index, expected_stamofu_CAM_launch_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_CAM_launch_mdp_info, expected_stamofu_CAM_launch_mdp_info;

    // central queue info grab
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_ldu_cq_info_grab_cq_index, expected_ldu_cq_info_grab_cq_index;
	logic [3:0] tb_ldu_cq_info_grab_op;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_cq_info_grab_mdp_info;
	logic [LOG_PR_COUNT-1:0] tb_ldu_cq_info_grab_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_cq_info_grab_ROB_index;

    // central queue info ret
	logic DUT_ldu_cq_info_ret_valid, expected_ldu_cq_info_ret_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_ldu_cq_info_ret_cq_index, expected_ldu_cq_info_ret_cq_index;
	logic DUT_ldu_cq_info_ret_WB_sent, expected_ldu_cq_info_ret_WB_sent;
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
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_ldu_mq_info_ret_cq_index, expected_ldu_mq_info_ret_cq_index;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_ldu_mq_info_ret_mq_index, expected_ldu_mq_info_ret_mq_index;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ldu_mq_info_ret_ROB_index, expected_ldu_mq_info_ret_ROB_index;
	logic DUT_ldu_mq_info_ret_WB_sent, expected_ldu_mq_info_ret_WB_sent;
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
		.INIT_ASID(INIT_ASID),
		.INIT_EXEC_MODE(INIT_EXEC_MODE),
		.INIT_VIRTUAL_MODE(INIT_VIRTUAL_MODE),
		.INIT_MXR(INIT_MXR),
		.INIT_SUM(INIT_SUM)
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
		.first_try_early_ready(DUT_first_try_early_ready),

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
		.second_try_do_mispred(tb_second_try_do_mispred),
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

	    // this pipe's fast forward notif
		.pipe_fast_forward_notif_valid(DUT_pipe_fast_forward_notif_valid),
		.pipe_fast_forward_notif_PR(DUT_pipe_fast_forward_notif_PR),

		.pipe_fast_forward_data_valid(DUT_pipe_fast_forward_data_valid),
		.pipe_fast_forward_data(DUT_pipe_fast_forward_data),

	    // CAM launch
		.stamofu_CAM_launch_valid(DUT_stamofu_CAM_launch_valid),
		.stamofu_CAM_launch_cq_index(DUT_stamofu_CAM_launch_cq_index),
		.stamofu_CAM_launch_is_mq(DUT_stamofu_CAM_launch_is_mq),
		.stamofu_CAM_launch_mq_index(DUT_stamofu_CAM_launch_mq_index),
		.stamofu_CAM_launch_PA_word(DUT_stamofu_CAM_launch_PA_word),
		.stamofu_CAM_launch_byte_mask(DUT_stamofu_CAM_launch_byte_mask),
		.stamofu_CAM_launch_ROB_index(DUT_stamofu_CAM_launch_ROB_index),
		.stamofu_CAM_launch_mdp_info(DUT_stamofu_CAM_launch_mdp_info),

	    // central queue info grab
		.ldu_cq_info_grab_cq_index(DUT_ldu_cq_info_grab_cq_index),
		.ldu_cq_info_grab_op(tb_ldu_cq_info_grab_op),
		.ldu_cq_info_grab_mdp_info(tb_ldu_cq_info_grab_mdp_info),
		.ldu_cq_info_grab_dest_PR(tb_ldu_cq_info_grab_dest_PR),
		.ldu_cq_info_grab_ROB_index(tb_ldu_cq_info_grab_ROB_index),

	    // central queue info ret
		.ldu_cq_info_ret_valid(DUT_ldu_cq_info_ret_valid),
		.ldu_cq_info_ret_cq_index(DUT_ldu_cq_info_ret_cq_index),
		.ldu_cq_info_ret_WB_sent(DUT_ldu_cq_info_ret_WB_sent),
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
		.ldu_mq_info_ret_cq_index(DUT_ldu_mq_info_ret_cq_index),
		.ldu_mq_info_ret_mq_index(DUT_ldu_mq_info_ret_mq_index),
		.ldu_mq_info_ret_ROB_index(DUT_ldu_mq_info_ret_ROB_index),
		.ldu_mq_info_ret_WB_sent(DUT_ldu_mq_info_ret_WB_sent),
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
		if (expected_first_try_early_ready !== DUT_first_try_early_ready) begin
			$display("TB ERROR: expected_first_try_early_ready (%h) != DUT_first_try_early_ready (%h)",
				expected_first_try_early_ready, DUT_first_try_early_ready);
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

		if (expected_pipe_fast_forward_notif_valid !== DUT_pipe_fast_forward_notif_valid) begin
			$display("TB ERROR: expected_pipe_fast_forward_notif_valid (%h) != DUT_pipe_fast_forward_notif_valid (%h)",
				expected_pipe_fast_forward_notif_valid, DUT_pipe_fast_forward_notif_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pipe_fast_forward_notif_PR !== DUT_pipe_fast_forward_notif_PR) begin
			$display("TB ERROR: expected_pipe_fast_forward_notif_PR (%h) != DUT_pipe_fast_forward_notif_PR (%h)",
				expected_pipe_fast_forward_notif_PR, DUT_pipe_fast_forward_notif_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pipe_fast_forward_data_valid !== DUT_pipe_fast_forward_data_valid) begin
			$display("TB ERROR: expected_pipe_fast_forward_data_valid (%h) != DUT_pipe_fast_forward_data_valid (%h)",
				expected_pipe_fast_forward_data_valid, DUT_pipe_fast_forward_data_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pipe_fast_forward_data !== DUT_pipe_fast_forward_data) begin
			$display("TB ERROR: expected_pipe_fast_forward_data (%h) != DUT_pipe_fast_forward_data (%h)",
				expected_pipe_fast_forward_data, DUT_pipe_fast_forward_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_CAM_launch_valid !== DUT_stamofu_CAM_launch_valid) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_valid (%h) != DUT_stamofu_CAM_launch_valid (%h)",
				expected_stamofu_CAM_launch_valid, DUT_stamofu_CAM_launch_valid);
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

		if (expected_stamofu_CAM_launch_mdp_info !== DUT_stamofu_CAM_launch_mdp_info) begin
			$display("TB ERROR: expected_stamofu_CAM_launch_mdp_info (%h) != DUT_stamofu_CAM_launch_mdp_info (%h)",
				expected_stamofu_CAM_launch_mdp_info, DUT_stamofu_CAM_launch_mdp_info);
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

		if (expected_ldu_cq_info_ret_WB_sent !== DUT_ldu_cq_info_ret_WB_sent) begin
			$display("TB ERROR: expected_ldu_cq_info_ret_WB_sent (%h) != DUT_ldu_cq_info_ret_WB_sent (%h)",
				expected_ldu_cq_info_ret_WB_sent, DUT_ldu_cq_info_ret_WB_sent);
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

		if (expected_ldu_mq_info_ret_cq_index !== DUT_ldu_mq_info_ret_cq_index) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_cq_index (%h) != DUT_ldu_mq_info_ret_cq_index (%h)",
				expected_ldu_mq_info_ret_cq_index, DUT_ldu_mq_info_ret_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_mq_index !== DUT_ldu_mq_info_ret_mq_index) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_mq_index (%h) != DUT_ldu_mq_info_ret_mq_index (%h)",
				expected_ldu_mq_info_ret_mq_index, DUT_ldu_mq_info_ret_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_ROB_index !== DUT_ldu_mq_info_ret_ROB_index) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_ROB_index (%h) != DUT_ldu_mq_info_ret_ROB_index (%h)",
				expected_ldu_mq_info_ret_ROB_index, DUT_ldu_mq_info_ret_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mq_info_ret_WB_sent !== DUT_ldu_mq_info_ret_WB_sent) begin
			$display("TB ERROR: expected_ldu_mq_info_ret_WB_sent (%h) != DUT_ldu_mq_info_ret_WB_sent (%h)",
				expected_ldu_mq_info_ret_WB_sent, DUT_ldu_mq_info_ret_WB_sent);
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
		tb_first_try_valid = '0;
		tb_first_try_is_mq = '0;
		tb_first_try_misaligned = '0;
		tb_first_try_VPN = '0;
		tb_first_try_PO_word = '0;
		tb_first_try_byte_mask = '0;
		tb_first_try_cq_index = '0;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = '0;
		tb_ldu_mq_enq_index = '0;
	    // ROB info
		tb_rob_abs_head_index = '0;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = '0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = '0;
		tb_stamofu_aq_io_aq_active = '0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = '0;
	    // second try
		tb_second_try_valid = '0;
		tb_second_try_do_mispred = '0;
		tb_second_try_is_mq = '0;
		tb_second_try_misaligned = '0;
		tb_second_try_page_fault = '0;
		tb_second_try_access_fault = '0;
		tb_second_try_is_mem = '0;
		tb_second_try_PPN = '0;
		tb_second_try_PO_word = '0;
		tb_second_try_byte_mask = '0;
		tb_second_try_cq_index = '0;
		tb_second_try_mq_index = '0;
	    // second try feedback
	    // data try
		tb_data_try_valid = '0;
		tb_data_try_do_mispred = '0;
		tb_data_try_data = '0;
		tb_data_try_cq_index = '0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = '0;
	    // dtlb resp
		tb_dtlb_resp_hit = '0;
		tb_dtlb_resp_PPN = '0;
		tb_dtlb_resp_is_mem = '0;
		tb_dtlb_resp_page_fault = '0;
		tb_dtlb_resp_access_fault = '0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = '0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = '0;
		tb_dcache_resp_tag_by_way = '0;
		tb_dcache_resp_data_by_way = '0;
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = '0;
	    // this pipe's fast forward notif
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = '0;
		tb_ldu_cq_info_grab_mdp_info = '0;
		tb_ldu_cq_info_grab_dest_PR = '0;
		tb_ldu_cq_info_grab_ROB_index = '0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = '0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = '0;
	    // restart from ROB
		tb_rob_restart_valid = '0;
		tb_rob_restart_ASID = '0;
		tb_rob_restart_exec_mode = '0;
		tb_rob_restart_virtual_mode = '0;
		tb_rob_restart_MXR = '0;
		tb_rob_restart_SUM = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_early_ready = '0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = '0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = '0;
	    // data try
	    // data try feedback
		expected_data_try_ack = '0;
	    // dtlb req
		expected_dtlb_req_valid = '0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = '0;
		expected_dtlb_req_ASID = '0;
		expected_dtlb_req_MXR = '0;
		expected_dtlb_req_SUM = '0;
		expected_dtlb_req_VPN = '0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = '0;
		expected_dcache_req_block_offset = '0;
		expected_dcache_req_index = '0;
		expected_dcache_req_cq_index = '0;
		expected_dcache_req_is_mq = '0;
		expected_dcache_req_mq_index = '0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = '0;
		expected_dcache_resp_hit_way = '0;
		expected_dcache_resp_miss_valid = '0;
		expected_dcache_resp_miss_tag = '0;
	    // writeback data to PRF
		expected_WB_valid = '0;
		expected_WB_data = '0;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = '0;
		expected_pipe_fast_forward_notif_PR = '0;
		expected_pipe_fast_forward_data_valid = '0;
		expected_pipe_fast_forward_data = '0;
	    // CAM launch
		expected_stamofu_CAM_launch_valid = '0;
		expected_stamofu_CAM_launch_cq_index = '0;
		expected_stamofu_CAM_launch_is_mq = '0;
		expected_stamofu_CAM_launch_mq_index = '0;
		expected_stamofu_CAM_launch_PA_word = '0;
		expected_stamofu_CAM_launch_byte_mask = '0;
		expected_stamofu_CAM_launch_ROB_index = '0;
		expected_stamofu_CAM_launch_mdp_info = '0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = '0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = '0;
		expected_ldu_cq_info_ret_cq_index = '0;
		expected_ldu_cq_info_ret_WB_sent = '0;
		expected_ldu_cq_info_ret_misaligned = '0;
		expected_ldu_cq_info_ret_dtlb_hit = '0;
		expected_ldu_cq_info_ret_page_fault = '0;
		expected_ldu_cq_info_ret_access_fault = '0;
		expected_ldu_cq_info_ret_dcache_hit = '0;
		expected_ldu_cq_info_ret_is_mem = '0;
		expected_ldu_cq_info_ret_aq_blocking = '0;
		expected_ldu_cq_info_ret_PA_word = '0;
		expected_ldu_cq_info_ret_byte_mask = '0;
		expected_ldu_cq_info_ret_data = '0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = '0;
		expected_ldu_mq_info_ret_cq_index = '0;
		expected_ldu_mq_info_ret_mq_index = '0;
		expected_ldu_mq_info_ret_ROB_index = '0;
		expected_ldu_mq_info_ret_WB_sent = '0;
		expected_ldu_mq_info_ret_dtlb_hit = '0;
		expected_ldu_mq_info_ret_page_fault = '0;
		expected_ldu_mq_info_ret_access_fault = '0;
		expected_ldu_mq_info_ret_dcache_hit = '0;
		expected_ldu_mq_info_ret_is_mem = '0;
		expected_ldu_mq_info_ret_aq_blocking = '0;
		expected_ldu_mq_info_ret_PA_word = '0;
		expected_ldu_mq_info_ret_byte_mask = '0;
		expected_ldu_mq_info_ret_data = '0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = '0;
		expected_mispred_notif_ROB_index = '0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = '0;
		expected_rob_exception_VA = '0;
		expected_rob_exception_page_fault = '0;
		expected_rob_exception_access_fault = '0;
		expected_rob_exception_ROB_index = '0;
	    // exception backpressure from ROB
	    // restart from ROB

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // first try
		tb_first_try_valid = '0;
		tb_first_try_is_mq = '0;
		tb_first_try_misaligned = '0;
		tb_first_try_VPN = '0;
		tb_first_try_PO_word = '0;
		tb_first_try_byte_mask = '0;
		tb_first_try_cq_index = '0;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = '0;
		tb_ldu_mq_enq_index = '0;
	    // ROB info
		tb_rob_abs_head_index = '0;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = '0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = '0;
		tb_stamofu_aq_io_aq_active = '0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = '0;
	    // second try
		tb_second_try_valid = '0;
		tb_second_try_do_mispred = '0;
		tb_second_try_is_mq = '0;
		tb_second_try_misaligned = '0;
		tb_second_try_page_fault = '0;
		tb_second_try_access_fault = '0;
		tb_second_try_is_mem = '0;
		tb_second_try_PPN = '0;
		tb_second_try_PO_word = '0;
		tb_second_try_byte_mask = '0;
		tb_second_try_cq_index = '0;
		tb_second_try_mq_index = '0;
	    // second try feedback
	    // data try
		tb_data_try_valid = '0;
		tb_data_try_do_mispred = '0;
		tb_data_try_data = '0;
		tb_data_try_cq_index = '0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = '0;
	    // dtlb resp
		tb_dtlb_resp_hit = '0;
		tb_dtlb_resp_PPN = '0;
		tb_dtlb_resp_is_mem = '0;
		tb_dtlb_resp_page_fault = '0;
		tb_dtlb_resp_access_fault = '0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = '0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = '0;
		tb_dcache_resp_tag_by_way = '0;
		tb_dcache_resp_data_by_way = '0;
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = '0;
	    // this pipe's fast forward notif
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = '0;
		tb_ldu_cq_info_grab_mdp_info = '0;
		tb_ldu_cq_info_grab_dest_PR = '0;
		tb_ldu_cq_info_grab_ROB_index = '0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = '0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = '0;
	    // restart from ROB
		tb_rob_restart_valid = '0;
		tb_rob_restart_ASID = '0;
		tb_rob_restart_exec_mode = '0;
		tb_rob_restart_virtual_mode = '0;
		tb_rob_restart_MXR = '0;
		tb_rob_restart_SUM = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_early_ready = '0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = '0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = '0;
	    // data try
	    // data try feedback
		expected_data_try_ack = '0;
	    // dtlb req
		expected_dtlb_req_valid = '0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = '0;
		expected_dtlb_req_ASID = '0;
		expected_dtlb_req_MXR = '0;
		expected_dtlb_req_SUM = '0;
		expected_dtlb_req_VPN = '0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = '0;
		expected_dcache_req_block_offset = '0;
		expected_dcache_req_index = '0;
		expected_dcache_req_cq_index = '0;
		expected_dcache_req_is_mq = '0;
		expected_dcache_req_mq_index = '0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = '0;
		expected_dcache_resp_hit_way = '0;
		expected_dcache_resp_miss_valid = '0;
		expected_dcache_resp_miss_tag = '0;
	    // writeback data to PRF
		expected_WB_valid = '0;
		expected_WB_data = '0;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = '0;
		expected_pipe_fast_forward_notif_PR = '0;
		expected_pipe_fast_forward_data_valid = '0;
		expected_pipe_fast_forward_data = '0;
	    // CAM launch
		expected_stamofu_CAM_launch_valid = '0;
		expected_stamofu_CAM_launch_cq_index = '0;
		expected_stamofu_CAM_launch_is_mq = '0;
		expected_stamofu_CAM_launch_mq_index = '0;
		expected_stamofu_CAM_launch_PA_word = '0;
		expected_stamofu_CAM_launch_byte_mask = '0;
		expected_stamofu_CAM_launch_ROB_index = '0;
		expected_stamofu_CAM_launch_mdp_info = '0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = '0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = '0;
		expected_ldu_cq_info_ret_cq_index = '0;
		expected_ldu_cq_info_ret_WB_sent = '0;
		expected_ldu_cq_info_ret_misaligned = '0;
		expected_ldu_cq_info_ret_dtlb_hit = '0;
		expected_ldu_cq_info_ret_page_fault = '0;
		expected_ldu_cq_info_ret_access_fault = '0;
		expected_ldu_cq_info_ret_dcache_hit = '0;
		expected_ldu_cq_info_ret_is_mem = '0;
		expected_ldu_cq_info_ret_aq_blocking = '0;
		expected_ldu_cq_info_ret_PA_word = '0;
		expected_ldu_cq_info_ret_byte_mask = '0;
		expected_ldu_cq_info_ret_data = '0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = '0;
		expected_ldu_mq_info_ret_cq_index = '0;
		expected_ldu_mq_info_ret_mq_index = '0;
		expected_ldu_mq_info_ret_ROB_index = '0;
		expected_ldu_mq_info_ret_WB_sent = '0;
		expected_ldu_mq_info_ret_dtlb_hit = '0;
		expected_ldu_mq_info_ret_page_fault = '0;
		expected_ldu_mq_info_ret_access_fault = '0;
		expected_ldu_mq_info_ret_dcache_hit = '0;
		expected_ldu_mq_info_ret_is_mem = '0;
		expected_ldu_mq_info_ret_aq_blocking = '0;
		expected_ldu_mq_info_ret_PA_word = '0;
		expected_ldu_mq_info_ret_byte_mask = '0;
		expected_ldu_mq_info_ret_data = '0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = '0;
		expected_mispred_notif_ROB_index = '0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = '0;
		expected_rob_exception_VA = '0;
		expected_rob_exception_page_fault = '0;
		expected_rob_exception_access_fault = '0;
		expected_rob_exception_ROB_index = '0;
	    // exception backpressure from ROB
	    // restart from ROB

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
	    // first try
		tb_first_try_valid = '0;
		tb_first_try_is_mq = '0;
		tb_first_try_misaligned = '0;
		tb_first_try_VPN = '0;
		tb_first_try_PO_word = '0;
		tb_first_try_byte_mask = '0;
		tb_first_try_cq_index = '0;
	    // first try feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_ldu_mq_enq_ready = '0;
		tb_ldu_mq_enq_index = '0;
	    // ROB info
		tb_rob_abs_head_index = '0;
	    // acquire advertisement
		tb_stamofu_aq_mem_aq_active = '0;
		tb_stamofu_aq_mem_aq_oldest_abs_ROB_index = '0;
		tb_stamofu_aq_io_aq_active = '0;
		tb_stamofu_aq_io_aq_oldest_abs_ROB_index = '0;
	    // second try
		tb_second_try_valid = '0;
		tb_second_try_do_mispred = '0;
		tb_second_try_is_mq = '0;
		tb_second_try_misaligned = '0;
		tb_second_try_page_fault = '0;
		tb_second_try_access_fault = '0;
		tb_second_try_is_mem = '0;
		tb_second_try_PPN = '0;
		tb_second_try_PO_word = '0;
		tb_second_try_byte_mask = '0;
		tb_second_try_cq_index = '0;
		tb_second_try_mq_index = '0;
	    // second try feedback
	    // data try
		tb_data_try_valid = '0;
		tb_data_try_do_mispred = '0;
		tb_data_try_data = '0;
		tb_data_try_cq_index = '0;
	    // data try feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_ready = '0;
	    // dtlb resp
		tb_dtlb_resp_hit = '0;
		tb_dtlb_resp_PPN = '0;
		tb_dtlb_resp_is_mem = '0;
		tb_dtlb_resp_page_fault = '0;
		tb_dtlb_resp_access_fault = '0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_ready = '0;
	    // dcache resp
		tb_dcache_resp_valid_by_way = '0;
		tb_dcache_resp_tag_by_way = '0;
		tb_dcache_resp_data_by_way = '0;
	    // dcache resp feedback
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = '0;
	    // this pipe's fast forward notif
	    // CAM launch
	    // central queue info grab
		tb_ldu_cq_info_grab_op = '0;
		tb_ldu_cq_info_grab_mdp_info = '0;
		tb_ldu_cq_info_grab_dest_PR = '0;
		tb_ldu_cq_info_grab_ROB_index = '0;
	    // central queue info ret
	    // misaligned queue info ret
	    // misprediction notification to ROB
	    // misprediction notification backpressure from ROB
		tb_mispred_notif_ready = '0;
	    // exception to ROB
	    // exception backpressure from ROB
		tb_rob_exception_ready = '0;
	    // restart from ROB
		tb_rob_restart_valid = '0;
		tb_rob_restart_ASID = '0;
		tb_rob_restart_exec_mode = '0;
		tb_rob_restart_virtual_mode = '0;
		tb_rob_restart_MXR = '0;
		tb_rob_restart_SUM = '0;

		@(negedge CLK);

		// outputs:

	    // first try
	    // first try feedback
		expected_first_try_early_ready = '0;
	    // op enqueue to misaligned queue
		expected_ldu_mq_enq_valid = '0;
	    // misaligned queue enqueue feedback
	    // ROB info
	    // acquire advertisement
	    // second try
	    // second try feedback
		expected_second_try_ack = '0;
	    // data try
	    // data try feedback
		expected_data_try_ack = '0;
	    // dtlb req
		expected_dtlb_req_valid = '0;
		expected_dtlb_req_exec_mode = M_MODE;
		expected_dtlb_req_virtual_mode = '0;
		expected_dtlb_req_ASID = '0;
		expected_dtlb_req_MXR = '0;
		expected_dtlb_req_SUM = '0;
		expected_dtlb_req_VPN = '0;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = '0;
		expected_dcache_req_block_offset = '0;
		expected_dcache_req_index = '0;
		expected_dcache_req_cq_index = '0;
		expected_dcache_req_is_mq = '0;
		expected_dcache_req_mq_index = '0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = '0;
		expected_dcache_resp_hit_way = '0;
		expected_dcache_resp_miss_valid = '0;
		expected_dcache_resp_miss_tag = '0;
	    // writeback data to PRF
		expected_WB_valid = '0;
		expected_WB_data = '0;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = '0;
		expected_pipe_fast_forward_notif_PR = '0;
		expected_pipe_fast_forward_data_valid = '0;
		expected_pipe_fast_forward_data = '0;
	    // CAM launch
		expected_stamofu_CAM_launch_valid = '0;
		expected_stamofu_CAM_launch_cq_index = '0;
		expected_stamofu_CAM_launch_is_mq = '0;
		expected_stamofu_CAM_launch_mq_index = '0;
		expected_stamofu_CAM_launch_PA_word = '0;
		expected_stamofu_CAM_launch_byte_mask = '0;
		expected_stamofu_CAM_launch_ROB_index = '0;
		expected_stamofu_CAM_launch_mdp_info = '0;
	    // central queue info grab
		expected_ldu_cq_info_grab_cq_index = '0;
	    // central queue info ret
		expected_ldu_cq_info_ret_valid = '0;
		expected_ldu_cq_info_ret_cq_index = '0;
		expected_ldu_cq_info_ret_WB_sent = '0;
		expected_ldu_cq_info_ret_misaligned = '0;
		expected_ldu_cq_info_ret_dtlb_hit = '0;
		expected_ldu_cq_info_ret_page_fault = '0;
		expected_ldu_cq_info_ret_access_fault = '0;
		expected_ldu_cq_info_ret_dcache_hit = '0;
		expected_ldu_cq_info_ret_is_mem = '0;
		expected_ldu_cq_info_ret_aq_blocking = '0;
		expected_ldu_cq_info_ret_PA_word = '0;
		expected_ldu_cq_info_ret_byte_mask = '0;
		expected_ldu_cq_info_ret_data = '0;
	    // misaligned queue info ret
		expected_ldu_mq_info_ret_valid = '0;
		expected_ldu_mq_info_ret_cq_index = '0;
		expected_ldu_mq_info_ret_mq_index = '0;
		expected_ldu_mq_info_ret_ROB_index = '0;
		expected_ldu_mq_info_ret_WB_sent = '0;
		expected_ldu_mq_info_ret_dtlb_hit = '0;
		expected_ldu_mq_info_ret_page_fault = '0;
		expected_ldu_mq_info_ret_access_fault = '0;
		expected_ldu_mq_info_ret_dcache_hit = '0;
		expected_ldu_mq_info_ret_is_mem = '0;
		expected_ldu_mq_info_ret_aq_blocking = '0;
		expected_ldu_mq_info_ret_PA_word = '0;
		expected_ldu_mq_info_ret_byte_mask = '0;
		expected_ldu_mq_info_ret_data = '0;
	    // misprediction notification to ROB
		expected_mispred_notif_valid = '0;
		expected_mispred_notif_ROB_index = '0;
	    // misprediction notification backpressure from ROB
	    // exception to ROB
		expected_rob_exception_valid = '0;
		expected_rob_exception_VA = '0;
		expected_rob_exception_page_fault = '0;
		expected_rob_exception_access_fault = '0;
		expected_rob_exception_ROB_index = '0;
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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule