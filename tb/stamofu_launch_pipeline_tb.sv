/*
    Filename: stamofu_launch_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_launch_pipeline module. 
    Spec: LOROF/spec/design/stamofu_launch_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_launch_pipeline_tb ();

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


    // REQ stage info
	logic tb_REQ_valid;
	logic tb_REQ_is_store;
	logic tb_REQ_is_amo;
	logic tb_REQ_is_fence;
	logic [3:0] tb_REQ_op;
	logic tb_REQ_is_mq;
	logic tb_REQ_misaligned;
	logic tb_REQ_misaligned_exception;
	logic [VPN_WIDTH-1:0] tb_REQ_VPN;
	logic [PO_WIDTH-3:0] tb_REQ_PO_word;
	logic [3:0] tb_REQ_byte_mask;
	logic [31:0] tb_REQ_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_REQ_cq_index;

    // REQ stage feedback
	logic DUT_REQ_ack, expected_REQ_ack;

    // op enqueue to misaligned queue
	logic DUT_stamofu_mq_enq_valid, expected_stamofu_mq_enq_valid;

    // misaligned queue enqueue feedback
	logic tb_stamofu_mq_enq_ready;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] tb_stamofu_mq_enq_index;

    // dtlb req
	logic DUT_dtlb_req_valid, expected_dtlb_req_valid;
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

    // dcache req feedback
	logic tb_dcache_req_ready;

    // dcache resp
	logic [1:0] tb_dcache_resp_valid_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] tb_dcache_resp_tag_by_way;

    // dcache resp feedback
	logic DUT_dcache_resp_hit_valid, expected_dcache_resp_hit_valid;
	logic DUT_dcache_resp_hit_way, expected_dcache_resp_hit_way;
	logic DUT_dcache_resp_miss_valid, expected_dcache_resp_miss_valid;
	logic DUT_dcache_resp_miss_exclusive, expected_dcache_resp_miss_exclusive;
	logic [DCACHE_TAG_WIDTH-1:0] DUT_dcache_resp_miss_tag, expected_dcache_resp_miss_tag;

    // CAM launch
	logic DUT_ldu_CAM_launch_valid, expected_ldu_CAM_launch_valid;
	logic [PA_WIDTH-2-1:0] DUT_ldu_CAM_launch_PA_word, expected_ldu_CAM_launch_PA_word;
	logic [3:0] DUT_ldu_CAM_launch_byte_mask, expected_ldu_CAM_launch_byte_mask;
	logic [31:0] DUT_ldu_CAM_launch_write_data, expected_ldu_CAM_launch_write_data;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ldu_CAM_launch_ROB_index, expected_ldu_CAM_launch_ROB_index;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_ldu_CAM_launch_cq_index, expected_ldu_CAM_launch_cq_index;
	logic DUT_ldu_CAM_launch_is_mq, expected_ldu_CAM_launch_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] DUT_ldu_CAM_launch_mq_index, expected_ldu_CAM_launch_mq_index;

    // central queue info grab
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_cq_info_grab_cq_index, expected_stamofu_cq_info_grab_cq_index;
	logic tb_stamofu_cq_info_grab_mem_aq;
	logic tb_stamofu_cq_info_grab_io_aq;
	logic tb_stamofu_cq_info_grab_mem_rl;
	logic tb_stamofu_cq_info_grab_io_rl;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_cq_info_grab_ROB_index;

    // central queue info ret
	logic DUT_stamofu_cq_info_ret_valid, expected_stamofu_cq_info_ret_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_cq_info_ret_cq_index, expected_stamofu_cq_info_ret_cq_index;
	logic DUT_stamofu_cq_info_ret_dtlb_hit, expected_stamofu_cq_info_ret_dtlb_hit;
	logic DUT_stamofu_cq_info_ret_page_fault, expected_stamofu_cq_info_ret_page_fault;
	logic DUT_stamofu_cq_info_ret_access_fault, expected_stamofu_cq_info_ret_access_fault;
	logic DUT_stamofu_cq_info_ret_is_mem, expected_stamofu_cq_info_ret_is_mem;
	logic DUT_stamofu_cq_info_ret_mem_aq, expected_stamofu_cq_info_ret_mem_aq;
	logic DUT_stamofu_cq_info_ret_io_aq, expected_stamofu_cq_info_ret_io_aq;
	logic DUT_stamofu_cq_info_ret_mem_rl, expected_stamofu_cq_info_ret_mem_rl;
	logic DUT_stamofu_cq_info_ret_io_rl, expected_stamofu_cq_info_ret_io_rl;
	logic DUT_stamofu_cq_info_ret_misaligned, expected_stamofu_cq_info_ret_misaligned;
	logic DUT_stamofu_cq_info_ret_misaligned_exception, expected_stamofu_cq_info_ret_misaligned_exception;
	logic [PA_WIDTH-2-1:0] DUT_stamofu_cq_info_ret_PA_word, expected_stamofu_cq_info_ret_PA_word;
	logic [3:0] DUT_stamofu_cq_info_ret_byte_mask, expected_stamofu_cq_info_ret_byte_mask;
	logic [31:0] DUT_stamofu_cq_info_ret_data, expected_stamofu_cq_info_ret_data;

    // misaligned queue info ret
	logic DUT_stamofu_mq_info_ret_valid, expected_stamofu_mq_info_ret_valid;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] DUT_stamofu_mq_info_ret_mq_index, expected_stamofu_mq_info_ret_mq_index;
	logic DUT_stamofu_mq_info_ret_dtlb_hit, expected_stamofu_mq_info_ret_dtlb_hit;
	logic DUT_stamofu_mq_info_ret_page_fault, expected_stamofu_mq_info_ret_page_fault;
	logic DUT_stamofu_mq_info_ret_access_fault, expected_stamofu_mq_info_ret_access_fault;
	logic DUT_stamofu_mq_info_ret_is_mem, expected_stamofu_mq_info_ret_is_mem;
	logic [PA_WIDTH-2-1:0] DUT_stamofu_mq_info_ret_PA_word, expected_stamofu_mq_info_ret_PA_word;
	logic [3:0] DUT_stamofu_mq_info_ret_byte_mask, expected_stamofu_mq_info_ret_byte_mask;
	logic [31:0] DUT_stamofu_mq_info_ret_data, expected_stamofu_mq_info_ret_data;

    // aq update
	logic DUT_stamofu_aq_update_valid, expected_stamofu_aq_update_valid;
	logic DUT_stamofu_aq_update_mem_aq, expected_stamofu_aq_update_mem_aq;
	logic DUT_stamofu_aq_update_io_aq, expected_stamofu_aq_update_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_aq_update_ROB_index, expected_stamofu_aq_update_ROB_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_launch_pipeline #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // REQ stage info
		.REQ_valid(tb_REQ_valid),
		.REQ_is_store(tb_REQ_is_store),
		.REQ_is_amo(tb_REQ_is_amo),
		.REQ_is_fence(tb_REQ_is_fence),
		.REQ_op(tb_REQ_op),
		.REQ_is_mq(tb_REQ_is_mq),
		.REQ_misaligned(tb_REQ_misaligned),
		.REQ_misaligned_exception(tb_REQ_misaligned_exception),
		.REQ_VPN(tb_REQ_VPN),
		.REQ_PO_word(tb_REQ_PO_word),
		.REQ_byte_mask(tb_REQ_byte_mask),
		.REQ_write_data(tb_REQ_write_data),
		.REQ_cq_index(tb_REQ_cq_index),

	    // REQ stage feedback
		.REQ_ack(DUT_REQ_ack),

	    // op enqueue to misaligned queue
		.stamofu_mq_enq_valid(DUT_stamofu_mq_enq_valid),

	    // misaligned queue enqueue feedback
		.stamofu_mq_enq_ready(tb_stamofu_mq_enq_ready),
		.stamofu_mq_enq_index(tb_stamofu_mq_enq_index),

	    // dtlb req
		.dtlb_req_valid(DUT_dtlb_req_valid),
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

	    // dcache req feedback
		.dcache_req_ready(tb_dcache_req_ready),

	    // dcache resp
		.dcache_resp_valid_by_way(tb_dcache_resp_valid_by_way),
		.dcache_resp_tag_by_way(tb_dcache_resp_tag_by_way),

	    // dcache resp feedback
		.dcache_resp_hit_valid(DUT_dcache_resp_hit_valid),
		.dcache_resp_hit_way(DUT_dcache_resp_hit_way),
		.dcache_resp_miss_valid(DUT_dcache_resp_miss_valid),
		.dcache_resp_miss_exclusive(DUT_dcache_resp_miss_exclusive),
		.dcache_resp_miss_tag(DUT_dcache_resp_miss_tag),

	    // CAM launch
		.ldu_CAM_launch_valid(DUT_ldu_CAM_launch_valid),
		.ldu_CAM_launch_PA_word(DUT_ldu_CAM_launch_PA_word),
		.ldu_CAM_launch_byte_mask(DUT_ldu_CAM_launch_byte_mask),
		.ldu_CAM_launch_write_data(DUT_ldu_CAM_launch_write_data),
		.ldu_CAM_launch_ROB_index(DUT_ldu_CAM_launch_ROB_index),
		.ldu_CAM_launch_cq_index(DUT_ldu_CAM_launch_cq_index),
		.ldu_CAM_launch_is_mq(DUT_ldu_CAM_launch_is_mq),
		.ldu_CAM_launch_mq_index(DUT_ldu_CAM_launch_mq_index),

	    // central queue info grab
		.stamofu_cq_info_grab_cq_index(DUT_stamofu_cq_info_grab_cq_index),
		.stamofu_cq_info_grab_mem_aq(tb_stamofu_cq_info_grab_mem_aq),
		.stamofu_cq_info_grab_io_aq(tb_stamofu_cq_info_grab_io_aq),
		.stamofu_cq_info_grab_mem_rl(tb_stamofu_cq_info_grab_mem_rl),
		.stamofu_cq_info_grab_io_rl(tb_stamofu_cq_info_grab_io_rl),
		.stamofu_cq_info_grab_ROB_index(tb_stamofu_cq_info_grab_ROB_index),

	    // central queue info ret
		.stamofu_cq_info_ret_valid(DUT_stamofu_cq_info_ret_valid),
		.stamofu_cq_info_ret_cq_index(DUT_stamofu_cq_info_ret_cq_index),
		.stamofu_cq_info_ret_dtlb_hit(DUT_stamofu_cq_info_ret_dtlb_hit),
		.stamofu_cq_info_ret_page_fault(DUT_stamofu_cq_info_ret_page_fault),
		.stamofu_cq_info_ret_access_fault(DUT_stamofu_cq_info_ret_access_fault),
		.stamofu_cq_info_ret_is_mem(DUT_stamofu_cq_info_ret_is_mem),
		.stamofu_cq_info_ret_mem_aq(DUT_stamofu_cq_info_ret_mem_aq),
		.stamofu_cq_info_ret_io_aq(DUT_stamofu_cq_info_ret_io_aq),
		.stamofu_cq_info_ret_mem_rl(DUT_stamofu_cq_info_ret_mem_rl),
		.stamofu_cq_info_ret_io_rl(DUT_stamofu_cq_info_ret_io_rl),
		.stamofu_cq_info_ret_misaligned(DUT_stamofu_cq_info_ret_misaligned),
		.stamofu_cq_info_ret_misaligned_exception(DUT_stamofu_cq_info_ret_misaligned_exception),
		.stamofu_cq_info_ret_PA_word(DUT_stamofu_cq_info_ret_PA_word),
		.stamofu_cq_info_ret_byte_mask(DUT_stamofu_cq_info_ret_byte_mask),
		.stamofu_cq_info_ret_data(DUT_stamofu_cq_info_ret_data),

	    // misaligned queue info ret
		.stamofu_mq_info_ret_valid(DUT_stamofu_mq_info_ret_valid),
		.stamofu_mq_info_ret_mq_index(DUT_stamofu_mq_info_ret_mq_index),
		.stamofu_mq_info_ret_dtlb_hit(DUT_stamofu_mq_info_ret_dtlb_hit),
		.stamofu_mq_info_ret_page_fault(DUT_stamofu_mq_info_ret_page_fault),
		.stamofu_mq_info_ret_access_fault(DUT_stamofu_mq_info_ret_access_fault),
		.stamofu_mq_info_ret_is_mem(DUT_stamofu_mq_info_ret_is_mem),
		.stamofu_mq_info_ret_PA_word(DUT_stamofu_mq_info_ret_PA_word),
		.stamofu_mq_info_ret_byte_mask(DUT_stamofu_mq_info_ret_byte_mask),
		.stamofu_mq_info_ret_data(DUT_stamofu_mq_info_ret_data),

	    // aq update
		.stamofu_aq_update_valid(DUT_stamofu_aq_update_valid),
		.stamofu_aq_update_mem_aq(DUT_stamofu_aq_update_mem_aq),
		.stamofu_aq_update_io_aq(DUT_stamofu_aq_update_io_aq),
		.stamofu_aq_update_ROB_index(DUT_stamofu_aq_update_ROB_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_REQ_ack !== DUT_REQ_ack) begin
			$display("TB ERROR: expected_REQ_ack (%h) != DUT_REQ_ack (%h)",
				expected_REQ_ack, DUT_REQ_ack);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_enq_valid !== DUT_stamofu_mq_enq_valid) begin
			$display("TB ERROR: expected_stamofu_mq_enq_valid (%h) != DUT_stamofu_mq_enq_valid (%h)",
				expected_stamofu_mq_enq_valid, DUT_stamofu_mq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_valid !== DUT_dtlb_req_valid) begin
			$display("TB ERROR: expected_dtlb_req_valid (%h) != DUT_dtlb_req_valid (%h)",
				expected_dtlb_req_valid, DUT_dtlb_req_valid);
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

		if (expected_dcache_resp_miss_exclusive !== DUT_dcache_resp_miss_exclusive) begin
			$display("TB ERROR: expected_dcache_resp_miss_exclusive (%h) != DUT_dcache_resp_miss_exclusive (%h)",
				expected_dcache_resp_miss_exclusive, DUT_dcache_resp_miss_exclusive);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_miss_tag !== DUT_dcache_resp_miss_tag) begin
			$display("TB ERROR: expected_dcache_resp_miss_tag (%h) != DUT_dcache_resp_miss_tag (%h)",
				expected_dcache_resp_miss_tag, DUT_dcache_resp_miss_tag);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_CAM_launch_valid !== DUT_ldu_CAM_launch_valid) begin
			$display("TB ERROR: expected_ldu_CAM_launch_valid (%h) != DUT_ldu_CAM_launch_valid (%h)",
				expected_ldu_CAM_launch_valid, DUT_ldu_CAM_launch_valid);
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

		if (expected_ldu_CAM_launch_ROB_index !== DUT_ldu_CAM_launch_ROB_index) begin
			$display("TB ERROR: expected_ldu_CAM_launch_ROB_index (%h) != DUT_ldu_CAM_launch_ROB_index (%h)",
				expected_ldu_CAM_launch_ROB_index, DUT_ldu_CAM_launch_ROB_index);
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

		if (expected_stamofu_cq_info_grab_cq_index !== DUT_stamofu_cq_info_grab_cq_index) begin
			$display("TB ERROR: expected_stamofu_cq_info_grab_cq_index (%h) != DUT_stamofu_cq_info_grab_cq_index (%h)",
				expected_stamofu_cq_info_grab_cq_index, DUT_stamofu_cq_info_grab_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_valid !== DUT_stamofu_cq_info_ret_valid) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_valid (%h) != DUT_stamofu_cq_info_ret_valid (%h)",
				expected_stamofu_cq_info_ret_valid, DUT_stamofu_cq_info_ret_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_cq_index !== DUT_stamofu_cq_info_ret_cq_index) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_cq_index (%h) != DUT_stamofu_cq_info_ret_cq_index (%h)",
				expected_stamofu_cq_info_ret_cq_index, DUT_stamofu_cq_info_ret_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_dtlb_hit !== DUT_stamofu_cq_info_ret_dtlb_hit) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_dtlb_hit (%h) != DUT_stamofu_cq_info_ret_dtlb_hit (%h)",
				expected_stamofu_cq_info_ret_dtlb_hit, DUT_stamofu_cq_info_ret_dtlb_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_page_fault !== DUT_stamofu_cq_info_ret_page_fault) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_page_fault (%h) != DUT_stamofu_cq_info_ret_page_fault (%h)",
				expected_stamofu_cq_info_ret_page_fault, DUT_stamofu_cq_info_ret_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_access_fault !== DUT_stamofu_cq_info_ret_access_fault) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_access_fault (%h) != DUT_stamofu_cq_info_ret_access_fault (%h)",
				expected_stamofu_cq_info_ret_access_fault, DUT_stamofu_cq_info_ret_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_is_mem !== DUT_stamofu_cq_info_ret_is_mem) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_is_mem (%h) != DUT_stamofu_cq_info_ret_is_mem (%h)",
				expected_stamofu_cq_info_ret_is_mem, DUT_stamofu_cq_info_ret_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_mem_aq !== DUT_stamofu_cq_info_ret_mem_aq) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_mem_aq (%h) != DUT_stamofu_cq_info_ret_mem_aq (%h)",
				expected_stamofu_cq_info_ret_mem_aq, DUT_stamofu_cq_info_ret_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_io_aq !== DUT_stamofu_cq_info_ret_io_aq) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_io_aq (%h) != DUT_stamofu_cq_info_ret_io_aq (%h)",
				expected_stamofu_cq_info_ret_io_aq, DUT_stamofu_cq_info_ret_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_mem_rl !== DUT_stamofu_cq_info_ret_mem_rl) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_mem_rl (%h) != DUT_stamofu_cq_info_ret_mem_rl (%h)",
				expected_stamofu_cq_info_ret_mem_rl, DUT_stamofu_cq_info_ret_mem_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_io_rl !== DUT_stamofu_cq_info_ret_io_rl) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_io_rl (%h) != DUT_stamofu_cq_info_ret_io_rl (%h)",
				expected_stamofu_cq_info_ret_io_rl, DUT_stamofu_cq_info_ret_io_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_misaligned !== DUT_stamofu_cq_info_ret_misaligned) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_misaligned (%h) != DUT_stamofu_cq_info_ret_misaligned (%h)",
				expected_stamofu_cq_info_ret_misaligned, DUT_stamofu_cq_info_ret_misaligned);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_misaligned_exception !== DUT_stamofu_cq_info_ret_misaligned_exception) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_misaligned_exception (%h) != DUT_stamofu_cq_info_ret_misaligned_exception (%h)",
				expected_stamofu_cq_info_ret_misaligned_exception, DUT_stamofu_cq_info_ret_misaligned_exception);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_PA_word !== DUT_stamofu_cq_info_ret_PA_word) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_PA_word (%h) != DUT_stamofu_cq_info_ret_PA_word (%h)",
				expected_stamofu_cq_info_ret_PA_word, DUT_stamofu_cq_info_ret_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_byte_mask !== DUT_stamofu_cq_info_ret_byte_mask) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_byte_mask (%h) != DUT_stamofu_cq_info_ret_byte_mask (%h)",
				expected_stamofu_cq_info_ret_byte_mask, DUT_stamofu_cq_info_ret_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_info_ret_data !== DUT_stamofu_cq_info_ret_data) begin
			$display("TB ERROR: expected_stamofu_cq_info_ret_data (%h) != DUT_stamofu_cq_info_ret_data (%h)",
				expected_stamofu_cq_info_ret_data, DUT_stamofu_cq_info_ret_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_valid !== DUT_stamofu_mq_info_ret_valid) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_valid (%h) != DUT_stamofu_mq_info_ret_valid (%h)",
				expected_stamofu_mq_info_ret_valid, DUT_stamofu_mq_info_ret_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_mq_index !== DUT_stamofu_mq_info_ret_mq_index) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_mq_index (%h) != DUT_stamofu_mq_info_ret_mq_index (%h)",
				expected_stamofu_mq_info_ret_mq_index, DUT_stamofu_mq_info_ret_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_dtlb_hit !== DUT_stamofu_mq_info_ret_dtlb_hit) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_dtlb_hit (%h) != DUT_stamofu_mq_info_ret_dtlb_hit (%h)",
				expected_stamofu_mq_info_ret_dtlb_hit, DUT_stamofu_mq_info_ret_dtlb_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_page_fault !== DUT_stamofu_mq_info_ret_page_fault) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_page_fault (%h) != DUT_stamofu_mq_info_ret_page_fault (%h)",
				expected_stamofu_mq_info_ret_page_fault, DUT_stamofu_mq_info_ret_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_access_fault !== DUT_stamofu_mq_info_ret_access_fault) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_access_fault (%h) != DUT_stamofu_mq_info_ret_access_fault (%h)",
				expected_stamofu_mq_info_ret_access_fault, DUT_stamofu_mq_info_ret_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_is_mem !== DUT_stamofu_mq_info_ret_is_mem) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_is_mem (%h) != DUT_stamofu_mq_info_ret_is_mem (%h)",
				expected_stamofu_mq_info_ret_is_mem, DUT_stamofu_mq_info_ret_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_PA_word !== DUT_stamofu_mq_info_ret_PA_word) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_PA_word (%h) != DUT_stamofu_mq_info_ret_PA_word (%h)",
				expected_stamofu_mq_info_ret_PA_word, DUT_stamofu_mq_info_ret_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_byte_mask !== DUT_stamofu_mq_info_ret_byte_mask) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_byte_mask (%h) != DUT_stamofu_mq_info_ret_byte_mask (%h)",
				expected_stamofu_mq_info_ret_byte_mask, DUT_stamofu_mq_info_ret_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_mq_info_ret_data !== DUT_stamofu_mq_info_ret_data) begin
			$display("TB ERROR: expected_stamofu_mq_info_ret_data (%h) != DUT_stamofu_mq_info_ret_data (%h)",
				expected_stamofu_mq_info_ret_data, DUT_stamofu_mq_info_ret_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_update_valid !== DUT_stamofu_aq_update_valid) begin
			$display("TB ERROR: expected_stamofu_aq_update_valid (%h) != DUT_stamofu_aq_update_valid (%h)",
				expected_stamofu_aq_update_valid, DUT_stamofu_aq_update_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_update_mem_aq !== DUT_stamofu_aq_update_mem_aq) begin
			$display("TB ERROR: expected_stamofu_aq_update_mem_aq (%h) != DUT_stamofu_aq_update_mem_aq (%h)",
				expected_stamofu_aq_update_mem_aq, DUT_stamofu_aq_update_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_update_io_aq !== DUT_stamofu_aq_update_io_aq) begin
			$display("TB ERROR: expected_stamofu_aq_update_io_aq (%h) != DUT_stamofu_aq_update_io_aq (%h)",
				expected_stamofu_aq_update_io_aq, DUT_stamofu_aq_update_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_update_ROB_index !== DUT_stamofu_aq_update_ROB_index) begin
			$display("TB ERROR: expected_stamofu_aq_update_ROB_index (%h) != DUT_stamofu_aq_update_ROB_index (%h)",
				expected_stamofu_aq_update_ROB_index, DUT_stamofu_aq_update_ROB_index);
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
	    // REQ stage info
		tb_REQ_valid = 1'b0;
		tb_REQ_is_store = 1'b0;
		tb_REQ_is_amo = 1'b0;
		tb_REQ_is_fence = 1'b0;
		tb_REQ_op = 4'b0000;
		tb_REQ_is_mq = 1'b0;
		tb_REQ_misaligned = 1'b0;
		tb_REQ_misaligned_exception = 1'b0;
		tb_REQ_VPN = 20'h00000;
		tb_REQ_PO_word = 10'h000;
		tb_REQ_byte_mask = 4'b0000;
		tb_REQ_write_data = 32'h00000000;
		tb_REQ_cq_index = 0;
	    // REQ stage feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_stamofu_mq_enq_ready = 1'b0;
		tb_stamofu_mq_enq_index = 0;
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
	    // dcache resp feedback
	    // CAM launch
	    // central queue info grab
		tb_stamofu_cq_info_grab_mem_aq = 1'b0;
		tb_stamofu_cq_info_grab_io_aq = 1'b0;
		tb_stamofu_cq_info_grab_mem_rl = 1'b0;
		tb_stamofu_cq_info_grab_io_rl = 1'b0;
		tb_stamofu_cq_info_grab_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // aq update

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage info
	    // REQ stage feedback
		expected_REQ_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_stamofu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_VPN = 20'h00000;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h000 << 2;
		expected_dcache_req_index = 'h000 >> 4;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_exclusive = 1'b1;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // CAM launch
		expected_ldu_CAM_launch_valid = 1'b0;
		expected_ldu_CAM_launch_PA_word = {22'h000000, 10'h000};
		expected_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_ldu_CAM_launch_write_data = 32'h00000000;
		expected_ldu_CAM_launch_ROB_index = 7'h00;
		expected_ldu_CAM_launch_cq_index = 0;
		expected_ldu_CAM_launch_is_mq = 1'b0;
		expected_ldu_CAM_launch_mq_index = 0;
	    // central queue info grab
		expected_stamofu_cq_info_grab_cq_index = 0;
	    // central queue info ret
		expected_stamofu_cq_info_ret_valid = 1'b0;
		expected_stamofu_cq_info_ret_cq_index = 0;
		expected_stamofu_cq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_cq_info_ret_page_fault = 1'b0;
		expected_stamofu_cq_info_ret_access_fault = 1'b0;
		expected_stamofu_cq_info_ret_is_mem = 1'b0;
		expected_stamofu_cq_info_ret_mem_aq = 1'b0;
		expected_stamofu_cq_info_ret_io_aq = 1'b0;
		expected_stamofu_cq_info_ret_mem_rl = 1'b0;
		expected_stamofu_cq_info_ret_io_rl = 1'b0;
		expected_stamofu_cq_info_ret_misaligned = 1'b0;
		expected_stamofu_cq_info_ret_misaligned_exception = 1'b0;
		expected_stamofu_cq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_cq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_cq_info_ret_data = 32'h00000000;
	    // misaligned queue info ret
		expected_stamofu_mq_info_ret_valid = 1'b0;
		expected_stamofu_mq_info_ret_mq_index = 0;
		expected_stamofu_mq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_mq_info_ret_page_fault = 1'b0;
		expected_stamofu_mq_info_ret_access_fault = 1'b0;
		expected_stamofu_mq_info_ret_is_mem = 1'b0;
		expected_stamofu_mq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_mq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_mq_info_ret_data = 32'h00000000;
	    // aq update
		expected_stamofu_aq_update_valid = 1'b0;
		expected_stamofu_aq_update_mem_aq = 1'b0;
		expected_stamofu_aq_update_io_aq = 1'b0;
		expected_stamofu_aq_update_ROB_index = 7'h00;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage info
		tb_REQ_valid = 1'b0;
		tb_REQ_is_store = 1'b0;
		tb_REQ_is_amo = 1'b0;
		tb_REQ_is_fence = 1'b0;
		tb_REQ_op = 4'b0000;
		tb_REQ_is_mq = 1'b0;
		tb_REQ_misaligned = 1'b0;
		tb_REQ_misaligned_exception = 1'b0;
		tb_REQ_VPN = 20'h00000;
		tb_REQ_PO_word = 10'h000;
		tb_REQ_byte_mask = 4'b0000;
		tb_REQ_write_data = 32'h00000000;
		tb_REQ_cq_index = 0;
	    // REQ stage feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_stamofu_mq_enq_ready = 1'b0;
		tb_stamofu_mq_enq_index = 0;
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
	    // dcache resp feedback
	    // CAM launch
	    // central queue info grab
		tb_stamofu_cq_info_grab_mem_aq = 1'b0;
		tb_stamofu_cq_info_grab_io_aq = 1'b0;
		tb_stamofu_cq_info_grab_mem_rl = 1'b0;
		tb_stamofu_cq_info_grab_io_rl = 1'b0;
		tb_stamofu_cq_info_grab_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // aq update

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage info
	    // REQ stage feedback
		expected_REQ_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_stamofu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_VPN = 20'h00000;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h000 << 2;
		expected_dcache_req_index = 'h000 >> 4;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_exclusive = 1'b1;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // CAM launch
		expected_ldu_CAM_launch_valid = 1'b0;
		expected_ldu_CAM_launch_PA_word = {22'h000000, 10'h000};
		expected_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_ldu_CAM_launch_write_data = 32'h00000000;
		expected_ldu_CAM_launch_ROB_index = 7'h00;
		expected_ldu_CAM_launch_cq_index = 0;
		expected_ldu_CAM_launch_is_mq = 1'b0;
		expected_ldu_CAM_launch_mq_index = 0;
	    // central queue info grab
		expected_stamofu_cq_info_grab_cq_index = 0;
	    // central queue info ret
		expected_stamofu_cq_info_ret_valid = 1'b0;
		expected_stamofu_cq_info_ret_cq_index = 0;
		expected_stamofu_cq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_cq_info_ret_page_fault = 1'b0;
		expected_stamofu_cq_info_ret_access_fault = 1'b0;
		expected_stamofu_cq_info_ret_is_mem = 1'b0;
		expected_stamofu_cq_info_ret_mem_aq = 1'b0;
		expected_stamofu_cq_info_ret_io_aq = 1'b0;
		expected_stamofu_cq_info_ret_mem_rl = 1'b0;
		expected_stamofu_cq_info_ret_io_rl = 1'b0;
		expected_stamofu_cq_info_ret_misaligned = 1'b0;
		expected_stamofu_cq_info_ret_misaligned_exception = 1'b0;
		expected_stamofu_cq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_cq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_cq_info_ret_data = 32'h00000000;
	    // misaligned queue info ret
		expected_stamofu_mq_info_ret_valid = 1'b0;
		expected_stamofu_mq_info_ret_mq_index = 0;
		expected_stamofu_mq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_mq_info_ret_page_fault = 1'b0;
		expected_stamofu_mq_info_ret_access_fault = 1'b0;
		expected_stamofu_mq_info_ret_is_mem = 1'b0;
		expected_stamofu_mq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_mq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_mq_info_ret_data = 32'h00000000;
	    // aq update
		expected_stamofu_aq_update_valid = 1'b0;
		expected_stamofu_aq_update_mem_aq = 1'b0;
		expected_stamofu_aq_update_io_aq = 1'b0;
		expected_stamofu_aq_update_ROB_index = 7'h00;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ: i",
			"\n\t\tRESP: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage info
		tb_REQ_valid = 1'b0;
		tb_REQ_is_store = 1'b0;
		tb_REQ_is_amo = 1'b0;
		tb_REQ_is_fence = 1'b0;
		tb_REQ_op = 4'b0000;
		tb_REQ_is_mq = 1'b0;
		tb_REQ_misaligned = 1'b0;
		tb_REQ_misaligned_exception = 1'b0;
		tb_REQ_VPN = 20'h00000;
		tb_REQ_PO_word = 10'h000;
		tb_REQ_byte_mask = 4'b0000;
		tb_REQ_write_data = 32'h00000000;
		tb_REQ_cq_index = 0;
	    // REQ stage feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_stamofu_mq_enq_ready = 1'b0;
		tb_stamofu_mq_enq_index = 0;
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
	    // dcache resp feedback
	    // CAM launch
	    // central queue info grab
		tb_stamofu_cq_info_grab_mem_aq = 1'b0;
		tb_stamofu_cq_info_grab_io_aq = 1'b0;
		tb_stamofu_cq_info_grab_mem_rl = 1'b0;
		tb_stamofu_cq_info_grab_io_rl = 1'b0;
		tb_stamofu_cq_info_grab_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // aq update

		@(negedge CLK);

		// outputs:

	    // REQ stage info
	    // REQ stage feedback
		expected_REQ_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_stamofu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_VPN = 20'h00000;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h000 << 2;
		expected_dcache_req_index = 'h000 >> 4;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_exclusive = 1'b1;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // CAM launch
		expected_ldu_CAM_launch_valid = 1'b0;
		expected_ldu_CAM_launch_PA_word = {22'h000000, 10'h000};
		expected_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_ldu_CAM_launch_write_data = 32'h00000000;
		expected_ldu_CAM_launch_ROB_index = 7'h00;
		expected_ldu_CAM_launch_cq_index = 0;
		expected_ldu_CAM_launch_is_mq = 1'b0;
		expected_ldu_CAM_launch_mq_index = 0;
	    // central queue info grab
		expected_stamofu_cq_info_grab_cq_index = 0;
	    // central queue info ret
		expected_stamofu_cq_info_ret_valid = 1'b0;
		expected_stamofu_cq_info_ret_cq_index = 0;
		expected_stamofu_cq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_cq_info_ret_page_fault = 1'b0;
		expected_stamofu_cq_info_ret_access_fault = 1'b0;
		expected_stamofu_cq_info_ret_is_mem = 1'b0;
		expected_stamofu_cq_info_ret_mem_aq = 1'b0;
		expected_stamofu_cq_info_ret_io_aq = 1'b0;
		expected_stamofu_cq_info_ret_mem_rl = 1'b0;
		expected_stamofu_cq_info_ret_io_rl = 1'b0;
		expected_stamofu_cq_info_ret_misaligned = 1'b0;
		expected_stamofu_cq_info_ret_misaligned_exception = 1'b0;
		expected_stamofu_cq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_cq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_cq_info_ret_data = 32'h00000000;
	    // misaligned queue info ret
		expected_stamofu_mq_info_ret_valid = 1'b0;
		expected_stamofu_mq_info_ret_mq_index = 0;
		expected_stamofu_mq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_mq_info_ret_page_fault = 1'b0;
		expected_stamofu_mq_info_ret_access_fault = 1'b0;
		expected_stamofu_mq_info_ret_is_mem = 1'b0;
		expected_stamofu_mq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_mq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_mq_info_ret_data = 32'h00000000;
	    // aq update
		expected_stamofu_aq_update_valid = 1'b0;
		expected_stamofu_aq_update_mem_aq = 1'b0;
		expected_stamofu_aq_update_io_aq = 1'b0;
		expected_stamofu_aq_update_ROB_index = 7'h00;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tREQ: i",
			"\n\t\tRESP: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage info
		tb_REQ_valid = 1'b0;
		tb_REQ_is_store = 1'b0;
		tb_REQ_is_amo = 1'b0;
		tb_REQ_is_fence = 1'b0;
		tb_REQ_op = 4'b0000;
		tb_REQ_is_mq = 1'b0;
		tb_REQ_misaligned = 1'b0;
		tb_REQ_misaligned_exception = 1'b0;
		tb_REQ_VPN = 20'h00000;
		tb_REQ_PO_word = 10'h000;
		tb_REQ_byte_mask = 4'b0000;
		tb_REQ_write_data = 32'h00000000;
		tb_REQ_cq_index = 0;
	    // REQ stage feedback
	    // op enqueue to misaligned queue
	    // misaligned queue enqueue feedback
		tb_stamofu_mq_enq_ready = 1'b0;
		tb_stamofu_mq_enq_index = 0;
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
	    // dcache resp feedback
	    // CAM launch
	    // central queue info grab
		tb_stamofu_cq_info_grab_mem_aq = 1'b0;
		tb_stamofu_cq_info_grab_io_aq = 1'b0;
		tb_stamofu_cq_info_grab_mem_rl = 1'b0;
		tb_stamofu_cq_info_grab_io_rl = 1'b0;
		tb_stamofu_cq_info_grab_ROB_index = 7'h00;
	    // central queue info ret
	    // misaligned queue info ret
	    // aq update

		@(negedge CLK);

		// outputs:

	    // REQ stage info
	    // REQ stage feedback
		expected_REQ_ack = 1'b0;
	    // op enqueue to misaligned queue
		expected_stamofu_mq_enq_valid = 1'b0;
	    // misaligned queue enqueue feedback
	    // dtlb req
		expected_dtlb_req_valid = 1'b0;
		expected_dtlb_req_VPN = 20'h00000;
	    // dtlb req feedback
	    // dtlb resp
	    // dcache req
		expected_dcache_req_valid = 1'b0;
		expected_dcache_req_block_offset = 'h000 << 2;
		expected_dcache_req_index = 'h000 >> 4;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_hit_valid = 1'b0;
		expected_dcache_resp_hit_way = 1'b0;
		expected_dcache_resp_miss_valid = 1'b0;
		expected_dcache_resp_miss_exclusive = 1'b1;
		expected_dcache_resp_miss_tag = 22'h000000;
	    // CAM launch
		expected_ldu_CAM_launch_valid = 1'b0;
		expected_ldu_CAM_launch_PA_word = {22'h000000, 10'h000};
		expected_ldu_CAM_launch_byte_mask = 4'b0000;
		expected_ldu_CAM_launch_write_data = 32'h00000000;
		expected_ldu_CAM_launch_ROB_index = 7'h00;
		expected_ldu_CAM_launch_cq_index = 0;
		expected_ldu_CAM_launch_is_mq = 1'b0;
		expected_ldu_CAM_launch_mq_index = 0;
	    // central queue info grab
		expected_stamofu_cq_info_grab_cq_index = 0;
	    // central queue info ret
		expected_stamofu_cq_info_ret_valid = 1'b0;
		expected_stamofu_cq_info_ret_cq_index = 0;
		expected_stamofu_cq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_cq_info_ret_page_fault = 1'b0;
		expected_stamofu_cq_info_ret_access_fault = 1'b0;
		expected_stamofu_cq_info_ret_is_mem = 1'b0;
		expected_stamofu_cq_info_ret_mem_aq = 1'b0;
		expected_stamofu_cq_info_ret_io_aq = 1'b0;
		expected_stamofu_cq_info_ret_mem_rl = 1'b0;
		expected_stamofu_cq_info_ret_io_rl = 1'b0;
		expected_stamofu_cq_info_ret_misaligned = 1'b0;
		expected_stamofu_cq_info_ret_misaligned_exception = 1'b0;
		expected_stamofu_cq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_cq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_cq_info_ret_data = 32'h00000000;
	    // misaligned queue info ret
		expected_stamofu_mq_info_ret_valid = 1'b0;
		expected_stamofu_mq_info_ret_mq_index = 0;
		expected_stamofu_mq_info_ret_dtlb_hit = 1'b0;
		expected_stamofu_mq_info_ret_page_fault = 1'b0;
		expected_stamofu_mq_info_ret_access_fault = 1'b0;
		expected_stamofu_mq_info_ret_is_mem = 1'b0;
		expected_stamofu_mq_info_ret_PA_word = {22'h000000, 10'h000};
		expected_stamofu_mq_info_ret_byte_mask = 4'b0000;
		expected_stamofu_mq_info_ret_data = 32'h00000000;
	    // aq update
		expected_stamofu_aq_update_valid = 1'b0;
		expected_stamofu_aq_update_mem_aq = 1'b0;
		expected_stamofu_aq_update_io_aq = 1'b0;
		expected_stamofu_aq_update_ROB_index = 7'h00;

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