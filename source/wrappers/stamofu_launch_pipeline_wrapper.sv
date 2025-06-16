/*
    Filename: stamofu_launch_pipeline_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_launch_pipeline module. 
    Spec: LOROF/spec/design/stamofu_launch_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_launch_pipeline_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // REQ stage info
	input logic next_REQ_valid,
	input logic next_REQ_is_store,
	input logic next_REQ_is_amo,
	input logic next_REQ_is_fence,
	input logic [3:0] next_REQ_op,
	input logic next_REQ_is_mq,
	input logic next_REQ_misaligned,
	input logic next_REQ_misaligned_exception,
	input logic [VPN_WIDTH-1:0] next_REQ_VPN,
	input logic [PO_WIDTH-3:0] next_REQ_PO_word,
	input logic [3:0] next_REQ_byte_mask,
	input logic [31:0] next_REQ_write_data,
	input logic [LOG_STAMOFU_CQ_ENTRIES-1:0] next_REQ_cq_index,

    // REQ stage feedback
	output logic last_REQ_ack,

    // op enqueue to misaligned queue
	output logic last_stamofu_mq_enq_valid,

    // misaligned queue enqueue feedback
	input logic next_stamofu_mq_enq_ready,
	input logic [LOG_STAMOFU_MQ_ENTRIES-1:0] next_stamofu_mq_enq_index,

    // dtlb req
	output logic last_dtlb_req_valid,
	output logic [VPN_WIDTH-1:0] last_dtlb_req_VPN,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_dtlb_req_cq_index,
	output logic last_dtlb_req_is_mq,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_dtlb_req_mq_index,

    // dtlb req feedback
	input logic next_dtlb_req_ready,

    // dtlb resp
	input logic next_dtlb_resp_hit,
	input logic [PPN_WIDTH-1:0] next_dtlb_resp_PPN,
	input logic next_dtlb_resp_is_mem,
	input logic next_dtlb_resp_page_fault,
	input logic next_dtlb_resp_access_fault,

    // dcache req
	output logic last_dcache_req_valid,
	output logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] last_dcache_req_block_offset,
	output logic [DCACHE_INDEX_WIDTH-1:0] last_dcache_req_index,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_dcache_req_cq_index,
	output logic last_dcache_req_is_mq,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_dcache_req_mq_index,

    // dcache req feedback
	input logic next_dcache_req_ready,

    // dcache resp
	input logic [1:0] next_dcache_resp_valid_by_way,
	input logic [1:0] next_dcache_resp_exclusive_by_way,
	input logic [1:0][DCACHE_TAG_WIDTH-1:0] next_dcache_resp_tag_by_way,

    // dcache resp feedback
	output logic last_dcache_resp_hit_valid,
	output logic last_dcache_resp_hit_exclusive,
	output logic last_dcache_resp_hit_way,
	output logic last_dcache_resp_miss_valid,
	output logic last_dcache_resp_miss_exclusive,
	output logic [DCACHE_TAG_WIDTH-1:0] last_dcache_resp_miss_tag,

    // CAM launch
	output logic last_ldu_CAM_launch_valid,
	output logic [PA_WIDTH-2-1:0] last_ldu_CAM_launch_PA_word,
	output logic [3:0] last_ldu_CAM_launch_byte_mask,
	output logic [31:0] last_ldu_CAM_launch_write_data,
	output logic [LOG_ROB_ENTRIES-1:0] last_ldu_CAM_launch_ROB_index,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_ldu_CAM_launch_cq_index,
	output logic last_ldu_CAM_launch_is_mq,
	output logic [LOG_STAMOFU_MQ_ENTRIES-1:0] last_ldu_CAM_launch_mq_index,

    // central queue info grab
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_cq_info_grab_cq_index,
	input logic next_stamofu_cq_info_grab_mem_aq,
	input logic next_stamofu_cq_info_grab_io_aq,
	input logic next_stamofu_cq_info_grab_mem_rl,
	input logic next_stamofu_cq_info_grab_io_rl,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_cq_info_grab_ROB_index,

    // central queue info ret
	output logic last_stamofu_cq_info_ret_valid,
	output logic [LOG_STAMOFU_CQ_ENTRIES-1:0] last_stamofu_cq_info_ret_cq_index,
	output logic last_stamofu_cq_info_ret_dtlb_hit,
	output logic last_stamofu_cq_info_ret_page_fault,
	output logic last_stamofu_cq_info_ret_access_fault,
	output logic last_stamofu_cq_info_ret_is_mem,
	output logic last_stamofu_cq_info_ret_mem_aq,
	output logic last_stamofu_cq_info_ret_io_aq,
	output logic last_stamofu_cq_info_ret_mem_rl,
	output logic last_stamofu_cq_info_ret_io_rl,
	output logic last_stamofu_cq_info_ret_misaligned,
	output logic last_stamofu_cq_info_ret_misaligned_exception,
	output logic [PA_WIDTH-2-1:0] last_stamofu_cq_info_ret_PA_word,
	output logic [3:0] last_stamofu_cq_info_ret_byte_mask,
	output logic [31:0] last_stamofu_cq_info_ret_data,

    // misaligned queue info ret
	output logic last_stamofu_mq_info_ret_valid,
	output logic [LOG_STAMOFU_MQ_ENTRIES-1:0] last_stamofu_mq_info_ret_mq_index,
	output logic last_stamofu_mq_info_ret_dtlb_hit,
	output logic last_stamofu_mq_info_ret_page_fault,
	output logic last_stamofu_mq_info_ret_access_fault,
	output logic last_stamofu_mq_info_ret_is_mem,
	output logic [PA_WIDTH-2-1:0] last_stamofu_mq_info_ret_PA_word,
	output logic [3:0] last_stamofu_mq_info_ret_byte_mask,
	output logic [31:0] last_stamofu_mq_info_ret_data,

    // aq update
	output logic last_stamofu_aq_update_valid,
	output logic last_stamofu_aq_update_mem_aq,
	output logic last_stamofu_aq_update_io_aq,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_aq_update_ROB_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // REQ stage info
	logic REQ_valid;
	logic REQ_is_store;
	logic REQ_is_amo;
	logic REQ_is_fence;
	logic [3:0] REQ_op;
	logic REQ_is_mq;
	logic REQ_misaligned;
	logic REQ_misaligned_exception;
	logic [VPN_WIDTH-1:0] REQ_VPN;
	logic [PO_WIDTH-3:0] REQ_PO_word;
	logic [3:0] REQ_byte_mask;
	logic [31:0] REQ_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] REQ_cq_index;

    // REQ stage feedback
	logic REQ_ack;

    // op enqueue to misaligned queue
	logic stamofu_mq_enq_valid;

    // misaligned queue enqueue feedback
	logic stamofu_mq_enq_ready;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_enq_index;

    // dtlb req
	logic dtlb_req_valid;
	logic [VPN_WIDTH-1:0] dtlb_req_VPN;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dtlb_req_cq_index;
	logic dtlb_req_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dtlb_req_mq_index;

    // dtlb req feedback
	logic dtlb_req_ready;

    // dtlb resp
	logic dtlb_resp_hit;
	logic [PPN_WIDTH-1:0] dtlb_resp_PPN;
	logic dtlb_resp_is_mem;
	logic dtlb_resp_page_fault;
	logic dtlb_resp_access_fault;

    // dcache req
	logic dcache_req_valid;
	logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] dcache_req_block_offset;
	logic [DCACHE_INDEX_WIDTH-1:0] dcache_req_index;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dcache_req_cq_index;
	logic dcache_req_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dcache_req_mq_index;

    // dcache req feedback
	logic dcache_req_ready;

    // dcache resp
	logic [1:0] dcache_resp_valid_by_way;
	logic [1:0] dcache_resp_exclusive_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] dcache_resp_tag_by_way;

    // dcache resp feedback
	logic dcache_resp_hit_valid;
	logic dcache_resp_hit_exclusive;
	logic dcache_resp_hit_way;
	logic dcache_resp_miss_valid;
	logic dcache_resp_miss_exclusive;
	logic [DCACHE_TAG_WIDTH-1:0] dcache_resp_miss_tag;

    // CAM launch
	logic ldu_CAM_launch_valid;
	logic [PA_WIDTH-2-1:0] ldu_CAM_launch_PA_word;
	logic [3:0] ldu_CAM_launch_byte_mask;
	logic [31:0] ldu_CAM_launch_write_data;
	logic [LOG_ROB_ENTRIES-1:0] ldu_CAM_launch_ROB_index;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_launch_cq_index;
	logic ldu_CAM_launch_is_mq;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] ldu_CAM_launch_mq_index;

    // central queue info grab
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_grab_cq_index;
	logic stamofu_cq_info_grab_mem_aq;
	logic stamofu_cq_info_grab_io_aq;
	logic stamofu_cq_info_grab_mem_rl;
	logic stamofu_cq_info_grab_io_rl;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_info_grab_ROB_index;

    // central queue info ret
	logic stamofu_cq_info_ret_valid;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_ret_cq_index;
	logic stamofu_cq_info_ret_dtlb_hit;
	logic stamofu_cq_info_ret_page_fault;
	logic stamofu_cq_info_ret_access_fault;
	logic stamofu_cq_info_ret_is_mem;
	logic stamofu_cq_info_ret_mem_aq;
	logic stamofu_cq_info_ret_io_aq;
	logic stamofu_cq_info_ret_mem_rl;
	logic stamofu_cq_info_ret_io_rl;
	logic stamofu_cq_info_ret_misaligned;
	logic stamofu_cq_info_ret_misaligned_exception;
	logic [PA_WIDTH-2-1:0] stamofu_cq_info_ret_PA_word;
	logic [3:0] stamofu_cq_info_ret_byte_mask;
	logic [31:0] stamofu_cq_info_ret_data;

    // misaligned queue info ret
	logic stamofu_mq_info_ret_valid;
	logic [LOG_STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_ret_mq_index;
	logic stamofu_mq_info_ret_dtlb_hit;
	logic stamofu_mq_info_ret_page_fault;
	logic stamofu_mq_info_ret_access_fault;
	logic stamofu_mq_info_ret_is_mem;
	logic [PA_WIDTH-2-1:0] stamofu_mq_info_ret_PA_word;
	logic [3:0] stamofu_mq_info_ret_byte_mask;
	logic [31:0] stamofu_mq_info_ret_data;

    // aq update
	logic stamofu_aq_update_valid;
	logic stamofu_aq_update_mem_aq;
	logic stamofu_aq_update_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_update_ROB_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	stamofu_launch_pipeline #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // REQ stage info
			REQ_valid <= '0;
			REQ_is_store <= '0;
			REQ_is_amo <= '0;
			REQ_is_fence <= '0;
			REQ_op <= '0;
			REQ_is_mq <= '0;
			REQ_misaligned <= '0;
			REQ_misaligned_exception <= '0;
			REQ_VPN <= '0;
			REQ_PO_word <= '0;
			REQ_byte_mask <= '0;
			REQ_write_data <= '0;
			REQ_cq_index <= '0;

		    // REQ stage feedback
			last_REQ_ack <= '0;

		    // op enqueue to misaligned queue
			last_stamofu_mq_enq_valid <= '0;

		    // misaligned queue enqueue feedback
			stamofu_mq_enq_ready <= '0;
			stamofu_mq_enq_index <= '0;

		    // dtlb req
			last_dtlb_req_valid <= '0;
			last_dtlb_req_VPN <= '0;
			last_dtlb_req_cq_index <= '0;
			last_dtlb_req_is_mq <= '0;
			last_dtlb_req_mq_index <= '0;

		    // dtlb req feedback
			dtlb_req_ready <= '0;

		    // dtlb resp
			dtlb_resp_hit <= '0;
			dtlb_resp_PPN <= '0;
			dtlb_resp_is_mem <= '0;
			dtlb_resp_page_fault <= '0;
			dtlb_resp_access_fault <= '0;

		    // dcache req
			last_dcache_req_valid <= '0;
			last_dcache_req_block_offset <= '0;
			last_dcache_req_index <= '0;
			last_dcache_req_cq_index <= '0;
			last_dcache_req_is_mq <= '0;
			last_dcache_req_mq_index <= '0;

		    // dcache req feedback
			dcache_req_ready <= '0;

		    // dcache resp
			dcache_resp_valid_by_way <= '0;
			dcache_resp_exclusive_by_way <= '0;
			dcache_resp_tag_by_way <= '0;

		    // dcache resp feedback
			last_dcache_resp_hit_valid <= '0;
			last_dcache_resp_hit_exclusive <= '0;
			last_dcache_resp_hit_way <= '0;
			last_dcache_resp_miss_valid <= '0;
			last_dcache_resp_miss_exclusive <= '0;
			last_dcache_resp_miss_tag <= '0;

		    // CAM launch
			last_ldu_CAM_launch_valid <= '0;
			last_ldu_CAM_launch_PA_word <= '0;
			last_ldu_CAM_launch_byte_mask <= '0;
			last_ldu_CAM_launch_write_data <= '0;
			last_ldu_CAM_launch_ROB_index <= '0;
			last_ldu_CAM_launch_cq_index <= '0;
			last_ldu_CAM_launch_is_mq <= '0;
			last_ldu_CAM_launch_mq_index <= '0;

		    // central queue info grab
			last_stamofu_cq_info_grab_cq_index <= '0;
			stamofu_cq_info_grab_mem_aq <= '0;
			stamofu_cq_info_grab_io_aq <= '0;
			stamofu_cq_info_grab_mem_rl <= '0;
			stamofu_cq_info_grab_io_rl <= '0;
			stamofu_cq_info_grab_ROB_index <= '0;

		    // central queue info ret
			last_stamofu_cq_info_ret_valid <= '0;
			last_stamofu_cq_info_ret_cq_index <= '0;
			last_stamofu_cq_info_ret_dtlb_hit <= '0;
			last_stamofu_cq_info_ret_page_fault <= '0;
			last_stamofu_cq_info_ret_access_fault <= '0;
			last_stamofu_cq_info_ret_is_mem <= '0;
			last_stamofu_cq_info_ret_mem_aq <= '0;
			last_stamofu_cq_info_ret_io_aq <= '0;
			last_stamofu_cq_info_ret_mem_rl <= '0;
			last_stamofu_cq_info_ret_io_rl <= '0;
			last_stamofu_cq_info_ret_misaligned <= '0;
			last_stamofu_cq_info_ret_misaligned_exception <= '0;
			last_stamofu_cq_info_ret_PA_word <= '0;
			last_stamofu_cq_info_ret_byte_mask <= '0;
			last_stamofu_cq_info_ret_data <= '0;

		    // misaligned queue info ret
			last_stamofu_mq_info_ret_valid <= '0;
			last_stamofu_mq_info_ret_mq_index <= '0;
			last_stamofu_mq_info_ret_dtlb_hit <= '0;
			last_stamofu_mq_info_ret_page_fault <= '0;
			last_stamofu_mq_info_ret_access_fault <= '0;
			last_stamofu_mq_info_ret_is_mem <= '0;
			last_stamofu_mq_info_ret_PA_word <= '0;
			last_stamofu_mq_info_ret_byte_mask <= '0;
			last_stamofu_mq_info_ret_data <= '0;

		    // aq update
			last_stamofu_aq_update_valid <= '0;
			last_stamofu_aq_update_mem_aq <= '0;
			last_stamofu_aq_update_io_aq <= '0;
			last_stamofu_aq_update_ROB_index <= '0;
        end
        else begin


		    // REQ stage info
			REQ_valid <= next_REQ_valid;
			REQ_is_store <= next_REQ_is_store;
			REQ_is_amo <= next_REQ_is_amo;
			REQ_is_fence <= next_REQ_is_fence;
			REQ_op <= next_REQ_op;
			REQ_is_mq <= next_REQ_is_mq;
			REQ_misaligned <= next_REQ_misaligned;
			REQ_misaligned_exception <= next_REQ_misaligned_exception;
			REQ_VPN <= next_REQ_VPN;
			REQ_PO_word <= next_REQ_PO_word;
			REQ_byte_mask <= next_REQ_byte_mask;
			REQ_write_data <= next_REQ_write_data;
			REQ_cq_index <= next_REQ_cq_index;

		    // REQ stage feedback
			last_REQ_ack <= REQ_ack;

		    // op enqueue to misaligned queue
			last_stamofu_mq_enq_valid <= stamofu_mq_enq_valid;

		    // misaligned queue enqueue feedback
			stamofu_mq_enq_ready <= next_stamofu_mq_enq_ready;
			stamofu_mq_enq_index <= next_stamofu_mq_enq_index;

		    // dtlb req
			last_dtlb_req_valid <= dtlb_req_valid;
			last_dtlb_req_VPN <= dtlb_req_VPN;
			last_dtlb_req_cq_index <= dtlb_req_cq_index;
			last_dtlb_req_is_mq <= dtlb_req_is_mq;
			last_dtlb_req_mq_index <= dtlb_req_mq_index;

		    // dtlb req feedback
			dtlb_req_ready <= next_dtlb_req_ready;

		    // dtlb resp
			dtlb_resp_hit <= next_dtlb_resp_hit;
			dtlb_resp_PPN <= next_dtlb_resp_PPN;
			dtlb_resp_is_mem <= next_dtlb_resp_is_mem;
			dtlb_resp_page_fault <= next_dtlb_resp_page_fault;
			dtlb_resp_access_fault <= next_dtlb_resp_access_fault;

		    // dcache req
			last_dcache_req_valid <= dcache_req_valid;
			last_dcache_req_block_offset <= dcache_req_block_offset;
			last_dcache_req_index <= dcache_req_index;
			last_dcache_req_cq_index <= dcache_req_cq_index;
			last_dcache_req_is_mq <= dcache_req_is_mq;
			last_dcache_req_mq_index <= dcache_req_mq_index;

		    // dcache req feedback
			dcache_req_ready <= next_dcache_req_ready;

		    // dcache resp
			dcache_resp_valid_by_way <= next_dcache_resp_valid_by_way;
			dcache_resp_exclusive_by_way <= next_dcache_resp_exclusive_by_way;
			dcache_resp_tag_by_way <= next_dcache_resp_tag_by_way;

		    // dcache resp feedback
			last_dcache_resp_hit_valid <= dcache_resp_hit_valid;
			last_dcache_resp_hit_exclusive <= dcache_resp_hit_exclusive;
			last_dcache_resp_hit_way <= dcache_resp_hit_way;
			last_dcache_resp_miss_valid <= dcache_resp_miss_valid;
			last_dcache_resp_miss_exclusive <= dcache_resp_miss_exclusive;
			last_dcache_resp_miss_tag <= dcache_resp_miss_tag;

		    // CAM launch
			last_ldu_CAM_launch_valid <= ldu_CAM_launch_valid;
			last_ldu_CAM_launch_PA_word <= ldu_CAM_launch_PA_word;
			last_ldu_CAM_launch_byte_mask <= ldu_CAM_launch_byte_mask;
			last_ldu_CAM_launch_write_data <= ldu_CAM_launch_write_data;
			last_ldu_CAM_launch_ROB_index <= ldu_CAM_launch_ROB_index;
			last_ldu_CAM_launch_cq_index <= ldu_CAM_launch_cq_index;
			last_ldu_CAM_launch_is_mq <= ldu_CAM_launch_is_mq;
			last_ldu_CAM_launch_mq_index <= ldu_CAM_launch_mq_index;

		    // central queue info grab
			last_stamofu_cq_info_grab_cq_index <= stamofu_cq_info_grab_cq_index;
			stamofu_cq_info_grab_mem_aq <= next_stamofu_cq_info_grab_mem_aq;
			stamofu_cq_info_grab_io_aq <= next_stamofu_cq_info_grab_io_aq;
			stamofu_cq_info_grab_mem_rl <= next_stamofu_cq_info_grab_mem_rl;
			stamofu_cq_info_grab_io_rl <= next_stamofu_cq_info_grab_io_rl;
			stamofu_cq_info_grab_ROB_index <= next_stamofu_cq_info_grab_ROB_index;

		    // central queue info ret
			last_stamofu_cq_info_ret_valid <= stamofu_cq_info_ret_valid;
			last_stamofu_cq_info_ret_cq_index <= stamofu_cq_info_ret_cq_index;
			last_stamofu_cq_info_ret_dtlb_hit <= stamofu_cq_info_ret_dtlb_hit;
			last_stamofu_cq_info_ret_page_fault <= stamofu_cq_info_ret_page_fault;
			last_stamofu_cq_info_ret_access_fault <= stamofu_cq_info_ret_access_fault;
			last_stamofu_cq_info_ret_is_mem <= stamofu_cq_info_ret_is_mem;
			last_stamofu_cq_info_ret_mem_aq <= stamofu_cq_info_ret_mem_aq;
			last_stamofu_cq_info_ret_io_aq <= stamofu_cq_info_ret_io_aq;
			last_stamofu_cq_info_ret_mem_rl <= stamofu_cq_info_ret_mem_rl;
			last_stamofu_cq_info_ret_io_rl <= stamofu_cq_info_ret_io_rl;
			last_stamofu_cq_info_ret_misaligned <= stamofu_cq_info_ret_misaligned;
			last_stamofu_cq_info_ret_misaligned_exception <= stamofu_cq_info_ret_misaligned_exception;
			last_stamofu_cq_info_ret_PA_word <= stamofu_cq_info_ret_PA_word;
			last_stamofu_cq_info_ret_byte_mask <= stamofu_cq_info_ret_byte_mask;
			last_stamofu_cq_info_ret_data <= stamofu_cq_info_ret_data;

		    // misaligned queue info ret
			last_stamofu_mq_info_ret_valid <= stamofu_mq_info_ret_valid;
			last_stamofu_mq_info_ret_mq_index <= stamofu_mq_info_ret_mq_index;
			last_stamofu_mq_info_ret_dtlb_hit <= stamofu_mq_info_ret_dtlb_hit;
			last_stamofu_mq_info_ret_page_fault <= stamofu_mq_info_ret_page_fault;
			last_stamofu_mq_info_ret_access_fault <= stamofu_mq_info_ret_access_fault;
			last_stamofu_mq_info_ret_is_mem <= stamofu_mq_info_ret_is_mem;
			last_stamofu_mq_info_ret_PA_word <= stamofu_mq_info_ret_PA_word;
			last_stamofu_mq_info_ret_byte_mask <= stamofu_mq_info_ret_byte_mask;
			last_stamofu_mq_info_ret_data <= stamofu_mq_info_ret_data;

		    // aq update
			last_stamofu_aq_update_valid <= stamofu_aq_update_valid;
			last_stamofu_aq_update_mem_aq <= stamofu_aq_update_mem_aq;
			last_stamofu_aq_update_io_aq <= stamofu_aq_update_io_aq;
			last_stamofu_aq_update_ROB_index <= stamofu_aq_update_ROB_index;
        end
    end

endmodule