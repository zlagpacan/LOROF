/*
    Filename: ldu_launch_pipeline_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ldu_launch_pipeline module. 
    Spec: LOROF/spec/design/ldu_launch_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module ldu_launch_pipeline_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // first try
	input logic next_first_try_valid,
	input logic next_first_try_is_mq,
	input logic next_first_try_misaligned,
	input logic [VPN_WIDTH-1:0] next_first_try_VPN,
	input logic [PO_WIDTH-3:0] next_first_try_PO_word,
	input logic [3:0] next_first_try_byte_mask,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_first_try_cq_index,

    // first try feedback
	output logic last_first_try_ack,

    // op enqueue to misaligned queue
	output logic last_ldu_mq_enq_valid,

    // misaligned queue enqueue feedback
	input logic next_ldu_mq_enq_ready,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_ldu_mq_enq_index,

    // ROB info
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_abs_head_index,

    // acquire advertisement
	input logic next_stamofu_aq_mem_aq_active,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_aq_mem_aq_oldest_abs_ROB_index,
	input logic next_stamofu_aq_io_aq_active,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_aq_io_aq_oldest_abs_ROB_index,

    // second try
	input logic next_second_try_valid,
	input logic next_second_try_is_mq,
	input logic next_second_try_misaligned,
	input logic next_second_try_page_fault,
	input logic next_second_try_access_fault,
	input logic next_second_try_is_mem,
	input logic [PPN_WIDTH-1:0] next_second_try_PPN,
	input logic [PO_WIDTH-3:0] next_second_try_PO_word,
	input logic [3:0] next_second_try_byte_mask,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_second_try_cq_index,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_second_try_mq_index,

    // second try feedback
	output logic last_second_try_ack,

    // data try
	input logic next_data_try_valid,
	input logic next_data_try_do_mispred,
	input logic [31:0] next_data_try_data,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_data_try_cq_index,

    // data try feedback
	output logic last_data_try_ack,

    // dtlb req
	output logic last_dtlb_req_valid,
	output logic [1:0] last_dtlb_req_exec_mode,
	output logic last_dtlb_req_virtual_mode,
	output logic [ASID_WIDTH-1:0] last_dtlb_req_ASID,
	output logic last_dtlb_req_MXR,
	output logic last_dtlb_req_SUM,
	output logic [VPN_WIDTH-1:0] last_dtlb_req_VPN,

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

    // dcache req feedback
	input logic next_dcache_req_ready,

    // dcache resp
	input logic [1:0] next_dcache_resp_valid_by_way,
	input logic [1:0][DCACHE_TAG_WIDTH-1:0] next_dcache_resp_tag_by_way,
	input logic [1:0][31:0] next_dcache_resp_data_by_way,

    // dcache resp feedback
	output logic last_dcache_resp_hit_valid,
	output logic last_dcache_resp_hit_way,
	output logic last_dcache_resp_miss_valid,
	output logic [DCACHE_TAG_WIDTH-1:0] last_dcache_resp_miss_tag,

    // writeback data to PRF
	output logic last_WB_valid,
	output logic [31:0] last_WB_data,
	output logic [LOG_PR_COUNT-1:0] last_WB_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_WB_ROB_index,

    // writeback backpressure from PRF
	input logic next_WB_ready,

    // CAM launch
	output logic last_stamofu_CAM_launch_valid,
	output logic [PA_WIDTH-2-1:0] last_stamofu_CAM_launch_PA_word,
	output logic [3:0] last_stamofu_CAM_launch_byte_mask,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_CAM_launch_ROB_index,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_stamofu_CAM_launch_cq_index,
	output logic last_stamofu_CAM_launch_is_mq,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_stamofu_CAM_launch_mq_index,

    // central queue info grab
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_ldu_cq_info_grab_cq_index,
	input logic [3:0] next_ldu_cq_info_grab_op,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_cq_info_grab_mdp_info,
	input logic [LOG_PR_COUNT-1:0] next_ldu_cq_info_grab_dest_PR,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_cq_info_grab_ROB_index,

    // central queue info ret
	output logic last_ldu_cq_info_ret_valid,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_ldu_cq_info_ret_cq_index,
	output logic last_ldu_cq_info_ret_misaligned,
	output logic last_ldu_cq_info_ret_dtlb_hit,
	output logic last_ldu_cq_info_ret_page_fault,
	output logic last_ldu_cq_info_ret_access_fault,
	output logic last_ldu_cq_info_ret_dcache_hit,
	output logic last_ldu_cq_info_ret_is_mem,
	output logic last_ldu_cq_info_ret_aq_blocking,
	output logic [PA_WIDTH-2-1:0] last_ldu_cq_info_ret_PA_word,
	output logic [3:0] last_ldu_cq_info_ret_byte_mask,
	output logic [31:0] last_ldu_cq_info_ret_data,

    // misaligned queue info ret
	output logic last_ldu_mq_info_ret_valid,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_ldu_mq_info_ret_mq_index,
	output logic last_ldu_mq_info_ret_dtlb_hit,
	output logic last_ldu_mq_info_ret_page_fault,
	output logic last_ldu_mq_info_ret_access_fault,
	output logic last_ldu_mq_info_ret_dcache_hit,
	output logic last_ldu_mq_info_ret_is_mem,
	output logic last_ldu_mq_info_ret_aq_blocking,
	output logic [PA_WIDTH-2-1:0] last_ldu_mq_info_ret_PA_word,
	output logic [3:0] last_ldu_mq_info_ret_byte_mask,
	output logic [31:0] last_ldu_mq_info_ret_data,

    // misprediction notification to ROB
	output logic last_mispred_notif_valid,
	output logic [LOG_ROB_ENTRIES-1:0] last_mispred_notif_ROB_index,

    // misprediction notification backpressure from ROB
	input logic next_mispred_notif_ready,

    // exception to ROB
	output logic last_rob_exception_valid,
	output logic [VA_WIDTH-1:0] last_rob_exception_VA,
	output logic last_rob_exception_page_fault,
	output logic last_rob_exception_access_fault,
	output logic [LOG_ROB_ENTRIES-1:0] last_rob_exception_ROB_index,

    // exception backpressure from ROB
	input logic next_rob_exception_ready,

    // restart from ROB
	input logic next_rob_restart_valid,
	input logic [8:0] next_rob_restart_ASID,
	input logic [1:0] next_rob_restart_exec_mode,
	input logic next_rob_restart_virtual_mode,
	input logic next_rob_restart_MXR,
	input logic next_rob_restart_SUM
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // first try
	logic first_try_valid;
	logic first_try_is_mq;
	logic first_try_misaligned;
	logic [VPN_WIDTH-1:0] first_try_VPN;
	logic [PO_WIDTH-3:0] first_try_PO_word;
	logic [3:0] first_try_byte_mask;
	logic [LOG_LDU_CQ_ENTRIES-1:0] first_try_cq_index;

    // first try feedback
	logic first_try_ack;

    // op enqueue to misaligned queue
	logic ldu_mq_enq_valid;

    // misaligned queue enqueue feedback
	logic ldu_mq_enq_ready;
	logic [LOG_LDU_MQ_ENTRIES-1:0] ldu_mq_enq_index;

    // ROB info
	logic [LOG_ROB_ENTRIES-1:0] rob_abs_head_index;

    // acquire advertisement
	logic stamofu_aq_mem_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_mem_aq_oldest_abs_ROB_index;
	logic stamofu_aq_io_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_io_aq_oldest_abs_ROB_index;

    // second try
	logic second_try_valid;
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
	logic second_try_ack;

    // data try
	logic data_try_valid;
	logic data_try_do_mispred;
	logic [31:0] data_try_data;
	logic [LOG_LDU_CQ_ENTRIES-1:0] data_try_cq_index;

    // data try feedback
	logic data_try_ack;

    // dtlb req
	logic dtlb_req_valid;
	logic [1:0] dtlb_req_exec_mode;
	logic dtlb_req_virtual_mode;
	logic [ASID_WIDTH-1:0] dtlb_req_ASID;
	logic dtlb_req_MXR;
	logic dtlb_req_SUM;
	logic [VPN_WIDTH-1:0] dtlb_req_VPN;

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

    // dcache req feedback
	logic dcache_req_ready;

    // dcache resp
	logic [1:0] dcache_resp_valid_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] dcache_resp_tag_by_way;
	logic [1:0][31:0] dcache_resp_data_by_way;

    // dcache resp feedback
	logic dcache_resp_hit_valid;
	logic dcache_resp_hit_way;
	logic dcache_resp_miss_valid;
	logic [DCACHE_TAG_WIDTH-1:0] dcache_resp_miss_tag;

    // writeback data to PRF
	logic WB_valid;
	logic [31:0] WB_data;
	logic [LOG_PR_COUNT-1:0] WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index;

    // writeback backpressure from PRF
	logic WB_ready;

    // CAM launch
	logic stamofu_CAM_launch_valid;
	logic [PA_WIDTH-2-1:0] stamofu_CAM_launch_PA_word;
	logic [3:0] stamofu_CAM_launch_byte_mask;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_CAM_launch_ROB_index;
	logic [LOG_LDU_CQ_ENTRIES-1:0] stamofu_CAM_launch_cq_index;
	logic stamofu_CAM_launch_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] stamofu_CAM_launch_mq_index;

    // central queue info grab
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_info_grab_cq_index;
	logic [3:0] ldu_cq_info_grab_op;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_info_grab_mdp_info;
	logic [LOG_PR_COUNT-1:0] ldu_cq_info_grab_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_info_grab_ROB_index;

    // central queue info ret
	logic ldu_cq_info_ret_valid;
	logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_info_ret_cq_index;
	logic ldu_cq_info_ret_misaligned;
	logic ldu_cq_info_ret_dtlb_hit;
	logic ldu_cq_info_ret_page_fault;
	logic ldu_cq_info_ret_access_fault;
	logic ldu_cq_info_ret_dcache_hit;
	logic ldu_cq_info_ret_is_mem;
	logic ldu_cq_info_ret_aq_blocking;
	logic [PA_WIDTH-2-1:0] ldu_cq_info_ret_PA_word;
	logic [3:0] ldu_cq_info_ret_byte_mask;
	logic [31:0] ldu_cq_info_ret_data;

    // misaligned queue info ret
	logic ldu_mq_info_ret_valid;
	logic [LOG_LDU_MQ_ENTRIES-1:0] ldu_mq_info_ret_mq_index;
	logic ldu_mq_info_ret_dtlb_hit;
	logic ldu_mq_info_ret_page_fault;
	logic ldu_mq_info_ret_access_fault;
	logic ldu_mq_info_ret_dcache_hit;
	logic ldu_mq_info_ret_is_mem;
	logic ldu_mq_info_ret_aq_blocking;
	logic [PA_WIDTH-2-1:0] ldu_mq_info_ret_PA_word;
	logic [3:0] ldu_mq_info_ret_byte_mask;
	logic [31:0] ldu_mq_info_ret_data;

    // misprediction notification to ROB
	logic mispred_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] mispred_notif_ROB_index;

    // misprediction notification backpressure from ROB
	logic mispred_notif_ready;

    // exception to ROB
	logic rob_exception_valid;
	logic [VA_WIDTH-1:0] rob_exception_VA;
	logic rob_exception_page_fault;
	logic rob_exception_access_fault;
	logic [LOG_ROB_ENTRIES-1:0] rob_exception_ROB_index;

    // exception backpressure from ROB
	logic rob_exception_ready;

    // restart from ROB
	logic rob_restart_valid;
	logic [8:0] rob_restart_ASID;
	logic [1:0] rob_restart_exec_mode;
	logic rob_restart_virtual_mode;
	logic rob_restart_MXR;
	logic rob_restart_SUM;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ldu_launch_pipeline #(
		.INIT_ASID(9'h0),
		.INIT_EXEC_MODE(M_MODE),
		.INIT_VIRTUAL_MODE(1'b0),
		.INIT_MXR(1'b0),
		.INIT_SUM(1'b0)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // first try
			first_try_valid <= '0;
			first_try_is_mq <= '0;
			first_try_misaligned <= '0;
			first_try_VPN <= '0;
			first_try_PO_word <= '0;
			first_try_byte_mask <= '0;
			first_try_cq_index <= '0;

		    // first try feedback
			last_first_try_ack <= '0;

		    // op enqueue to misaligned queue
			last_ldu_mq_enq_valid <= '0;

		    // misaligned queue enqueue feedback
			ldu_mq_enq_ready <= '0;
			ldu_mq_enq_index <= '0;

		    // ROB info
			rob_abs_head_index <= '0;

		    // acquire advertisement
			stamofu_aq_mem_aq_active <= '0;
			stamofu_aq_mem_aq_oldest_abs_ROB_index <= '0;
			stamofu_aq_io_aq_active <= '0;
			stamofu_aq_io_aq_oldest_abs_ROB_index <= '0;

		    // second try
			second_try_valid <= '0;
			second_try_is_mq <= '0;
			second_try_misaligned <= '0;
			second_try_page_fault <= '0;
			second_try_access_fault <= '0;
			second_try_is_mem <= '0;
			second_try_PPN <= '0;
			second_try_PO_word <= '0;
			second_try_byte_mask <= '0;
			second_try_cq_index <= '0;
			second_try_mq_index <= '0;

		    // second try feedback
			last_second_try_ack <= '0;

		    // data try
			data_try_valid <= '0;
			data_try_do_mispred <= '0;
			data_try_data <= '0;
			data_try_cq_index <= '0;

		    // data try feedback
			last_data_try_ack <= '0;

		    // dtlb req
			last_dtlb_req_valid <= '0;
			last_dtlb_req_exec_mode <= '0;
			last_dtlb_req_virtual_mode <= '0;
			last_dtlb_req_ASID <= '0;
			last_dtlb_req_MXR <= '0;
			last_dtlb_req_SUM <= '0;
			last_dtlb_req_VPN <= '0;

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

		    // dcache req feedback
			dcache_req_ready <= '0;

		    // dcache resp
			dcache_resp_valid_by_way <= '0;
			dcache_resp_tag_by_way <= '0;
			dcache_resp_data_by_way <= '0;

		    // dcache resp feedback
			last_dcache_resp_hit_valid <= '0;
			last_dcache_resp_hit_way <= '0;
			last_dcache_resp_miss_valid <= '0;
			last_dcache_resp_miss_tag <= '0;

		    // writeback data to PRF
			last_WB_valid <= '0;
			last_WB_data <= '0;
			last_WB_PR <= '0;
			last_WB_ROB_index <= '0;

		    // writeback backpressure from PRF
			WB_ready <= '0;

		    // CAM launch
			last_stamofu_CAM_launch_valid <= '0;
			last_stamofu_CAM_launch_PA_word <= '0;
			last_stamofu_CAM_launch_byte_mask <= '0;
			last_stamofu_CAM_launch_ROB_index <= '0;
			last_stamofu_CAM_launch_cq_index <= '0;
			last_stamofu_CAM_launch_is_mq <= '0;
			last_stamofu_CAM_launch_mq_index <= '0;

		    // central queue info grab
			last_ldu_cq_info_grab_cq_index <= '0;
			ldu_cq_info_grab_op <= '0;
			ldu_cq_info_grab_mdp_info <= '0;
			ldu_cq_info_grab_dest_PR <= '0;
			ldu_cq_info_grab_ROB_index <= '0;

		    // central queue info ret
			last_ldu_cq_info_ret_valid <= '0;
			last_ldu_cq_info_ret_cq_index <= '0;
			last_ldu_cq_info_ret_misaligned <= '0;
			last_ldu_cq_info_ret_dtlb_hit <= '0;
			last_ldu_cq_info_ret_page_fault <= '0;
			last_ldu_cq_info_ret_access_fault <= '0;
			last_ldu_cq_info_ret_dcache_hit <= '0;
			last_ldu_cq_info_ret_is_mem <= '0;
			last_ldu_cq_info_ret_aq_blocking <= '0;
			last_ldu_cq_info_ret_PA_word <= '0;
			last_ldu_cq_info_ret_byte_mask <= '0;
			last_ldu_cq_info_ret_data <= '0;

		    // misaligned queue info ret
			last_ldu_mq_info_ret_valid <= '0;
			last_ldu_mq_info_ret_mq_index <= '0;
			last_ldu_mq_info_ret_dtlb_hit <= '0;
			last_ldu_mq_info_ret_page_fault <= '0;
			last_ldu_mq_info_ret_access_fault <= '0;
			last_ldu_mq_info_ret_dcache_hit <= '0;
			last_ldu_mq_info_ret_is_mem <= '0;
			last_ldu_mq_info_ret_aq_blocking <= '0;
			last_ldu_mq_info_ret_PA_word <= '0;
			last_ldu_mq_info_ret_byte_mask <= '0;
			last_ldu_mq_info_ret_data <= '0;

		    // misprediction notification to ROB
			last_mispred_notif_valid <= '0;
			last_mispred_notif_ROB_index <= '0;

		    // misprediction notification backpressure from ROB
			mispred_notif_ready <= '0;

		    // exception to ROB
			last_rob_exception_valid <= '0;
			last_rob_exception_VA <= '0;
			last_rob_exception_page_fault <= '0;
			last_rob_exception_access_fault <= '0;
			last_rob_exception_ROB_index <= '0;

		    // exception backpressure from ROB
			rob_exception_ready <= '0;

		    // restart from ROB
			rob_restart_valid <= '0;
			rob_restart_ASID <= '0;
			rob_restart_exec_mode <= '0;
			rob_restart_virtual_mode <= '0;
			rob_restart_MXR <= '0;
			rob_restart_SUM <= '0;
        end
        else begin


		    // first try
			first_try_valid <= next_first_try_valid;
			first_try_is_mq <= next_first_try_is_mq;
			first_try_misaligned <= next_first_try_misaligned;
			first_try_VPN <= next_first_try_VPN;
			first_try_PO_word <= next_first_try_PO_word;
			first_try_byte_mask <= next_first_try_byte_mask;
			first_try_cq_index <= next_first_try_cq_index;

		    // first try feedback
			last_first_try_ack <= first_try_ack;

		    // op enqueue to misaligned queue
			last_ldu_mq_enq_valid <= ldu_mq_enq_valid;

		    // misaligned queue enqueue feedback
			ldu_mq_enq_ready <= next_ldu_mq_enq_ready;
			ldu_mq_enq_index <= next_ldu_mq_enq_index;

		    // ROB info
			rob_abs_head_index <= next_rob_abs_head_index;

		    // acquire advertisement
			stamofu_aq_mem_aq_active <= next_stamofu_aq_mem_aq_active;
			stamofu_aq_mem_aq_oldest_abs_ROB_index <= next_stamofu_aq_mem_aq_oldest_abs_ROB_index;
			stamofu_aq_io_aq_active <= next_stamofu_aq_io_aq_active;
			stamofu_aq_io_aq_oldest_abs_ROB_index <= next_stamofu_aq_io_aq_oldest_abs_ROB_index;

		    // second try
			second_try_valid <= next_second_try_valid;
			second_try_is_mq <= next_second_try_is_mq;
			second_try_misaligned <= next_second_try_misaligned;
			second_try_page_fault <= next_second_try_page_fault;
			second_try_access_fault <= next_second_try_access_fault;
			second_try_is_mem <= next_second_try_is_mem;
			second_try_PPN <= next_second_try_PPN;
			second_try_PO_word <= next_second_try_PO_word;
			second_try_byte_mask <= next_second_try_byte_mask;
			second_try_cq_index <= next_second_try_cq_index;
			second_try_mq_index <= next_second_try_mq_index;

		    // second try feedback
			last_second_try_ack <= second_try_ack;

		    // data try
			data_try_valid <= next_data_try_valid;
			data_try_do_mispred <= next_data_try_do_mispred;
			data_try_data <= next_data_try_data;
			data_try_cq_index <= next_data_try_cq_index;

		    // data try feedback
			last_data_try_ack <= data_try_ack;

		    // dtlb req
			last_dtlb_req_valid <= dtlb_req_valid;
			last_dtlb_req_exec_mode <= dtlb_req_exec_mode;
			last_dtlb_req_virtual_mode <= dtlb_req_virtual_mode;
			last_dtlb_req_ASID <= dtlb_req_ASID;
			last_dtlb_req_MXR <= dtlb_req_MXR;
			last_dtlb_req_SUM <= dtlb_req_SUM;
			last_dtlb_req_VPN <= dtlb_req_VPN;

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

		    // dcache req feedback
			dcache_req_ready <= next_dcache_req_ready;

		    // dcache resp
			dcache_resp_valid_by_way <= next_dcache_resp_valid_by_way;
			dcache_resp_tag_by_way <= next_dcache_resp_tag_by_way;
			dcache_resp_data_by_way <= next_dcache_resp_data_by_way;

		    // dcache resp feedback
			last_dcache_resp_hit_valid <= dcache_resp_hit_valid;
			last_dcache_resp_hit_way <= dcache_resp_hit_way;
			last_dcache_resp_miss_valid <= dcache_resp_miss_valid;
			last_dcache_resp_miss_tag <= dcache_resp_miss_tag;

		    // writeback data to PRF
			last_WB_valid <= WB_valid;
			last_WB_data <= WB_data;
			last_WB_PR <= WB_PR;
			last_WB_ROB_index <= WB_ROB_index;

		    // writeback backpressure from PRF
			WB_ready <= next_WB_ready;

		    // CAM launch
			last_stamofu_CAM_launch_valid <= stamofu_CAM_launch_valid;
			last_stamofu_CAM_launch_PA_word <= stamofu_CAM_launch_PA_word;
			last_stamofu_CAM_launch_byte_mask <= stamofu_CAM_launch_byte_mask;
			last_stamofu_CAM_launch_ROB_index <= stamofu_CAM_launch_ROB_index;
			last_stamofu_CAM_launch_cq_index <= stamofu_CAM_launch_cq_index;
			last_stamofu_CAM_launch_is_mq <= stamofu_CAM_launch_is_mq;
			last_stamofu_CAM_launch_mq_index <= stamofu_CAM_launch_mq_index;

		    // central queue info grab
			last_ldu_cq_info_grab_cq_index <= ldu_cq_info_grab_cq_index;
			ldu_cq_info_grab_op <= next_ldu_cq_info_grab_op;
			ldu_cq_info_grab_mdp_info <= next_ldu_cq_info_grab_mdp_info;
			ldu_cq_info_grab_dest_PR <= next_ldu_cq_info_grab_dest_PR;
			ldu_cq_info_grab_ROB_index <= next_ldu_cq_info_grab_ROB_index;

		    // central queue info ret
			last_ldu_cq_info_ret_valid <= ldu_cq_info_ret_valid;
			last_ldu_cq_info_ret_cq_index <= ldu_cq_info_ret_cq_index;
			last_ldu_cq_info_ret_misaligned <= ldu_cq_info_ret_misaligned;
			last_ldu_cq_info_ret_dtlb_hit <= ldu_cq_info_ret_dtlb_hit;
			last_ldu_cq_info_ret_page_fault <= ldu_cq_info_ret_page_fault;
			last_ldu_cq_info_ret_access_fault <= ldu_cq_info_ret_access_fault;
			last_ldu_cq_info_ret_dcache_hit <= ldu_cq_info_ret_dcache_hit;
			last_ldu_cq_info_ret_is_mem <= ldu_cq_info_ret_is_mem;
			last_ldu_cq_info_ret_aq_blocking <= ldu_cq_info_ret_aq_blocking;
			last_ldu_cq_info_ret_PA_word <= ldu_cq_info_ret_PA_word;
			last_ldu_cq_info_ret_byte_mask <= ldu_cq_info_ret_byte_mask;
			last_ldu_cq_info_ret_data <= ldu_cq_info_ret_data;

		    // misaligned queue info ret
			last_ldu_mq_info_ret_valid <= ldu_mq_info_ret_valid;
			last_ldu_mq_info_ret_mq_index <= ldu_mq_info_ret_mq_index;
			last_ldu_mq_info_ret_dtlb_hit <= ldu_mq_info_ret_dtlb_hit;
			last_ldu_mq_info_ret_page_fault <= ldu_mq_info_ret_page_fault;
			last_ldu_mq_info_ret_access_fault <= ldu_mq_info_ret_access_fault;
			last_ldu_mq_info_ret_dcache_hit <= ldu_mq_info_ret_dcache_hit;
			last_ldu_mq_info_ret_is_mem <= ldu_mq_info_ret_is_mem;
			last_ldu_mq_info_ret_aq_blocking <= ldu_mq_info_ret_aq_blocking;
			last_ldu_mq_info_ret_PA_word <= ldu_mq_info_ret_PA_word;
			last_ldu_mq_info_ret_byte_mask <= ldu_mq_info_ret_byte_mask;
			last_ldu_mq_info_ret_data <= ldu_mq_info_ret_data;

		    // misprediction notification to ROB
			last_mispred_notif_valid <= mispred_notif_valid;
			last_mispred_notif_ROB_index <= mispred_notif_ROB_index;

		    // misprediction notification backpressure from ROB
			mispred_notif_ready <= next_mispred_notif_ready;

		    // exception to ROB
			last_rob_exception_valid <= rob_exception_valid;
			last_rob_exception_VA <= rob_exception_VA;
			last_rob_exception_page_fault <= rob_exception_page_fault;
			last_rob_exception_access_fault <= rob_exception_access_fault;
			last_rob_exception_ROB_index <= rob_exception_ROB_index;

		    // exception backpressure from ROB
			rob_exception_ready <= next_rob_exception_ready;

		    // restart from ROB
			rob_restart_valid <= next_rob_restart_valid;
			rob_restart_ASID <= next_rob_restart_ASID;
			rob_restart_exec_mode <= next_rob_restart_exec_mode;
			rob_restart_virtual_mode <= next_rob_restart_virtual_mode;
			rob_restart_MXR <= next_rob_restart_MXR;
			rob_restart_SUM <= next_rob_restart_SUM;
        end
    end

endmodule