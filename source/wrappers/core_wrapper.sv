/*
    Filename: core_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around core module. 
    Spec: LOROF/spec/design/core.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter FETCH_UNIT_WAIT_FOR_RESTART_STATE = 1'b1;
parameter ROB_RESTART_ON_RESET = 1'b1;
parameter INIT_PC = 32'h00000000;
parameter INIT_ASID = 9'h000;
parameter INIT_EXEC_MODE = M_MODE;
parameter INIT_VIRTUAL_MODE = 1'b0;
parameter INIT_MXR = 1'b0;
parameter INIT_SUM = 1'b0;
parameter INIT_TRAP_SFENCE = 1'b0;
parameter INIT_TRAP_WFI = 1'b0;
parameter INIT_TRAP_SRET = 1'b0;
parameter INIT_TVEC_BASE_PC = 32'h0000F000;

module core_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // itlb req
	output logic last_itlb_req_valid,
	output logic [1:0] last_itlb_req_exec_mode,
	output logic last_itlb_req_virtual_mode,
	output logic [ASID_WIDTH-1:0] last_itlb_req_ASID,
	output logic [VPN_WIDTH-1:0] last_itlb_req_VPN,

    // itlb resp
	input logic next_itlb_resp_valid,
	input logic [PPN_WIDTH-1:0] next_itlb_resp_PPN,
	input logic next_itlb_resp_page_fault,
	input logic next_itlb_resp_access_fault,

    // icache req
	output logic last_icache_req_valid,
	output logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] last_icache_req_block_offset,
	output logic [ICACHE_INDEX_WIDTH-1:0] last_icache_req_index,

    // icache resp
	input logic [1:0] next_icache_resp_valid_by_way,
	input logic [1:0][ICACHE_TAG_WIDTH-1:0] next_icache_resp_tag_by_way,
	input logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0] next_icache_resp_instr_16B_by_way,

    // icache resp feedback
	output logic last_icache_resp_hit_valid,
	output logic last_icache_resp_hit_way,
	output logic last_icache_resp_miss_valid,
	output logic [ICACHE_TAG_WIDTH-1:0] last_icache_resp_miss_tag,

    // dtlb req
	output logic last_dtlb_req_bank0_valid,
	output logic [1:0] last_dtlb_req_bank0_exec_mode,
	output logic last_dtlb_req_bank0_virtual_mode,
	output logic [ASID_WIDTH-1:0] last_dtlb_req_bank0_ASID,
	output logic last_dtlb_req_bank0_MXR,
	output logic last_dtlb_req_bank0_SUM,
	output logic [VPN_WIDTH-1:0] last_dtlb_req_bank0_VPN,
	output logic last_dtlb_req_bank0_is_read,
	output logic last_dtlb_req_bank0_is_write,

	output logic last_dtlb_req_bank1_valid,
	output logic [1:0] last_dtlb_req_bank1_exec_mode,
	output logic last_dtlb_req_bank1_virtual_mode,
	output logic [ASID_WIDTH-1:0] last_dtlb_req_bank1_ASID,
	output logic last_dtlb_req_bank1_MXR,
	output logic last_dtlb_req_bank1_SUM,
	output logic [VPN_WIDTH-1:0] last_dtlb_req_bank1_VPN,
	output logic last_dtlb_req_bank1_is_read,
	output logic last_dtlb_req_bank1_is_write,

    // dtlb req feedback
	input logic next_dtlb_req_bank0_ready,

	input logic next_dtlb_req_bank1_ready,

    // dtlb resp
	input logic next_dtlb_resp_bank0_hit,
	input logic [PPN_WIDTH-1:0] next_dtlb_resp_bank0_PPN,
	input logic next_dtlb_resp_bank0_is_mem,
	input logic next_dtlb_resp_bank0_page_fault,
	input logic next_dtlb_resp_bank0_access_fault,

	input logic next_dtlb_resp_bank1_hit,
	input logic [PPN_WIDTH-1:0] next_dtlb_resp_bank1_PPN,
	input logic next_dtlb_resp_bank1_is_mem,
	input logic next_dtlb_resp_bank1_page_fault,
	input logic next_dtlb_resp_bank1_access_fault,

    // dtlb miss resp
	input logic next_dtlb_miss_resp_valid,
	input logic next_dtlb_miss_resp_is_ldu,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_dtlb_miss_resp_cq_index,
	input logic next_dtlb_miss_resp_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_dtlb_miss_resp_mq_index,
	input logic [PPN_WIDTH-1:0] next_dtlb_miss_resp_PPN,
	input logic next_dtlb_miss_resp_is_mem,
	input logic next_dtlb_miss_resp_page_fault,
	input logic next_dtlb_miss_resp_access_fault,

    // dcache req
	output logic last_dcache_req_bank0_valid,
	output logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] last_dcache_req_bank0_block_offset,
	output logic [DCACHE_INDEX_WIDTH-1:0] last_dcache_req_bank0_index,
	output logic last_dcache_req_bank0_is_ldu,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_dcache_req_bank0_cq_index,
	output logic last_dcache_req_bank0_is_mq,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_dcache_req_bank0_mq_index,

	output logic last_dcache_req_bank1_valid,
	output logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] last_dcache_req_bank1_block_offset,
	output logic [DCACHE_INDEX_WIDTH-1:0] last_dcache_req_bank1_index,
	output logic last_dcache_req_bank1_is_ldu,
	output logic [LOG_LDU_CQ_ENTRIES-1:0] last_dcache_req_bank1_cq_index,
	output logic last_dcache_req_bank1_is_mq,
	output logic [LOG_LDU_MQ_ENTRIES-1:0] last_dcache_req_bank1_mq_index,

    // dcache req feedback
	input logic next_dcache_req_bank0_ready,

	input logic next_dcache_req_bank1_ready,

    // dcache resp
	input logic [1:0] next_dcache_resp_bank0_valid_by_way,
	input logic [1:0] next_dcache_resp_bank0_exclusive_by_way,
	input logic [1:0][DCACHE_TAG_WIDTH-1:0] next_dcache_resp_bank0_tag_by_way,
	input logic [1:0][31:0] next_dcache_resp_bank0_data_by_way,

	input logic [1:0] next_dcache_resp_bank1_valid_by_way,
	input logic [1:0] next_dcache_resp_bank1_exclusive_by_way,
	input logic [1:0][DCACHE_TAG_WIDTH-1:0] next_dcache_resp_bank1_tag_by_way,
	input logic [1:0][31:0] next_dcache_resp_bank1_data_by_way,

    // dcache resp feedback
	output logic last_dcache_resp_bank0_hit_valid,
	output logic last_dcache_resp_bank0_hit_exclusive,
	output logic last_dcache_resp_bank0_hit_way,
	output logic last_dcache_resp_bank0_miss_valid,
	output logic last_dcache_resp_bank0_miss_prefetch,
	output logic last_dcache_resp_bank0_miss_exclusive,
	output logic [DCACHE_TAG_WIDTH-1:0] last_dcache_resp_bank0_miss_tag,

	output logic last_dcache_resp_bank1_hit_valid,
	output logic last_dcache_resp_bank1_hit_exclusive,
	output logic last_dcache_resp_bank1_hit_way,
	output logic last_dcache_resp_bank1_miss_valid,
	output logic last_dcache_resp_bank1_miss_prefetch,
	output logic last_dcache_resp_bank1_miss_exclusive,
	output logic [DCACHE_TAG_WIDTH-1:0] last_dcache_resp_bank1_miss_tag,

    // dcache miss resp
	input logic next_dcache_miss_resp_valid,
	input logic next_dcache_miss_resp_is_ldu,
	input logic [LOG_LDU_CQ_ENTRIES-1:0] next_dcache_miss_resp_cq_index,
	input logic next_dcache_miss_resp_is_mq,
	input logic [LOG_LDU_MQ_ENTRIES-1:0] next_dcache_miss_resp_mq_index,
	input logic [31:0] next_dcache_miss_resp_data,

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

    // write buffer WB data to PRF
	input logic next_wr_buf_WB_valid,
	input logic [31:0] next_wr_buf_WB_data,
	input logic [LOG_PR_COUNT-1:0] next_wr_buf_WB_PR,
        // don't need ROB_index as WB_send_complete = 1'b0

    // write buffer WB feedback from PRF
	output logic last_wr_buf_WB_ready,

    // sfence invalidation to MMU
	output logic last_sfence_inv_valid,
	output logic [VA_WIDTH-1:0] last_sfence_inv_VA,
	output logic [ASID_WIDTH-1:0] last_sfence_inv_ASID,

    // sfence invalidation backpressure from MMU
	input logic next_sfence_inv_ready,

    // hardware failure
	output logic last_unrecoverable_fault
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // itlb req
	logic itlb_req_valid;
	logic [1:0] itlb_req_exec_mode;
	logic itlb_req_virtual_mode;
	logic [ASID_WIDTH-1:0] itlb_req_ASID;
	logic [VPN_WIDTH-1:0] itlb_req_VPN;

    // itlb resp
	logic itlb_resp_valid;
	logic [PPN_WIDTH-1:0] itlb_resp_PPN;
	logic itlb_resp_page_fault;
	logic itlb_resp_access_fault;

    // icache req
	logic icache_req_valid;
	logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] icache_req_block_offset;
	logic [ICACHE_INDEX_WIDTH-1:0] icache_req_index;

    // icache resp
	logic [1:0] icache_resp_valid_by_way;
	logic [1:0][ICACHE_TAG_WIDTH-1:0] icache_resp_tag_by_way;
	logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0] icache_resp_instr_16B_by_way;

    // icache resp feedback
	logic icache_resp_hit_valid;
	logic icache_resp_hit_way;
	logic icache_resp_miss_valid;
	logic [ICACHE_TAG_WIDTH-1:0] icache_resp_miss_tag;

    // dtlb req
	logic dtlb_req_bank0_valid;
	logic [1:0] dtlb_req_bank0_exec_mode;
	logic dtlb_req_bank0_virtual_mode;
	logic [ASID_WIDTH-1:0] dtlb_req_bank0_ASID;
	logic dtlb_req_bank0_MXR;
	logic dtlb_req_bank0_SUM;
	logic [VPN_WIDTH-1:0] dtlb_req_bank0_VPN;
	logic dtlb_req_bank0_is_read;
	logic dtlb_req_bank0_is_write;

	logic dtlb_req_bank1_valid;
	logic [1:0] dtlb_req_bank1_exec_mode;
	logic dtlb_req_bank1_virtual_mode;
	logic [ASID_WIDTH-1:0] dtlb_req_bank1_ASID;
	logic dtlb_req_bank1_MXR;
	logic dtlb_req_bank1_SUM;
	logic [VPN_WIDTH-1:0] dtlb_req_bank1_VPN;
	logic dtlb_req_bank1_is_read;
	logic dtlb_req_bank1_is_write;

    // dtlb req feedback
	logic dtlb_req_bank0_ready;

	logic dtlb_req_bank1_ready;

    // dtlb resp
	logic dtlb_resp_bank0_hit;
	logic [PPN_WIDTH-1:0] dtlb_resp_bank0_PPN;
	logic dtlb_resp_bank0_is_mem;
	logic dtlb_resp_bank0_page_fault;
	logic dtlb_resp_bank0_access_fault;

	logic dtlb_resp_bank1_hit;
	logic [PPN_WIDTH-1:0] dtlb_resp_bank1_PPN;
	logic dtlb_resp_bank1_is_mem;
	logic dtlb_resp_bank1_page_fault;
	logic dtlb_resp_bank1_access_fault;

    // dtlb miss resp
	logic dtlb_miss_resp_valid;
	logic dtlb_miss_resp_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dtlb_miss_resp_cq_index;
	logic dtlb_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dtlb_miss_resp_mq_index;
	logic [PPN_WIDTH-1:0] dtlb_miss_resp_PPN;
	logic dtlb_miss_resp_is_mem;
	logic dtlb_miss_resp_page_fault;
	logic dtlb_miss_resp_access_fault;

    // dcache req
	logic dcache_req_bank0_valid;
	logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] dcache_req_bank0_block_offset;
	logic [DCACHE_INDEX_WIDTH-1:0] dcache_req_bank0_index;
	logic dcache_req_bank0_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dcache_req_bank0_cq_index;
	logic dcache_req_bank0_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dcache_req_bank0_mq_index;

	logic dcache_req_bank1_valid;
	logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] dcache_req_bank1_block_offset;
	logic [DCACHE_INDEX_WIDTH-1:0] dcache_req_bank1_index;
	logic dcache_req_bank1_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dcache_req_bank1_cq_index;
	logic dcache_req_bank1_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dcache_req_bank1_mq_index;

    // dcache req feedback
	logic dcache_req_bank0_ready;

	logic dcache_req_bank1_ready;

    // dcache resp
	logic [1:0] dcache_resp_bank0_valid_by_way;
	logic [1:0] dcache_resp_bank0_exclusive_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] dcache_resp_bank0_tag_by_way;
	logic [1:0][31:0] dcache_resp_bank0_data_by_way;

	logic [1:0] dcache_resp_bank1_valid_by_way;
	logic [1:0] dcache_resp_bank1_exclusive_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] dcache_resp_bank1_tag_by_way;
	logic [1:0][31:0] dcache_resp_bank1_data_by_way;

    // dcache resp feedback
	logic dcache_resp_bank0_hit_valid;
	logic dcache_resp_bank0_hit_exclusive;
	logic dcache_resp_bank0_hit_way;
	logic dcache_resp_bank0_miss_valid;
	logic dcache_resp_bank0_miss_prefetch;
	logic dcache_resp_bank0_miss_exclusive;
	logic [DCACHE_TAG_WIDTH-1:0] dcache_resp_bank0_miss_tag;

	logic dcache_resp_bank1_hit_valid;
	logic dcache_resp_bank1_hit_exclusive;
	logic dcache_resp_bank1_hit_way;
	logic dcache_resp_bank1_miss_valid;
	logic dcache_resp_bank1_miss_prefetch;
	logic dcache_resp_bank1_miss_exclusive;
	logic [DCACHE_TAG_WIDTH-1:0] dcache_resp_bank1_miss_tag;

    // dcache miss resp
	logic dcache_miss_resp_valid;
	logic dcache_miss_resp_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] dcache_miss_resp_cq_index;
	logic dcache_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] dcache_miss_resp_mq_index;
	logic [31:0] dcache_miss_resp_data;

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

    // write buffer WB data to PRF
	logic wr_buf_WB_valid;
	logic [31:0] wr_buf_WB_data;
	logic [LOG_PR_COUNT-1:0] wr_buf_WB_PR;
        // don't need ROB_index as WB_send_complete = 1'b0

    // write buffer WB feedback from PRF
	logic wr_buf_WB_ready;

    // sfence invalidation to MMU
	logic sfence_inv_valid;
	logic [VA_WIDTH-1:0] sfence_inv_VA;
	logic [ASID_WIDTH-1:0] sfence_inv_ASID;

    // sfence invalidation backpressure from MMU
	logic sfence_inv_ready;

    // hardware failure
	logic unrecoverable_fault;

    // ----------------------------------------------------------------
    // Module Instantiation:

	core #(
		.FETCH_UNIT_WAIT_FOR_RESTART_STATE(FETCH_UNIT_WAIT_FOR_RESTART_STATE),
		.ROB_RESTART_ON_RESET(ROB_RESTART_ON_RESET),
		.INIT_PC(INIT_PC),
		.INIT_ASID(INIT_ASID),
		.INIT_EXEC_MODE(INIT_EXEC_MODE),
		.INIT_VIRTUAL_MODE(INIT_VIRTUAL_MODE),
		.INIT_MXR(INIT_MXR),
		.INIT_SUM(INIT_SUM),
		.INIT_TRAP_SFENCE(INIT_TRAP_SFENCE),
		.INIT_TRAP_WFI(INIT_TRAP_WFI),
		.INIT_TRAP_SRET(INIT_TRAP_SRET),
		.INIT_TVEC_BASE_PC(INIT_TVEC_BASE_PC)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // itlb req
			last_itlb_req_valid <= '0;
			last_itlb_req_exec_mode <= '0;
			last_itlb_req_virtual_mode <= '0;
			last_itlb_req_ASID <= '0;
			last_itlb_req_VPN <= '0;

		    // itlb resp
			itlb_resp_valid <= '0;
			itlb_resp_PPN <= '0;
			itlb_resp_page_fault <= '0;
			itlb_resp_access_fault <= '0;

		    // icache req
			last_icache_req_valid <= '0;
			last_icache_req_block_offset <= '0;
			last_icache_req_index <= '0;

		    // icache resp
			icache_resp_valid_by_way <= '0;
			icache_resp_tag_by_way <= '0;
			icache_resp_instr_16B_by_way <= '0;

		    // icache resp feedback
			last_icache_resp_hit_valid <= '0;
			last_icache_resp_hit_way <= '0;
			last_icache_resp_miss_valid <= '0;
			last_icache_resp_miss_tag <= '0;

		    // dtlb req
			last_dtlb_req_bank0_valid <= '0;
			last_dtlb_req_bank0_exec_mode <= '0;
			last_dtlb_req_bank0_virtual_mode <= '0;
			last_dtlb_req_bank0_ASID <= '0;
			last_dtlb_req_bank0_MXR <= '0;
			last_dtlb_req_bank0_SUM <= '0;
			last_dtlb_req_bank0_VPN <= '0;
			last_dtlb_req_bank0_is_read <= '0;
			last_dtlb_req_bank0_is_write <= '0;

			last_dtlb_req_bank1_valid <= '0;
			last_dtlb_req_bank1_exec_mode <= '0;
			last_dtlb_req_bank1_virtual_mode <= '0;
			last_dtlb_req_bank1_ASID <= '0;
			last_dtlb_req_bank1_MXR <= '0;
			last_dtlb_req_bank1_SUM <= '0;
			last_dtlb_req_bank1_VPN <= '0;
			last_dtlb_req_bank1_is_read <= '0;
			last_dtlb_req_bank1_is_write <= '0;

		    // dtlb req feedback
			dtlb_req_bank0_ready <= '0;

			dtlb_req_bank1_ready <= '0;

		    // dtlb resp
			dtlb_resp_bank0_hit <= '0;
			dtlb_resp_bank0_PPN <= '0;
			dtlb_resp_bank0_is_mem <= '0;
			dtlb_resp_bank0_page_fault <= '0;
			dtlb_resp_bank0_access_fault <= '0;

			dtlb_resp_bank1_hit <= '0;
			dtlb_resp_bank1_PPN <= '0;
			dtlb_resp_bank1_is_mem <= '0;
			dtlb_resp_bank1_page_fault <= '0;
			dtlb_resp_bank1_access_fault <= '0;

		    // dtlb miss resp
			dtlb_miss_resp_valid <= '0;
			dtlb_miss_resp_is_ldu <= '0;
			dtlb_miss_resp_cq_index <= '0;
			dtlb_miss_resp_is_mq <= '0;
			dtlb_miss_resp_mq_index <= '0;
			dtlb_miss_resp_PPN <= '0;
			dtlb_miss_resp_is_mem <= '0;
			dtlb_miss_resp_page_fault <= '0;
			dtlb_miss_resp_access_fault <= '0;

		    // dcache req
			last_dcache_req_bank0_valid <= '0;
			last_dcache_req_bank0_block_offset <= '0;
			last_dcache_req_bank0_index <= '0;
			last_dcache_req_bank0_is_ldu <= '0;
			last_dcache_req_bank0_cq_index <= '0;
			last_dcache_req_bank0_is_mq <= '0;
			last_dcache_req_bank0_mq_index <= '0;

			last_dcache_req_bank1_valid <= '0;
			last_dcache_req_bank1_block_offset <= '0;
			last_dcache_req_bank1_index <= '0;
			last_dcache_req_bank1_is_ldu <= '0;
			last_dcache_req_bank1_cq_index <= '0;
			last_dcache_req_bank1_is_mq <= '0;
			last_dcache_req_bank1_mq_index <= '0;

		    // dcache req feedback
			dcache_req_bank0_ready <= '0;

			dcache_req_bank1_ready <= '0;

		    // dcache resp
			dcache_resp_bank0_valid_by_way <= '0;
			dcache_resp_bank0_exclusive_by_way <= '0;
			dcache_resp_bank0_tag_by_way <= '0;
			dcache_resp_bank0_data_by_way <= '0;

			dcache_resp_bank1_valid_by_way <= '0;
			dcache_resp_bank1_exclusive_by_way <= '0;
			dcache_resp_bank1_tag_by_way <= '0;
			dcache_resp_bank1_data_by_way <= '0;

		    // dcache resp feedback
			last_dcache_resp_bank0_hit_valid <= '0;
			last_dcache_resp_bank0_hit_exclusive <= '0;
			last_dcache_resp_bank0_hit_way <= '0;
			last_dcache_resp_bank0_miss_valid <= '0;
			last_dcache_resp_bank0_miss_prefetch <= '0;
			last_dcache_resp_bank0_miss_exclusive <= '0;
			last_dcache_resp_bank0_miss_tag <= '0;

			last_dcache_resp_bank1_hit_valid <= '0;
			last_dcache_resp_bank1_hit_exclusive <= '0;
			last_dcache_resp_bank1_hit_way <= '0;
			last_dcache_resp_bank1_miss_valid <= '0;
			last_dcache_resp_bank1_miss_prefetch <= '0;
			last_dcache_resp_bank1_miss_exclusive <= '0;
			last_dcache_resp_bank1_miss_tag <= '0;

		    // dcache miss resp
			dcache_miss_resp_valid <= '0;
			dcache_miss_resp_is_ldu <= '0;
			dcache_miss_resp_cq_index <= '0;
			dcache_miss_resp_is_mq <= '0;
			dcache_miss_resp_mq_index <= '0;
			dcache_miss_resp_data <= '0;

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

		    // write buffer WB data to PRF
			wr_buf_WB_valid <= '0;
			wr_buf_WB_data <= '0;
			wr_buf_WB_PR <= '0;
		        // don't need ROB_index as WB_send_complete = 1'b0

		    // write buffer WB feedback from PRF
			last_wr_buf_WB_ready <= '0;

		    // sfence invalidation to MMU
			last_sfence_inv_valid <= '0;
			last_sfence_inv_VA <= '0;
			last_sfence_inv_ASID <= '0;

		    // sfence invalidation backpressure from MMU
			sfence_inv_ready <= '0;

		    // hardware failure
			last_unrecoverable_fault <= '0;
        end
        else begin

		    // itlb req
			last_itlb_req_valid <= itlb_req_valid;
			last_itlb_req_exec_mode <= itlb_req_exec_mode;
			last_itlb_req_virtual_mode <= itlb_req_virtual_mode;
			last_itlb_req_ASID <= itlb_req_ASID;
			last_itlb_req_VPN <= itlb_req_VPN;

		    // itlb resp
			itlb_resp_valid <= next_itlb_resp_valid;
			itlb_resp_PPN <= next_itlb_resp_PPN;
			itlb_resp_page_fault <= next_itlb_resp_page_fault;
			itlb_resp_access_fault <= next_itlb_resp_access_fault;

		    // icache req
			last_icache_req_valid <= icache_req_valid;
			last_icache_req_block_offset <= icache_req_block_offset;
			last_icache_req_index <= icache_req_index;

		    // icache resp
			icache_resp_valid_by_way <= next_icache_resp_valid_by_way;
			icache_resp_tag_by_way <= next_icache_resp_tag_by_way;
			icache_resp_instr_16B_by_way <= next_icache_resp_instr_16B_by_way;

		    // icache resp feedback
			last_icache_resp_hit_valid <= icache_resp_hit_valid;
			last_icache_resp_hit_way <= icache_resp_hit_way;
			last_icache_resp_miss_valid <= icache_resp_miss_valid;
			last_icache_resp_miss_tag <= icache_resp_miss_tag;

		    // dtlb req
			last_dtlb_req_bank0_valid <= dtlb_req_bank0_valid;
			last_dtlb_req_bank0_exec_mode <= dtlb_req_bank0_exec_mode;
			last_dtlb_req_bank0_virtual_mode <= dtlb_req_bank0_virtual_mode;
			last_dtlb_req_bank0_ASID <= dtlb_req_bank0_ASID;
			last_dtlb_req_bank0_MXR <= dtlb_req_bank0_MXR;
			last_dtlb_req_bank0_SUM <= dtlb_req_bank0_SUM;
			last_dtlb_req_bank0_VPN <= dtlb_req_bank0_VPN;
			last_dtlb_req_bank0_is_read <= dtlb_req_bank0_is_read;
			last_dtlb_req_bank0_is_write <= dtlb_req_bank0_is_write;

			last_dtlb_req_bank1_valid <= dtlb_req_bank1_valid;
			last_dtlb_req_bank1_exec_mode <= dtlb_req_bank1_exec_mode;
			last_dtlb_req_bank1_virtual_mode <= dtlb_req_bank1_virtual_mode;
			last_dtlb_req_bank1_ASID <= dtlb_req_bank1_ASID;
			last_dtlb_req_bank1_MXR <= dtlb_req_bank1_MXR;
			last_dtlb_req_bank1_SUM <= dtlb_req_bank1_SUM;
			last_dtlb_req_bank1_VPN <= dtlb_req_bank1_VPN;
			last_dtlb_req_bank1_is_read <= dtlb_req_bank1_is_read;
			last_dtlb_req_bank1_is_write <= dtlb_req_bank1_is_write;

		    // dtlb req feedback
			dtlb_req_bank0_ready <= next_dtlb_req_bank0_ready;

			dtlb_req_bank1_ready <= next_dtlb_req_bank1_ready;

		    // dtlb resp
			dtlb_resp_bank0_hit <= next_dtlb_resp_bank0_hit;
			dtlb_resp_bank0_PPN <= next_dtlb_resp_bank0_PPN;
			dtlb_resp_bank0_is_mem <= next_dtlb_resp_bank0_is_mem;
			dtlb_resp_bank0_page_fault <= next_dtlb_resp_bank0_page_fault;
			dtlb_resp_bank0_access_fault <= next_dtlb_resp_bank0_access_fault;

			dtlb_resp_bank1_hit <= next_dtlb_resp_bank1_hit;
			dtlb_resp_bank1_PPN <= next_dtlb_resp_bank1_PPN;
			dtlb_resp_bank1_is_mem <= next_dtlb_resp_bank1_is_mem;
			dtlb_resp_bank1_page_fault <= next_dtlb_resp_bank1_page_fault;
			dtlb_resp_bank1_access_fault <= next_dtlb_resp_bank1_access_fault;

		    // dtlb miss resp
			dtlb_miss_resp_valid <= next_dtlb_miss_resp_valid;
			dtlb_miss_resp_is_ldu <= next_dtlb_miss_resp_is_ldu;
			dtlb_miss_resp_cq_index <= next_dtlb_miss_resp_cq_index;
			dtlb_miss_resp_is_mq <= next_dtlb_miss_resp_is_mq;
			dtlb_miss_resp_mq_index <= next_dtlb_miss_resp_mq_index;
			dtlb_miss_resp_PPN <= next_dtlb_miss_resp_PPN;
			dtlb_miss_resp_is_mem <= next_dtlb_miss_resp_is_mem;
			dtlb_miss_resp_page_fault <= next_dtlb_miss_resp_page_fault;
			dtlb_miss_resp_access_fault <= next_dtlb_miss_resp_access_fault;

		    // dcache req
			last_dcache_req_bank0_valid <= dcache_req_bank0_valid;
			last_dcache_req_bank0_block_offset <= dcache_req_bank0_block_offset;
			last_dcache_req_bank0_index <= dcache_req_bank0_index;
			last_dcache_req_bank0_is_ldu <= dcache_req_bank0_is_ldu;
			last_dcache_req_bank0_cq_index <= dcache_req_bank0_cq_index;
			last_dcache_req_bank0_is_mq <= dcache_req_bank0_is_mq;
			last_dcache_req_bank0_mq_index <= dcache_req_bank0_mq_index;

			last_dcache_req_bank1_valid <= dcache_req_bank1_valid;
			last_dcache_req_bank1_block_offset <= dcache_req_bank1_block_offset;
			last_dcache_req_bank1_index <= dcache_req_bank1_index;
			last_dcache_req_bank1_is_ldu <= dcache_req_bank1_is_ldu;
			last_dcache_req_bank1_cq_index <= dcache_req_bank1_cq_index;
			last_dcache_req_bank1_is_mq <= dcache_req_bank1_is_mq;
			last_dcache_req_bank1_mq_index <= dcache_req_bank1_mq_index;

		    // dcache req feedback
			dcache_req_bank0_ready <= next_dcache_req_bank0_ready;

			dcache_req_bank1_ready <= next_dcache_req_bank1_ready;

		    // dcache resp
			dcache_resp_bank0_valid_by_way <= next_dcache_resp_bank0_valid_by_way;
			dcache_resp_bank0_exclusive_by_way <= next_dcache_resp_bank0_exclusive_by_way;
			dcache_resp_bank0_tag_by_way <= next_dcache_resp_bank0_tag_by_way;
			dcache_resp_bank0_data_by_way <= next_dcache_resp_bank0_data_by_way;

			dcache_resp_bank1_valid_by_way <= next_dcache_resp_bank1_valid_by_way;
			dcache_resp_bank1_exclusive_by_way <= next_dcache_resp_bank1_exclusive_by_way;
			dcache_resp_bank1_tag_by_way <= next_dcache_resp_bank1_tag_by_way;
			dcache_resp_bank1_data_by_way <= next_dcache_resp_bank1_data_by_way;

		    // dcache resp feedback
			last_dcache_resp_bank0_hit_valid <= dcache_resp_bank0_hit_valid;
			last_dcache_resp_bank0_hit_exclusive <= dcache_resp_bank0_hit_exclusive;
			last_dcache_resp_bank0_hit_way <= dcache_resp_bank0_hit_way;
			last_dcache_resp_bank0_miss_valid <= dcache_resp_bank0_miss_valid;
			last_dcache_resp_bank0_miss_prefetch <= dcache_resp_bank0_miss_prefetch;
			last_dcache_resp_bank0_miss_exclusive <= dcache_resp_bank0_miss_exclusive;
			last_dcache_resp_bank0_miss_tag <= dcache_resp_bank0_miss_tag;

			last_dcache_resp_bank1_hit_valid <= dcache_resp_bank1_hit_valid;
			last_dcache_resp_bank1_hit_exclusive <= dcache_resp_bank1_hit_exclusive;
			last_dcache_resp_bank1_hit_way <= dcache_resp_bank1_hit_way;
			last_dcache_resp_bank1_miss_valid <= dcache_resp_bank1_miss_valid;
			last_dcache_resp_bank1_miss_prefetch <= dcache_resp_bank1_miss_prefetch;
			last_dcache_resp_bank1_miss_exclusive <= dcache_resp_bank1_miss_exclusive;
			last_dcache_resp_bank1_miss_tag <= dcache_resp_bank1_miss_tag;

		    // dcache miss resp
			dcache_miss_resp_valid <= next_dcache_miss_resp_valid;
			dcache_miss_resp_is_ldu <= next_dcache_miss_resp_is_ldu;
			dcache_miss_resp_cq_index <= next_dcache_miss_resp_cq_index;
			dcache_miss_resp_is_mq <= next_dcache_miss_resp_is_mq;
			dcache_miss_resp_mq_index <= next_dcache_miss_resp_mq_index;
			dcache_miss_resp_data <= next_dcache_miss_resp_data;

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

		    // write buffer WB data to PRF
			wr_buf_WB_valid <= next_wr_buf_WB_valid;
			wr_buf_WB_data <= next_wr_buf_WB_data;
			wr_buf_WB_PR <= next_wr_buf_WB_PR;
		        // don't need ROB_index as WB_send_complete = 1'b0

		    // write buffer WB feedback from PRF
			last_wr_buf_WB_ready <= wr_buf_WB_ready;

		    // sfence invalidation to MMU
			last_sfence_inv_valid <= sfence_inv_valid;
			last_sfence_inv_VA <= sfence_inv_VA;
			last_sfence_inv_ASID <= sfence_inv_ASID;

		    // sfence invalidation backpressure from MMU
			sfence_inv_ready <= next_sfence_inv_ready;

		    // hardware failure
			last_unrecoverable_fault <= unrecoverable_fault;
        end
    end

endmodule