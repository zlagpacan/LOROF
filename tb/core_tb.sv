/*
    Filename: core_tb.sv
    Author: zlagpacan
    Description: Testbench for core module. 
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
parameter INIT_TVEC_BASE_PC = 32'h80000000;

module core_tb ();

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

    // itlb req
	logic DUT_itlb_req_valid, expected_itlb_req_valid;
	logic [1:0] DUT_itlb_req_exec_mode, expected_itlb_req_exec_mode;
	logic DUT_itlb_req_virtual_mode, expected_itlb_req_virtual_mode;
	logic [ASID_WIDTH-1:0] DUT_itlb_req_ASID, expected_itlb_req_ASID;
	logic [VPN_WIDTH-1:0] DUT_itlb_req_VPN, expected_itlb_req_VPN;

    // itlb resp
	logic tb_itlb_resp_valid;
	logic [PPN_WIDTH-1:0] tb_itlb_resp_PPN;
	logic tb_itlb_resp_page_fault;
	logic tb_itlb_resp_access_fault;

    // icache req
	logic DUT_icache_req_valid, expected_icache_req_valid;
	logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] DUT_icache_req_block_offset, expected_icache_req_block_offset;
	logic [ICACHE_INDEX_WIDTH-1:0] DUT_icache_req_index, expected_icache_req_index;

    // icache resp
	logic [1:0] tb_icache_resp_valid_by_way;
	logic [1:0][ICACHE_TAG_WIDTH-1:0] tb_icache_resp_tag_by_way;
	logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0] tb_icache_resp_instr_16B_by_way;

    // icache resp feedback
	logic DUT_icache_resp_hit_valid, expected_icache_resp_hit_valid;
	logic DUT_icache_resp_hit_way, expected_icache_resp_hit_way;
	logic DUT_icache_resp_miss_valid, expected_icache_resp_miss_valid;
	logic [ICACHE_TAG_WIDTH-1:0] DUT_icache_resp_miss_tag, expected_icache_resp_miss_tag;

    // dtlb req
	logic DUT_dtlb_req_bank0_valid, expected_dtlb_req_bank0_valid;
	logic [1:0] DUT_dtlb_req_bank0_exec_mode, expected_dtlb_req_bank0_exec_mode;
	logic DUT_dtlb_req_bank0_virtual_mode, expected_dtlb_req_bank0_virtual_mode;
	logic [ASID_WIDTH-1:0] DUT_dtlb_req_bank0_ASID, expected_dtlb_req_bank0_ASID;
	logic DUT_dtlb_req_bank0_MXR, expected_dtlb_req_bank0_MXR;
	logic DUT_dtlb_req_bank0_SUM, expected_dtlb_req_bank0_SUM;
	logic [VPN_WIDTH-1:0] DUT_dtlb_req_bank0_VPN, expected_dtlb_req_bank0_VPN;
	logic DUT_dtlb_req_bank0_is_read, expected_dtlb_req_bank0_is_read;
	logic DUT_dtlb_req_bank0_is_write, expected_dtlb_req_bank0_is_write;

	logic DUT_dtlb_req_bank1_valid, expected_dtlb_req_bank1_valid;
	logic [1:0] DUT_dtlb_req_bank1_exec_mode, expected_dtlb_req_bank1_exec_mode;
	logic DUT_dtlb_req_bank1_virtual_mode, expected_dtlb_req_bank1_virtual_mode;
	logic [ASID_WIDTH-1:0] DUT_dtlb_req_bank1_ASID, expected_dtlb_req_bank1_ASID;
	logic DUT_dtlb_req_bank1_MXR, expected_dtlb_req_bank1_MXR;
	logic DUT_dtlb_req_bank1_SUM, expected_dtlb_req_bank1_SUM;
	logic [VPN_WIDTH-1:0] DUT_dtlb_req_bank1_VPN, expected_dtlb_req_bank1_VPN;
	logic DUT_dtlb_req_bank1_is_read, expected_dtlb_req_bank1_is_read;
	logic DUT_dtlb_req_bank1_is_write, expected_dtlb_req_bank1_is_write;

    // dtlb req feedback
	logic tb_dtlb_req_bank0_ready;

	logic tb_dtlb_req_bank1_ready;

    // dtlb resp
	logic tb_dtlb_resp_bank0_hit;
	logic [PPN_WIDTH-1:0] tb_dtlb_resp_bank0_PPN;
	logic tb_dtlb_resp_bank0_is_mem;
	logic tb_dtlb_resp_bank0_page_fault;
	logic tb_dtlb_resp_bank0_access_fault;

	logic tb_dtlb_resp_bank1_hit;
	logic [PPN_WIDTH-1:0] tb_dtlb_resp_bank1_PPN;
	logic tb_dtlb_resp_bank1_is_mem;
	logic tb_dtlb_resp_bank1_page_fault;
	logic tb_dtlb_resp_bank1_access_fault;

    // dtlb miss resp
	logic tb_dtlb_miss_resp_valid;
	logic tb_dtlb_miss_resp_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_dtlb_miss_resp_cq_index;
	logic tb_dtlb_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_dtlb_miss_resp_mq_index;
	logic [PPN_WIDTH-1:0] tb_dtlb_miss_resp_PPN;
	logic tb_dtlb_miss_resp_is_mem;
	logic tb_dtlb_miss_resp_page_fault;
	logic tb_dtlb_miss_resp_access_fault;

    // dcache req
	logic DUT_dcache_req_bank0_valid, expected_dcache_req_bank0_valid;
	logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] DUT_dcache_req_bank0_block_offset, expected_dcache_req_bank0_block_offset;
	logic [DCACHE_INDEX_WIDTH-1:0] DUT_dcache_req_bank0_index, expected_dcache_req_bank0_index;
	logic DUT_dcache_req_bank0_is_ldu, expected_dcache_req_bank0_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_dcache_req_bank0_cq_index, expected_dcache_req_bank0_cq_index;
	logic DUT_dcache_req_bank0_is_mq, expected_dcache_req_bank0_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_dcache_req_bank0_mq_index, expected_dcache_req_bank0_mq_index;

	logic DUT_dcache_req_bank1_valid, expected_dcache_req_bank1_valid;
	logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0] DUT_dcache_req_bank1_block_offset, expected_dcache_req_bank1_block_offset;
	logic [DCACHE_INDEX_WIDTH-1:0] DUT_dcache_req_bank1_index, expected_dcache_req_bank1_index;
	logic DUT_dcache_req_bank1_is_ldu, expected_dcache_req_bank1_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_dcache_req_bank1_cq_index, expected_dcache_req_bank1_cq_index;
	logic DUT_dcache_req_bank1_is_mq, expected_dcache_req_bank1_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] DUT_dcache_req_bank1_mq_index, expected_dcache_req_bank1_mq_index;

    // dcache req feedback
	logic tb_dcache_req_bank0_ready;

	logic tb_dcache_req_bank1_ready;

    // dcache resp
	logic [1:0] tb_dcache_resp_bank0_valid_by_way;
	logic [1:0] tb_dcache_resp_bank0_exclusive_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] tb_dcache_resp_bank0_tag_by_way;
	logic [1:0][31:0] tb_dcache_resp_bank0_data_by_way;

	logic [1:0] tb_dcache_resp_bank1_valid_by_way;
	logic [1:0] tb_dcache_resp_bank1_exclusive_by_way;
	logic [1:0][DCACHE_TAG_WIDTH-1:0] tb_dcache_resp_bank1_tag_by_way;
	logic [1:0][31:0] tb_dcache_resp_bank1_data_by_way;

    // dcache resp feedback
	logic DUT_dcache_resp_bank0_hit_valid, expected_dcache_resp_bank0_hit_valid;
	logic DUT_dcache_resp_bank0_hit_exclusive, expected_dcache_resp_bank0_hit_exclusive;
	logic DUT_dcache_resp_bank0_hit_way, expected_dcache_resp_bank0_hit_way;
	logic DUT_dcache_resp_bank0_miss_valid, expected_dcache_resp_bank0_miss_valid;
	logic DUT_dcache_resp_bank0_miss_prefetch, expected_dcache_resp_bank0_miss_prefetch;
	logic DUT_dcache_resp_bank0_miss_exclusive, expected_dcache_resp_bank0_miss_exclusive;
	logic [DCACHE_TAG_WIDTH-1:0] DUT_dcache_resp_bank0_miss_tag, expected_dcache_resp_bank0_miss_tag;

	logic DUT_dcache_resp_bank1_hit_valid, expected_dcache_resp_bank1_hit_valid;
	logic DUT_dcache_resp_bank1_hit_exclusive, expected_dcache_resp_bank1_hit_exclusive;
	logic DUT_dcache_resp_bank1_hit_way, expected_dcache_resp_bank1_hit_way;
	logic DUT_dcache_resp_bank1_miss_valid, expected_dcache_resp_bank1_miss_valid;
	logic DUT_dcache_resp_bank1_miss_prefetch, expected_dcache_resp_bank1_miss_prefetch;
	logic DUT_dcache_resp_bank1_miss_exclusive, expected_dcache_resp_bank1_miss_exclusive;
	logic [DCACHE_TAG_WIDTH-1:0] DUT_dcache_resp_bank1_miss_tag, expected_dcache_resp_bank1_miss_tag;

    // dcache miss resp
	logic tb_dcache_miss_resp_valid;
	logic tb_dcache_miss_resp_is_ldu;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_dcache_miss_resp_cq_index;
	logic tb_dcache_miss_resp_is_mq;
	logic [LOG_LDU_MQ_ENTRIES-1:0] tb_dcache_miss_resp_mq_index;
	logic [31:0] tb_dcache_miss_resp_data;

    // write buffer enq bank 0
	logic DUT_wr_buf_enq_bank0_valid, expected_wr_buf_enq_bank0_valid;
	logic DUT_wr_buf_enq_bank0_is_amo, expected_wr_buf_enq_bank0_is_amo;
	logic [3:0] DUT_wr_buf_enq_bank0_op, expected_wr_buf_enq_bank0_op;
	logic [LOG_PR_COUNT-1:0] DUT_wr_buf_enq_bank0_dest_PR, expected_wr_buf_enq_bank0_dest_PR;
	logic DUT_wr_buf_enq_bank0_is_mem, expected_wr_buf_enq_bank0_is_mem;
	logic [PA_WIDTH-2-1:0] DUT_wr_buf_enq_bank0_PA_word, expected_wr_buf_enq_bank0_PA_word;
	logic [3:0] DUT_wr_buf_enq_bank0_byte_mask, expected_wr_buf_enq_bank0_byte_mask;
	logic [31:0] DUT_wr_buf_enq_bank0_data, expected_wr_buf_enq_bank0_data;

    // write buffer enq feedback bank 0
	logic tb_wr_buf_enq_bank0_ready;
	logic tb_wr_buf_enq_bank0_mem_present;
	logic tb_wr_buf_enq_bank0_io_present;

    // write buffer enq bank 1
	logic DUT_wr_buf_enq_bank1_valid, expected_wr_buf_enq_bank1_valid;
	logic DUT_wr_buf_enq_bank1_is_amo, expected_wr_buf_enq_bank1_is_amo;
	logic [3:0] DUT_wr_buf_enq_bank1_op, expected_wr_buf_enq_bank1_op;
	logic [LOG_PR_COUNT-1:0] DUT_wr_buf_enq_bank1_dest_PR, expected_wr_buf_enq_bank1_dest_PR;
	logic DUT_wr_buf_enq_bank1_is_mem, expected_wr_buf_enq_bank1_is_mem;
	logic [PA_WIDTH-2-1:0] DUT_wr_buf_enq_bank1_PA_word, expected_wr_buf_enq_bank1_PA_word;
	logic [3:0] DUT_wr_buf_enq_bank1_byte_mask, expected_wr_buf_enq_bank1_byte_mask;
	logic [31:0] DUT_wr_buf_enq_bank1_data, expected_wr_buf_enq_bank1_data;

    // write buffer enq feedback bank 1
	logic tb_wr_buf_enq_bank1_ready;
	logic tb_wr_buf_enq_bank1_mem_present;
	logic tb_wr_buf_enq_bank1_io_present;

    // write buffer WB data to PRF
	logic tb_wr_buf_WB_valid;
	logic [31:0] tb_wr_buf_WB_data;
	logic [LOG_PR_COUNT-1:0] tb_wr_buf_WB_PR;
        // don't need ROB_index as WB_send_complete = 1'b0

    // write buffer WB feedback from PRF
	logic DUT_wr_buf_WB_ready, expected_wr_buf_WB_ready;

    // sfence invalidation to MMU
	logic DUT_sfence_inv_valid, expected_sfence_inv_valid;
	logic [VA_WIDTH-1:0] DUT_sfence_inv_VA, expected_sfence_inv_VA;
	logic [ASID_WIDTH-1:0] DUT_sfence_inv_ASID, expected_sfence_inv_ASID;

    // sfence invalidation backpressure from MMU
	logic tb_sfence_inv_ready;

	// ROB instret advertisement
	logic [31:0] DUT_rob_instret, expected_rob_instret;

    // stats
    logic [31:0] DUT_alu_reg_complete_count, expected_alu_reg_complete_count;
    logic [31:0] DUT_alu_imm_complete_count, expected_alu_imm_complete_count;
    logic [31:0] DUT_branch_complete_count, expected_branch_complete_count;
    logic [31:0] DUT_ldu_complete_count, expected_ldu_complete_count;
    logic [31:0] DUT_stamofu_complete_count, expected_stamofu_complete_count;
    logic [31:0] DUT_sysu_complete_count, expected_sysu_complete_count;
    logic [31:0] DUT_wr_buf_enq_count, expected_wr_buf_enq_count;
    logic [31:0] DUT_restart_count, expected_restart_count;

    // hardware failure
	logic DUT_unrecoverable_fault, expected_unrecoverable_fault;

    // ----------------------------------------------------------------
    // DUT instantiation:

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
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // itlb req
		.itlb_req_valid(DUT_itlb_req_valid),
		.itlb_req_exec_mode(DUT_itlb_req_exec_mode),
		.itlb_req_virtual_mode(DUT_itlb_req_virtual_mode),
		.itlb_req_ASID(DUT_itlb_req_ASID),
		.itlb_req_VPN(DUT_itlb_req_VPN),

	    // itlb resp
		.itlb_resp_valid(tb_itlb_resp_valid),
		.itlb_resp_PPN(tb_itlb_resp_PPN),
		.itlb_resp_page_fault(tb_itlb_resp_page_fault),
		.itlb_resp_access_fault(tb_itlb_resp_access_fault),

	    // icache req
		.icache_req_valid(DUT_icache_req_valid),
		.icache_req_block_offset(DUT_icache_req_block_offset),
		.icache_req_index(DUT_icache_req_index),

	    // icache resp
		.icache_resp_valid_by_way(tb_icache_resp_valid_by_way),
		.icache_resp_tag_by_way(tb_icache_resp_tag_by_way),
		.icache_resp_instr_16B_by_way(tb_icache_resp_instr_16B_by_way),

	    // icache resp feedback
		.icache_resp_hit_valid(DUT_icache_resp_hit_valid),
		.icache_resp_hit_way(DUT_icache_resp_hit_way),
		.icache_resp_miss_valid(DUT_icache_resp_miss_valid),
		.icache_resp_miss_tag(DUT_icache_resp_miss_tag),

	    // dtlb req
		.dtlb_req_bank0_valid(DUT_dtlb_req_bank0_valid),
		.dtlb_req_bank0_exec_mode(DUT_dtlb_req_bank0_exec_mode),
		.dtlb_req_bank0_virtual_mode(DUT_dtlb_req_bank0_virtual_mode),
		.dtlb_req_bank0_ASID(DUT_dtlb_req_bank0_ASID),
		.dtlb_req_bank0_MXR(DUT_dtlb_req_bank0_MXR),
		.dtlb_req_bank0_SUM(DUT_dtlb_req_bank0_SUM),
		.dtlb_req_bank0_VPN(DUT_dtlb_req_bank0_VPN),
		.dtlb_req_bank0_is_read(DUT_dtlb_req_bank0_is_read),
		.dtlb_req_bank0_is_write(DUT_dtlb_req_bank0_is_write),

		.dtlb_req_bank1_valid(DUT_dtlb_req_bank1_valid),
		.dtlb_req_bank1_exec_mode(DUT_dtlb_req_bank1_exec_mode),
		.dtlb_req_bank1_virtual_mode(DUT_dtlb_req_bank1_virtual_mode),
		.dtlb_req_bank1_ASID(DUT_dtlb_req_bank1_ASID),
		.dtlb_req_bank1_MXR(DUT_dtlb_req_bank1_MXR),
		.dtlb_req_bank1_SUM(DUT_dtlb_req_bank1_SUM),
		.dtlb_req_bank1_VPN(DUT_dtlb_req_bank1_VPN),
		.dtlb_req_bank1_is_read(DUT_dtlb_req_bank1_is_read),
		.dtlb_req_bank1_is_write(DUT_dtlb_req_bank1_is_write),

	    // dtlb req feedback
		.dtlb_req_bank0_ready(tb_dtlb_req_bank0_ready),

		.dtlb_req_bank1_ready(tb_dtlb_req_bank1_ready),

	    // dtlb resp
		.dtlb_resp_bank0_hit(tb_dtlb_resp_bank0_hit),
		.dtlb_resp_bank0_PPN(tb_dtlb_resp_bank0_PPN),
		.dtlb_resp_bank0_is_mem(tb_dtlb_resp_bank0_is_mem),
		.dtlb_resp_bank0_page_fault(tb_dtlb_resp_bank0_page_fault),
		.dtlb_resp_bank0_access_fault(tb_dtlb_resp_bank0_access_fault),

		.dtlb_resp_bank1_hit(tb_dtlb_resp_bank1_hit),
		.dtlb_resp_bank1_PPN(tb_dtlb_resp_bank1_PPN),
		.dtlb_resp_bank1_is_mem(tb_dtlb_resp_bank1_is_mem),
		.dtlb_resp_bank1_page_fault(tb_dtlb_resp_bank1_page_fault),
		.dtlb_resp_bank1_access_fault(tb_dtlb_resp_bank1_access_fault),

	    // dtlb miss resp
		.dtlb_miss_resp_valid(tb_dtlb_miss_resp_valid),
		.dtlb_miss_resp_is_ldu(tb_dtlb_miss_resp_is_ldu),
		.dtlb_miss_resp_cq_index(tb_dtlb_miss_resp_cq_index),
		.dtlb_miss_resp_is_mq(tb_dtlb_miss_resp_is_mq),
		.dtlb_miss_resp_mq_index(tb_dtlb_miss_resp_mq_index),
		.dtlb_miss_resp_PPN(tb_dtlb_miss_resp_PPN),
		.dtlb_miss_resp_is_mem(tb_dtlb_miss_resp_is_mem),
		.dtlb_miss_resp_page_fault(tb_dtlb_miss_resp_page_fault),
		.dtlb_miss_resp_access_fault(tb_dtlb_miss_resp_access_fault),

	    // dcache req
		.dcache_req_bank0_valid(DUT_dcache_req_bank0_valid),
		.dcache_req_bank0_block_offset(DUT_dcache_req_bank0_block_offset),
		.dcache_req_bank0_index(DUT_dcache_req_bank0_index),
		.dcache_req_bank0_is_ldu(DUT_dcache_req_bank0_is_ldu),
		.dcache_req_bank0_cq_index(DUT_dcache_req_bank0_cq_index),
		.dcache_req_bank0_is_mq(DUT_dcache_req_bank0_is_mq),
		.dcache_req_bank0_mq_index(DUT_dcache_req_bank0_mq_index),

		.dcache_req_bank1_valid(DUT_dcache_req_bank1_valid),
		.dcache_req_bank1_block_offset(DUT_dcache_req_bank1_block_offset),
		.dcache_req_bank1_index(DUT_dcache_req_bank1_index),
		.dcache_req_bank1_is_ldu(DUT_dcache_req_bank1_is_ldu),
		.dcache_req_bank1_cq_index(DUT_dcache_req_bank1_cq_index),
		.dcache_req_bank1_is_mq(DUT_dcache_req_bank1_is_mq),
		.dcache_req_bank1_mq_index(DUT_dcache_req_bank1_mq_index),

	    // dcache req feedback
		.dcache_req_bank0_ready(tb_dcache_req_bank0_ready),

		.dcache_req_bank1_ready(tb_dcache_req_bank1_ready),

	    // dcache resp
		.dcache_resp_bank0_valid_by_way(tb_dcache_resp_bank0_valid_by_way),
		.dcache_resp_bank0_exclusive_by_way(tb_dcache_resp_bank0_exclusive_by_way),
		.dcache_resp_bank0_tag_by_way(tb_dcache_resp_bank0_tag_by_way),
		.dcache_resp_bank0_data_by_way(tb_dcache_resp_bank0_data_by_way),

		.dcache_resp_bank1_valid_by_way(tb_dcache_resp_bank1_valid_by_way),
		.dcache_resp_bank1_exclusive_by_way(tb_dcache_resp_bank1_exclusive_by_way),
		.dcache_resp_bank1_tag_by_way(tb_dcache_resp_bank1_tag_by_way),
		.dcache_resp_bank1_data_by_way(tb_dcache_resp_bank1_data_by_way),

	    // dcache resp feedback
		.dcache_resp_bank0_hit_valid(DUT_dcache_resp_bank0_hit_valid),
		.dcache_resp_bank0_hit_exclusive(DUT_dcache_resp_bank0_hit_exclusive),
		.dcache_resp_bank0_hit_way(DUT_dcache_resp_bank0_hit_way),
		.dcache_resp_bank0_miss_valid(DUT_dcache_resp_bank0_miss_valid),
		.dcache_resp_bank0_miss_prefetch(DUT_dcache_resp_bank0_miss_prefetch),
		.dcache_resp_bank0_miss_exclusive(DUT_dcache_resp_bank0_miss_exclusive),
		.dcache_resp_bank0_miss_tag(DUT_dcache_resp_bank0_miss_tag),

		.dcache_resp_bank1_hit_valid(DUT_dcache_resp_bank1_hit_valid),
		.dcache_resp_bank1_hit_exclusive(DUT_dcache_resp_bank1_hit_exclusive),
		.dcache_resp_bank1_hit_way(DUT_dcache_resp_bank1_hit_way),
		.dcache_resp_bank1_miss_valid(DUT_dcache_resp_bank1_miss_valid),
		.dcache_resp_bank1_miss_prefetch(DUT_dcache_resp_bank1_miss_prefetch),
		.dcache_resp_bank1_miss_exclusive(DUT_dcache_resp_bank1_miss_exclusive),
		.dcache_resp_bank1_miss_tag(DUT_dcache_resp_bank1_miss_tag),

	    // dcache miss resp
		.dcache_miss_resp_valid(tb_dcache_miss_resp_valid),
		.dcache_miss_resp_is_ldu(tb_dcache_miss_resp_is_ldu),
		.dcache_miss_resp_cq_index(tb_dcache_miss_resp_cq_index),
		.dcache_miss_resp_is_mq(tb_dcache_miss_resp_is_mq),
		.dcache_miss_resp_mq_index(tb_dcache_miss_resp_mq_index),
		.dcache_miss_resp_data(tb_dcache_miss_resp_data),

	    // write buffer enq bank 0
		.wr_buf_enq_bank0_valid(DUT_wr_buf_enq_bank0_valid),
		.wr_buf_enq_bank0_is_amo(DUT_wr_buf_enq_bank0_is_amo),
		.wr_buf_enq_bank0_op(DUT_wr_buf_enq_bank0_op),
		.wr_buf_enq_bank0_dest_PR(DUT_wr_buf_enq_bank0_dest_PR),
		.wr_buf_enq_bank0_is_mem(DUT_wr_buf_enq_bank0_is_mem),
		.wr_buf_enq_bank0_PA_word(DUT_wr_buf_enq_bank0_PA_word),
		.wr_buf_enq_bank0_byte_mask(DUT_wr_buf_enq_bank0_byte_mask),
		.wr_buf_enq_bank0_data(DUT_wr_buf_enq_bank0_data),

	    // write buffer enq feedback bank 0
		.wr_buf_enq_bank0_ready(tb_wr_buf_enq_bank0_ready),
		.wr_buf_enq_bank0_mem_present(tb_wr_buf_enq_bank0_mem_present),
		.wr_buf_enq_bank0_io_present(tb_wr_buf_enq_bank0_io_present),

	    // write buffer enq bank 1
		.wr_buf_enq_bank1_valid(DUT_wr_buf_enq_bank1_valid),
		.wr_buf_enq_bank1_is_amo(DUT_wr_buf_enq_bank1_is_amo),
		.wr_buf_enq_bank1_op(DUT_wr_buf_enq_bank1_op),
		.wr_buf_enq_bank1_dest_PR(DUT_wr_buf_enq_bank1_dest_PR),
		.wr_buf_enq_bank1_is_mem(DUT_wr_buf_enq_bank1_is_mem),
		.wr_buf_enq_bank1_PA_word(DUT_wr_buf_enq_bank1_PA_word),
		.wr_buf_enq_bank1_byte_mask(DUT_wr_buf_enq_bank1_byte_mask),
		.wr_buf_enq_bank1_data(DUT_wr_buf_enq_bank1_data),

	    // write buffer enq feedback bank 1
		.wr_buf_enq_bank1_ready(tb_wr_buf_enq_bank1_ready),
		.wr_buf_enq_bank1_mem_present(tb_wr_buf_enq_bank1_mem_present),
		.wr_buf_enq_bank1_io_present(tb_wr_buf_enq_bank1_io_present),

	    // write buffer WB data to PRF
		.wr_buf_WB_valid(tb_wr_buf_WB_valid),
		.wr_buf_WB_data(tb_wr_buf_WB_data),
		.wr_buf_WB_PR(tb_wr_buf_WB_PR),
	        // don't need ROB_index as WB_send_complete = 1'b0

	    // write buffer WB feedback from PRF
		.wr_buf_WB_ready(DUT_wr_buf_WB_ready),

	    // sfence invalidation to MMU
		.sfence_inv_valid(DUT_sfence_inv_valid),
		.sfence_inv_VA(DUT_sfence_inv_VA),
		.sfence_inv_ASID(DUT_sfence_inv_ASID),

	    // sfence invalidation backpressure from MMU
		.sfence_inv_ready(tb_sfence_inv_ready),

		// ROB instret advertisement
		.rob_instret(DUT_rob_instret),

        // stats
        .alu_reg_complete_count(DUT_alu_reg_complete_count),
        .alu_imm_complete_count(DUT_alu_imm_complete_count),
        .branch_complete_count(DUT_branch_complete_count),
        .ldu_complete_count(DUT_ldu_complete_count),
        .stamofu_complete_count(DUT_stamofu_complete_count),
        .sysu_complete_count(DUT_sysu_complete_count),
        .wr_buf_enq_count(DUT_wr_buf_enq_count),
        .restart_count(DUT_restart_count),

	    // hardware failure
		.unrecoverable_fault(DUT_unrecoverable_fault)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_itlb_req_valid !== DUT_itlb_req_valid) begin
			$display("TB ERROR: expected_itlb_req_valid (%h) != DUT_itlb_req_valid (%h)",
				expected_itlb_req_valid, DUT_itlb_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_exec_mode !== DUT_itlb_req_exec_mode) begin
			$display("TB ERROR: expected_itlb_req_exec_mode (%h) != DUT_itlb_req_exec_mode (%h)",
				expected_itlb_req_exec_mode, DUT_itlb_req_exec_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_virtual_mode !== DUT_itlb_req_virtual_mode) begin
			$display("TB ERROR: expected_itlb_req_virtual_mode (%h) != DUT_itlb_req_virtual_mode (%h)",
				expected_itlb_req_virtual_mode, DUT_itlb_req_virtual_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_ASID !== DUT_itlb_req_ASID) begin
			$display("TB ERROR: expected_itlb_req_ASID (%h) != DUT_itlb_req_ASID (%h)",
				expected_itlb_req_ASID, DUT_itlb_req_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_VPN !== DUT_itlb_req_VPN) begin
			$display("TB ERROR: expected_itlb_req_VPN (%h) != DUT_itlb_req_VPN (%h)",
				expected_itlb_req_VPN, DUT_itlb_req_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_valid !== DUT_icache_req_valid) begin
			$display("TB ERROR: expected_icache_req_valid (%h) != DUT_icache_req_valid (%h)",
				expected_icache_req_valid, DUT_icache_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_block_offset !== DUT_icache_req_block_offset) begin
			$display("TB ERROR: expected_icache_req_block_offset (%h) != DUT_icache_req_block_offset (%h)",
				expected_icache_req_block_offset, DUT_icache_req_block_offset);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_index !== DUT_icache_req_index) begin
			$display("TB ERROR: expected_icache_req_index (%h) != DUT_icache_req_index (%h)",
				expected_icache_req_index, DUT_icache_req_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_hit_valid !== DUT_icache_resp_hit_valid) begin
			$display("TB ERROR: expected_icache_resp_hit_valid (%h) != DUT_icache_resp_hit_valid (%h)",
				expected_icache_resp_hit_valid, DUT_icache_resp_hit_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_hit_way !== DUT_icache_resp_hit_way) begin
			$display("TB ERROR: expected_icache_resp_hit_way (%h) != DUT_icache_resp_hit_way (%h)",
				expected_icache_resp_hit_way, DUT_icache_resp_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_miss_valid !== DUT_icache_resp_miss_valid) begin
			$display("TB ERROR: expected_icache_resp_miss_valid (%h) != DUT_icache_resp_miss_valid (%h)",
				expected_icache_resp_miss_valid, DUT_icache_resp_miss_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_miss_tag !== DUT_icache_resp_miss_tag) begin
			$display("TB ERROR: expected_icache_resp_miss_tag (%h) != DUT_icache_resp_miss_tag (%h)",
				expected_icache_resp_miss_tag, DUT_icache_resp_miss_tag);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_valid !== DUT_dtlb_req_bank0_valid) begin
			$display("TB ERROR: expected_dtlb_req_bank0_valid (%h) != DUT_dtlb_req_bank0_valid (%h)",
				expected_dtlb_req_bank0_valid, DUT_dtlb_req_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_exec_mode !== DUT_dtlb_req_bank0_exec_mode) begin
			$display("TB ERROR: expected_dtlb_req_bank0_exec_mode (%h) != DUT_dtlb_req_bank0_exec_mode (%h)",
				expected_dtlb_req_bank0_exec_mode, DUT_dtlb_req_bank0_exec_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_virtual_mode !== DUT_dtlb_req_bank0_virtual_mode) begin
			$display("TB ERROR: expected_dtlb_req_bank0_virtual_mode (%h) != DUT_dtlb_req_bank0_virtual_mode (%h)",
				expected_dtlb_req_bank0_virtual_mode, DUT_dtlb_req_bank0_virtual_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_ASID !== DUT_dtlb_req_bank0_ASID) begin
			$display("TB ERROR: expected_dtlb_req_bank0_ASID (%h) != DUT_dtlb_req_bank0_ASID (%h)",
				expected_dtlb_req_bank0_ASID, DUT_dtlb_req_bank0_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_MXR !== DUT_dtlb_req_bank0_MXR) begin
			$display("TB ERROR: expected_dtlb_req_bank0_MXR (%h) != DUT_dtlb_req_bank0_MXR (%h)",
				expected_dtlb_req_bank0_MXR, DUT_dtlb_req_bank0_MXR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_SUM !== DUT_dtlb_req_bank0_SUM) begin
			$display("TB ERROR: expected_dtlb_req_bank0_SUM (%h) != DUT_dtlb_req_bank0_SUM (%h)",
				expected_dtlb_req_bank0_SUM, DUT_dtlb_req_bank0_SUM);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_VPN !== DUT_dtlb_req_bank0_VPN) begin
			$display("TB ERROR: expected_dtlb_req_bank0_VPN (%h) != DUT_dtlb_req_bank0_VPN (%h)",
				expected_dtlb_req_bank0_VPN, DUT_dtlb_req_bank0_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_is_read !== DUT_dtlb_req_bank0_is_read) begin
			$display("TB ERROR: expected_dtlb_req_bank0_is_read (%h) != DUT_dtlb_req_bank0_is_read (%h)",
				expected_dtlb_req_bank0_is_read, DUT_dtlb_req_bank0_is_read);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank0_is_write !== DUT_dtlb_req_bank0_is_write) begin
			$display("TB ERROR: expected_dtlb_req_bank0_is_write (%h) != DUT_dtlb_req_bank0_is_write (%h)",
				expected_dtlb_req_bank0_is_write, DUT_dtlb_req_bank0_is_write);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_valid !== DUT_dtlb_req_bank1_valid) begin
			$display("TB ERROR: expected_dtlb_req_bank1_valid (%h) != DUT_dtlb_req_bank1_valid (%h)",
				expected_dtlb_req_bank1_valid, DUT_dtlb_req_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_exec_mode !== DUT_dtlb_req_bank1_exec_mode) begin
			$display("TB ERROR: expected_dtlb_req_bank1_exec_mode (%h) != DUT_dtlb_req_bank1_exec_mode (%h)",
				expected_dtlb_req_bank1_exec_mode, DUT_dtlb_req_bank1_exec_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_virtual_mode !== DUT_dtlb_req_bank1_virtual_mode) begin
			$display("TB ERROR: expected_dtlb_req_bank1_virtual_mode (%h) != DUT_dtlb_req_bank1_virtual_mode (%h)",
				expected_dtlb_req_bank1_virtual_mode, DUT_dtlb_req_bank1_virtual_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_ASID !== DUT_dtlb_req_bank1_ASID) begin
			$display("TB ERROR: expected_dtlb_req_bank1_ASID (%h) != DUT_dtlb_req_bank1_ASID (%h)",
				expected_dtlb_req_bank1_ASID, DUT_dtlb_req_bank1_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_MXR !== DUT_dtlb_req_bank1_MXR) begin
			$display("TB ERROR: expected_dtlb_req_bank1_MXR (%h) != DUT_dtlb_req_bank1_MXR (%h)",
				expected_dtlb_req_bank1_MXR, DUT_dtlb_req_bank1_MXR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_SUM !== DUT_dtlb_req_bank1_SUM) begin
			$display("TB ERROR: expected_dtlb_req_bank1_SUM (%h) != DUT_dtlb_req_bank1_SUM (%h)",
				expected_dtlb_req_bank1_SUM, DUT_dtlb_req_bank1_SUM);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_VPN !== DUT_dtlb_req_bank1_VPN) begin
			$display("TB ERROR: expected_dtlb_req_bank1_VPN (%h) != DUT_dtlb_req_bank1_VPN (%h)",
				expected_dtlb_req_bank1_VPN, DUT_dtlb_req_bank1_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_is_read !== DUT_dtlb_req_bank1_is_read) begin
			$display("TB ERROR: expected_dtlb_req_bank1_is_read (%h) != DUT_dtlb_req_bank1_is_read (%h)",
				expected_dtlb_req_bank1_is_read, DUT_dtlb_req_bank1_is_read);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dtlb_req_bank1_is_write !== DUT_dtlb_req_bank1_is_write) begin
			$display("TB ERROR: expected_dtlb_req_bank1_is_write (%h) != DUT_dtlb_req_bank1_is_write (%h)",
				expected_dtlb_req_bank1_is_write, DUT_dtlb_req_bank1_is_write);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank0_valid !== DUT_dcache_req_bank0_valid) begin
			$display("TB ERROR: expected_dcache_req_bank0_valid (%h) != DUT_dcache_req_bank0_valid (%h)",
				expected_dcache_req_bank0_valid, DUT_dcache_req_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank0_block_offset !== DUT_dcache_req_bank0_block_offset) begin
			$display("TB ERROR: expected_dcache_req_bank0_block_offset (%h) != DUT_dcache_req_bank0_block_offset (%h)",
				expected_dcache_req_bank0_block_offset, DUT_dcache_req_bank0_block_offset);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank0_index !== DUT_dcache_req_bank0_index) begin
			$display("TB ERROR: expected_dcache_req_bank0_index (%h) != DUT_dcache_req_bank0_index (%h)",
				expected_dcache_req_bank0_index, DUT_dcache_req_bank0_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank0_is_ldu !== DUT_dcache_req_bank0_is_ldu) begin
			$display("TB ERROR: expected_dcache_req_bank0_is_ldu (%h) != DUT_dcache_req_bank0_is_ldu (%h)",
				expected_dcache_req_bank0_is_ldu, DUT_dcache_req_bank0_is_ldu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank0_cq_index !== DUT_dcache_req_bank0_cq_index) begin
			$display("TB ERROR: expected_dcache_req_bank0_cq_index (%h) != DUT_dcache_req_bank0_cq_index (%h)",
				expected_dcache_req_bank0_cq_index, DUT_dcache_req_bank0_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank0_is_mq !== DUT_dcache_req_bank0_is_mq) begin
			$display("TB ERROR: expected_dcache_req_bank0_is_mq (%h) != DUT_dcache_req_bank0_is_mq (%h)",
				expected_dcache_req_bank0_is_mq, DUT_dcache_req_bank0_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank0_mq_index !== DUT_dcache_req_bank0_mq_index) begin
			$display("TB ERROR: expected_dcache_req_bank0_mq_index (%h) != DUT_dcache_req_bank0_mq_index (%h)",
				expected_dcache_req_bank0_mq_index, DUT_dcache_req_bank0_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank1_valid !== DUT_dcache_req_bank1_valid) begin
			$display("TB ERROR: expected_dcache_req_bank1_valid (%h) != DUT_dcache_req_bank1_valid (%h)",
				expected_dcache_req_bank1_valid, DUT_dcache_req_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank1_block_offset !== DUT_dcache_req_bank1_block_offset) begin
			$display("TB ERROR: expected_dcache_req_bank1_block_offset (%h) != DUT_dcache_req_bank1_block_offset (%h)",
				expected_dcache_req_bank1_block_offset, DUT_dcache_req_bank1_block_offset);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank1_index !== DUT_dcache_req_bank1_index) begin
			$display("TB ERROR: expected_dcache_req_bank1_index (%h) != DUT_dcache_req_bank1_index (%h)",
				expected_dcache_req_bank1_index, DUT_dcache_req_bank1_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank1_is_ldu !== DUT_dcache_req_bank1_is_ldu) begin
			$display("TB ERROR: expected_dcache_req_bank1_is_ldu (%h) != DUT_dcache_req_bank1_is_ldu (%h)",
				expected_dcache_req_bank1_is_ldu, DUT_dcache_req_bank1_is_ldu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank1_cq_index !== DUT_dcache_req_bank1_cq_index) begin
			$display("TB ERROR: expected_dcache_req_bank1_cq_index (%h) != DUT_dcache_req_bank1_cq_index (%h)",
				expected_dcache_req_bank1_cq_index, DUT_dcache_req_bank1_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank1_is_mq !== DUT_dcache_req_bank1_is_mq) begin
			$display("TB ERROR: expected_dcache_req_bank1_is_mq (%h) != DUT_dcache_req_bank1_is_mq (%h)",
				expected_dcache_req_bank1_is_mq, DUT_dcache_req_bank1_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_req_bank1_mq_index !== DUT_dcache_req_bank1_mq_index) begin
			$display("TB ERROR: expected_dcache_req_bank1_mq_index (%h) != DUT_dcache_req_bank1_mq_index (%h)",
				expected_dcache_req_bank1_mq_index, DUT_dcache_req_bank1_mq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank0_hit_valid !== DUT_dcache_resp_bank0_hit_valid) begin
			$display("TB ERROR: expected_dcache_resp_bank0_hit_valid (%h) != DUT_dcache_resp_bank0_hit_valid (%h)",
				expected_dcache_resp_bank0_hit_valid, DUT_dcache_resp_bank0_hit_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank0_hit_exclusive !== DUT_dcache_resp_bank0_hit_exclusive) begin
			$display("TB ERROR: expected_dcache_resp_bank0_hit_exclusive (%h) != DUT_dcache_resp_bank0_hit_exclusive (%h)",
				expected_dcache_resp_bank0_hit_exclusive, DUT_dcache_resp_bank0_hit_exclusive);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank0_hit_way !== DUT_dcache_resp_bank0_hit_way) begin
			$display("TB ERROR: expected_dcache_resp_bank0_hit_way (%h) != DUT_dcache_resp_bank0_hit_way (%h)",
				expected_dcache_resp_bank0_hit_way, DUT_dcache_resp_bank0_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank0_miss_valid !== DUT_dcache_resp_bank0_miss_valid) begin
			$display("TB ERROR: expected_dcache_resp_bank0_miss_valid (%h) != DUT_dcache_resp_bank0_miss_valid (%h)",
				expected_dcache_resp_bank0_miss_valid, DUT_dcache_resp_bank0_miss_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank0_miss_prefetch !== DUT_dcache_resp_bank0_miss_prefetch) begin
			$display("TB ERROR: expected_dcache_resp_bank0_miss_prefetch (%h) != DUT_dcache_resp_bank0_miss_prefetch (%h)",
				expected_dcache_resp_bank0_miss_prefetch, DUT_dcache_resp_bank0_miss_prefetch);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank0_miss_exclusive !== DUT_dcache_resp_bank0_miss_exclusive) begin
			$display("TB ERROR: expected_dcache_resp_bank0_miss_exclusive (%h) != DUT_dcache_resp_bank0_miss_exclusive (%h)",
				expected_dcache_resp_bank0_miss_exclusive, DUT_dcache_resp_bank0_miss_exclusive);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank0_miss_tag !== DUT_dcache_resp_bank0_miss_tag) begin
			$display("TB ERROR: expected_dcache_resp_bank0_miss_tag (%h) != DUT_dcache_resp_bank0_miss_tag (%h)",
				expected_dcache_resp_bank0_miss_tag, DUT_dcache_resp_bank0_miss_tag);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank1_hit_valid !== DUT_dcache_resp_bank1_hit_valid) begin
			$display("TB ERROR: expected_dcache_resp_bank1_hit_valid (%h) != DUT_dcache_resp_bank1_hit_valid (%h)",
				expected_dcache_resp_bank1_hit_valid, DUT_dcache_resp_bank1_hit_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank1_hit_exclusive !== DUT_dcache_resp_bank1_hit_exclusive) begin
			$display("TB ERROR: expected_dcache_resp_bank1_hit_exclusive (%h) != DUT_dcache_resp_bank1_hit_exclusive (%h)",
				expected_dcache_resp_bank1_hit_exclusive, DUT_dcache_resp_bank1_hit_exclusive);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank1_hit_way !== DUT_dcache_resp_bank1_hit_way) begin
			$display("TB ERROR: expected_dcache_resp_bank1_hit_way (%h) != DUT_dcache_resp_bank1_hit_way (%h)",
				expected_dcache_resp_bank1_hit_way, DUT_dcache_resp_bank1_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank1_miss_valid !== DUT_dcache_resp_bank1_miss_valid) begin
			$display("TB ERROR: expected_dcache_resp_bank1_miss_valid (%h) != DUT_dcache_resp_bank1_miss_valid (%h)",
				expected_dcache_resp_bank1_miss_valid, DUT_dcache_resp_bank1_miss_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank1_miss_prefetch !== DUT_dcache_resp_bank1_miss_prefetch) begin
			$display("TB ERROR: expected_dcache_resp_bank1_miss_prefetch (%h) != DUT_dcache_resp_bank1_miss_prefetch (%h)",
				expected_dcache_resp_bank1_miss_prefetch, DUT_dcache_resp_bank1_miss_prefetch);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank1_miss_exclusive !== DUT_dcache_resp_bank1_miss_exclusive) begin
			$display("TB ERROR: expected_dcache_resp_bank1_miss_exclusive (%h) != DUT_dcache_resp_bank1_miss_exclusive (%h)",
				expected_dcache_resp_bank1_miss_exclusive, DUT_dcache_resp_bank1_miss_exclusive);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dcache_resp_bank1_miss_tag !== DUT_dcache_resp_bank1_miss_tag) begin
			$display("TB ERROR: expected_dcache_resp_bank1_miss_tag (%h) != DUT_dcache_resp_bank1_miss_tag (%h)",
				expected_dcache_resp_bank1_miss_tag, DUT_dcache_resp_bank1_miss_tag);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_valid !== DUT_wr_buf_enq_bank0_valid) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_valid (%h) != DUT_wr_buf_enq_bank0_valid (%h)",
				expected_wr_buf_enq_bank0_valid, DUT_wr_buf_enq_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_is_amo !== DUT_wr_buf_enq_bank0_is_amo) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_is_amo (%h) != DUT_wr_buf_enq_bank0_is_amo (%h)",
				expected_wr_buf_enq_bank0_is_amo, DUT_wr_buf_enq_bank0_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_op !== DUT_wr_buf_enq_bank0_op) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_op (%h) != DUT_wr_buf_enq_bank0_op (%h)",
				expected_wr_buf_enq_bank0_op, DUT_wr_buf_enq_bank0_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_dest_PR !== DUT_wr_buf_enq_bank0_dest_PR) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_dest_PR (%h) != DUT_wr_buf_enq_bank0_dest_PR (%h)",
				expected_wr_buf_enq_bank0_dest_PR, DUT_wr_buf_enq_bank0_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_is_mem !== DUT_wr_buf_enq_bank0_is_mem) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_is_mem (%h) != DUT_wr_buf_enq_bank0_is_mem (%h)",
				expected_wr_buf_enq_bank0_is_mem, DUT_wr_buf_enq_bank0_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_PA_word !== DUT_wr_buf_enq_bank0_PA_word) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_PA_word (%h) != DUT_wr_buf_enq_bank0_PA_word (%h)",
				expected_wr_buf_enq_bank0_PA_word, DUT_wr_buf_enq_bank0_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_byte_mask !== DUT_wr_buf_enq_bank0_byte_mask) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_byte_mask (%h) != DUT_wr_buf_enq_bank0_byte_mask (%h)",
				expected_wr_buf_enq_bank0_byte_mask, DUT_wr_buf_enq_bank0_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank0_data !== DUT_wr_buf_enq_bank0_data) begin
			$display("TB ERROR: expected_wr_buf_enq_bank0_data (%h) != DUT_wr_buf_enq_bank0_data (%h)",
				expected_wr_buf_enq_bank0_data, DUT_wr_buf_enq_bank0_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_valid !== DUT_wr_buf_enq_bank1_valid) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_valid (%h) != DUT_wr_buf_enq_bank1_valid (%h)",
				expected_wr_buf_enq_bank1_valid, DUT_wr_buf_enq_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_is_amo !== DUT_wr_buf_enq_bank1_is_amo) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_is_amo (%h) != DUT_wr_buf_enq_bank1_is_amo (%h)",
				expected_wr_buf_enq_bank1_is_amo, DUT_wr_buf_enq_bank1_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_op !== DUT_wr_buf_enq_bank1_op) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_op (%h) != DUT_wr_buf_enq_bank1_op (%h)",
				expected_wr_buf_enq_bank1_op, DUT_wr_buf_enq_bank1_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_dest_PR !== DUT_wr_buf_enq_bank1_dest_PR) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_dest_PR (%h) != DUT_wr_buf_enq_bank1_dest_PR (%h)",
				expected_wr_buf_enq_bank1_dest_PR, DUT_wr_buf_enq_bank1_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_is_mem !== DUT_wr_buf_enq_bank1_is_mem) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_is_mem (%h) != DUT_wr_buf_enq_bank1_is_mem (%h)",
				expected_wr_buf_enq_bank1_is_mem, DUT_wr_buf_enq_bank1_is_mem);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_PA_word !== DUT_wr_buf_enq_bank1_PA_word) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_PA_word (%h) != DUT_wr_buf_enq_bank1_PA_word (%h)",
				expected_wr_buf_enq_bank1_PA_word, DUT_wr_buf_enq_bank1_PA_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_byte_mask !== DUT_wr_buf_enq_bank1_byte_mask) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_byte_mask (%h) != DUT_wr_buf_enq_bank1_byte_mask (%h)",
				expected_wr_buf_enq_bank1_byte_mask, DUT_wr_buf_enq_bank1_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_bank1_data !== DUT_wr_buf_enq_bank1_data) begin
			$display("TB ERROR: expected_wr_buf_enq_bank1_data (%h) != DUT_wr_buf_enq_bank1_data (%h)",
				expected_wr_buf_enq_bank1_data, DUT_wr_buf_enq_bank1_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_WB_ready !== DUT_wr_buf_WB_ready) begin
			$display("TB ERROR: expected_wr_buf_WB_ready (%h) != DUT_wr_buf_WB_ready (%h)",
				expected_wr_buf_WB_ready, DUT_wr_buf_WB_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sfence_inv_valid !== DUT_sfence_inv_valid) begin
			$display("TB ERROR: expected_sfence_inv_valid (%h) != DUT_sfence_inv_valid (%h)",
				expected_sfence_inv_valid, DUT_sfence_inv_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sfence_inv_VA !== DUT_sfence_inv_VA) begin
			$display("TB ERROR: expected_sfence_inv_VA (%h) != DUT_sfence_inv_VA (%h)",
				expected_sfence_inv_VA, DUT_sfence_inv_VA);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sfence_inv_ASID !== DUT_sfence_inv_ASID) begin
			$display("TB ERROR: expected_sfence_inv_ASID (%h) != DUT_sfence_inv_ASID (%h)",
				expected_sfence_inv_ASID, DUT_sfence_inv_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_instret !== DUT_rob_instret) begin
			$display("TB ERROR: expected_rob_instret (%0d) != DUT_rob_instret (%0d)",
				expected_rob_instret, DUT_rob_instret);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_alu_reg_complete_count !== DUT_alu_reg_complete_count) begin
			$display("TB ERROR: expected_alu_reg_complete_count (%0d) != DUT_alu_reg_complete_count (%0d)",
				expected_alu_reg_complete_count, DUT_alu_reg_complete_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_alu_imm_complete_count !== DUT_alu_imm_complete_count) begin
			$display("TB ERROR: expected_alu_imm_complete_count (%0d) != DUT_alu_imm_complete_count (%0d)",
				expected_alu_imm_complete_count, DUT_alu_imm_complete_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_complete_count !== DUT_branch_complete_count) begin
			$display("TB ERROR: expected_branch_complete_count (%0d) != DUT_branch_complete_count (%0d)",
				expected_branch_complete_count, DUT_branch_complete_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_complete_count !== DUT_ldu_complete_count) begin
			$display("TB ERROR: expected_ldu_complete_count (%0d) != DUT_ldu_complete_count (%0d)",
				expected_ldu_complete_count, DUT_ldu_complete_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_complete_count !== DUT_stamofu_complete_count) begin
			$display("TB ERROR: expected_stamofu_complete_count (%0d) != DUT_stamofu_complete_count (%0d)",
				expected_stamofu_complete_count, DUT_stamofu_complete_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_complete_count !== DUT_sysu_complete_count) begin
			$display("TB ERROR: expected_sysu_complete_count (%0d) != DUT_sysu_complete_count (%0d)",
				expected_sysu_complete_count, DUT_sysu_complete_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wr_buf_enq_count !== DUT_wr_buf_enq_count) begin
			$display("TB ERROR: expected_wr_buf_enq_count (%0d) != DUT_wr_buf_enq_count (%0d)",
				expected_wr_buf_enq_count, DUT_wr_buf_enq_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_count !== DUT_restart_count) begin
			$display("TB ERROR: expected_restart_count (%0d) != DUT_restart_count (%0d)",
				expected_restart_count, DUT_restart_count);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_unrecoverable_fault !== DUT_unrecoverable_fault) begin
			$display("TB ERROR: expected_unrecoverable_fault (%h) != DUT_unrecoverable_fault (%h)",
				expected_unrecoverable_fault, DUT_unrecoverable_fault);
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
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_PPN = 22'h000000;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_icache_resp_instr_16B_by_way = {
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000
		};
	    // icache resp feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_bank0_ready = 1'b1;
		tb_dtlb_req_bank1_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_bank0_hit = 1'b0;
		tb_dtlb_resp_bank0_PPN = 22'h000000;
		tb_dtlb_resp_bank0_is_mem = 1'b0;
		tb_dtlb_resp_bank0_page_fault = 1'b0;
		tb_dtlb_resp_bank0_access_fault = 1'b0;
		tb_dtlb_resp_bank1_hit = 1'b0;
		tb_dtlb_resp_bank1_PPN = 22'h000000;
		tb_dtlb_resp_bank1_is_mem = 1'b0;
		tb_dtlb_resp_bank1_page_fault = 1'b0;
		tb_dtlb_resp_bank1_access_fault = 1'b0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_ldu = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_bank0_ready = 1'b1;
		tb_dcache_req_bank1_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_bank0_valid_by_way = 2'b00;
		tb_dcache_resp_bank0_exclusive_by_way = 2'b00;
		tb_dcache_resp_bank0_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_bank0_data_by_way = {32'h00000000, 32'h00000000};
		tb_dcache_resp_bank1_valid_by_way = 2'b00;
		tb_dcache_resp_bank1_exclusive_by_way = 2'b00;
		tb_dcache_resp_bank1_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_bank1_data_by_way = {32'h00000000, 32'h00000000};
	    // dcache resp feedback
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_ldu = 1'b0;
		tb_dcache_miss_resp_cq_index = 0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
	    // write buffer enq bank 0
	    // write buffer enq feedback bank 0
		tb_wr_buf_enq_bank0_ready = 1'b1;
		tb_wr_buf_enq_bank0_mem_present = 1'b0;
		tb_wr_buf_enq_bank0_io_present = 1'b0;
	    // write buffer enq bank 1
	    // write buffer enq feedback bank 1
		tb_wr_buf_enq_bank1_ready = 1'b1;
		tb_wr_buf_enq_bank1_mem_present = 1'b0;
		tb_wr_buf_enq_bank1_io_present = 1'b0;
	    // write buffer WB data to PRF
		tb_wr_buf_WB_valid = 1'b0;
		tb_wr_buf_WB_data = 32'h00000000;
		tb_wr_buf_WB_PR = 0;
	    // write buffer WB feedback from PRF
	    // sfence invalidation to MMU
	    // sfence invalidation backpressure from MMU
		// ROB instret advertisement
		tb_sfence_inv_ready = 1'b1;
	    // hardware failure

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b0;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_ASID = 9'h000;
		expected_itlb_req_VPN = 20'h00000;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b0;
		expected_icache_req_block_offset = 0;
		expected_icache_req_index = 0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h000000;
	    // dtlb req
		expected_dtlb_req_bank0_valid = 1'b0;
		expected_dtlb_req_bank0_exec_mode = M_MODE;
		expected_dtlb_req_bank0_virtual_mode = 1'b0;
		expected_dtlb_req_bank0_ASID = 9'h000;
		expected_dtlb_req_bank0_MXR = 1'b0;
		expected_dtlb_req_bank0_SUM = 1'b0;
		expected_dtlb_req_bank0_VPN = 20'h00000;
		expected_dtlb_req_bank0_is_read = 1'b0;
		expected_dtlb_req_bank0_is_write = 1'b1;
		expected_dtlb_req_bank1_valid = 1'b0;
		expected_dtlb_req_bank1_exec_mode = M_MODE;
		expected_dtlb_req_bank1_virtual_mode = 1'b0;
		expected_dtlb_req_bank1_ASID = 9'h000;
		expected_dtlb_req_bank1_MXR = 1'b0;
		expected_dtlb_req_bank1_SUM = 1'b0;
		expected_dtlb_req_bank1_VPN = 20'h00000;
		expected_dtlb_req_bank1_is_read = 1'b0;
		expected_dtlb_req_bank1_is_write = 1'b1;
	    // dtlb req feedback
	    // dtlb resp
	    // dtlb miss resp
	    // dcache req
		expected_dcache_req_bank0_valid = 1'b0;
		expected_dcache_req_bank0_block_offset = 0;
		expected_dcache_req_bank0_index = 0;
		expected_dcache_req_bank0_is_ldu = 1'b0;
		expected_dcache_req_bank0_cq_index = 0;
		expected_dcache_req_bank0_is_mq = 1'b0;
		expected_dcache_req_bank0_mq_index = 0;
		expected_dcache_req_bank1_valid = 1'b0;
		expected_dcache_req_bank1_block_offset = 0;
		expected_dcache_req_bank1_index = 0;
		expected_dcache_req_bank1_is_ldu = 1'b0;
		expected_dcache_req_bank1_cq_index = 0;
		expected_dcache_req_bank1_is_mq = 1'b0;
		expected_dcache_req_bank1_mq_index = 0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_bank0_hit_valid = 1'b0;
		expected_dcache_resp_bank0_hit_exclusive = 1'b1;
		expected_dcache_resp_bank0_hit_way = 1'b0;
		expected_dcache_resp_bank0_miss_valid = 1'b0;
		expected_dcache_resp_bank0_miss_prefetch = 1'b1;
		expected_dcache_resp_bank0_miss_exclusive = 1'b1;
		expected_dcache_resp_bank0_miss_tag = 22'h000000;
		expected_dcache_resp_bank1_hit_valid = 1'b0;
		expected_dcache_resp_bank1_hit_exclusive = 1'b1;
		expected_dcache_resp_bank1_hit_way = 1'b0;
		expected_dcache_resp_bank1_miss_valid = 1'b0;
		expected_dcache_resp_bank1_miss_prefetch = 1'b1;
		expected_dcache_resp_bank1_miss_exclusive = 1'b1;
		expected_dcache_resp_bank1_miss_tag = 22'h000000;
	    // dcache miss resp
	    // write buffer enq bank 0
		expected_wr_buf_enq_bank0_valid = 1'b0;
		expected_wr_buf_enq_bank0_is_amo = 1'b0;
		expected_wr_buf_enq_bank0_op = 4'b0000;
		expected_wr_buf_enq_bank0_dest_PR = 0;
		expected_wr_buf_enq_bank0_is_mem = 1'b0;
		expected_wr_buf_enq_bank0_PA_word = 32'h00000000;
		expected_wr_buf_enq_bank0_byte_mask = 4'b0000;
		expected_wr_buf_enq_bank0_data = 32'h00000000;
	    // write buffer enq feedback bank 0
	    // write buffer enq bank 1
		expected_wr_buf_enq_bank1_valid = 1'b0;
		expected_wr_buf_enq_bank1_is_amo = 1'b0;
		expected_wr_buf_enq_bank1_op = 4'b0000;
		expected_wr_buf_enq_bank1_dest_PR = 0;
		expected_wr_buf_enq_bank1_is_mem = 1'b0;
		expected_wr_buf_enq_bank1_PA_word = 32'h00000000;
		expected_wr_buf_enq_bank1_byte_mask = 4'b0000;
		expected_wr_buf_enq_bank1_data = 32'h00000000;
	    // write buffer enq feedback bank 1
	    // write buffer WB data to PRF
	    // write buffer WB feedback from PRF
		expected_wr_buf_WB_ready = 1'b1;
	    // sfence invalidation to MMU
		expected_sfence_inv_valid = 1'b0;
		expected_sfence_inv_VA = 20'h00000;
		expected_sfence_inv_ASID = 9'h000;
	    // sfence invalidation backpressure from MMU
		// ROB instret advertisement
		expected_rob_instret = 32'h0;
        // stats
        expected_alu_reg_complete_count = 32'h0;
        expected_alu_imm_complete_count = 32'h0;
        expected_branch_complete_count = 32'h0;
        expected_ldu_complete_count = 32'h0;
        expected_stamofu_complete_count = 32'h0;
        expected_sysu_complete_count = 32'h0;
        expected_wr_buf_enq_count = 32'h0;
        expected_restart_count = 32'h0;
	    // hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_PPN = 22'h000000;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {22'h000000, 22'h000000};
		tb_icache_resp_instr_16B_by_way = {
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000,
			16'h0000, 16'h0000
		};
	    // icache resp feedback
	    // dtlb req
	    // dtlb req feedback
		tb_dtlb_req_bank0_ready = 1'b1;
		tb_dtlb_req_bank1_ready = 1'b1;
	    // dtlb resp
		tb_dtlb_resp_bank0_hit = 1'b0;
		tb_dtlb_resp_bank0_PPN = 22'h000000;
		tb_dtlb_resp_bank0_is_mem = 1'b0;
		tb_dtlb_resp_bank0_page_fault = 1'b0;
		tb_dtlb_resp_bank0_access_fault = 1'b0;
		tb_dtlb_resp_bank1_hit = 1'b0;
		tb_dtlb_resp_bank1_PPN = 22'h000000;
		tb_dtlb_resp_bank1_is_mem = 1'b0;
		tb_dtlb_resp_bank1_page_fault = 1'b0;
		tb_dtlb_resp_bank1_access_fault = 1'b0;
	    // dtlb miss resp
		tb_dtlb_miss_resp_valid = 1'b0;
		tb_dtlb_miss_resp_is_ldu = 1'b0;
		tb_dtlb_miss_resp_cq_index = 0;
		tb_dtlb_miss_resp_is_mq = 1'b0;
		tb_dtlb_miss_resp_mq_index = 0;
		tb_dtlb_miss_resp_PPN = 22'h000000;
		tb_dtlb_miss_resp_is_mem = 1'b0;
		tb_dtlb_miss_resp_page_fault = 1'b0;
		tb_dtlb_miss_resp_access_fault = 1'b0;
	    // dcache req
	    // dcache req feedback
		tb_dcache_req_bank0_ready = 1'b1;
		tb_dcache_req_bank1_ready = 1'b1;
	    // dcache resp
		tb_dcache_resp_bank0_valid_by_way = 2'b00;
		tb_dcache_resp_bank0_exclusive_by_way = 2'b00;
		tb_dcache_resp_bank0_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_bank0_data_by_way = {32'h00000000, 32'h00000000};
		tb_dcache_resp_bank1_valid_by_way = 2'b00;
		tb_dcache_resp_bank1_exclusive_by_way = 2'b00;
		tb_dcache_resp_bank1_tag_by_way = {22'h000000, 22'h000000};
		tb_dcache_resp_bank1_data_by_way = {32'h00000000, 32'h00000000};
	    // dcache resp feedback
	    // dcache miss resp
		tb_dcache_miss_resp_valid = 1'b0;
		tb_dcache_miss_resp_is_ldu = 1'b0;
		tb_dcache_miss_resp_cq_index = 0;
		tb_dcache_miss_resp_is_mq = 1'b0;
		tb_dcache_miss_resp_mq_index = 0;
		tb_dcache_miss_resp_data = 32'h00000000;
	    // write buffer enq bank 0
	    // write buffer enq feedback bank 0
		tb_wr_buf_enq_bank0_ready = 1'b1;
		tb_wr_buf_enq_bank0_mem_present = 1'b0;
		tb_wr_buf_enq_bank0_io_present = 1'b0;
	    // write buffer enq bank 1
	    // write buffer enq feedback bank 1
		tb_wr_buf_enq_bank1_ready = 1'b1;
		tb_wr_buf_enq_bank1_mem_present = 1'b0;
		tb_wr_buf_enq_bank1_io_present = 1'b0;
	    // write buffer WB data to PRF
		tb_wr_buf_WB_valid = 1'b0;
		tb_wr_buf_WB_data = 32'h00000000;
		tb_wr_buf_WB_PR = 0;
	    // write buffer WB feedback from PRF
	    // sfence invalidation to MMU
	    // sfence invalidation backpressure from MMU
		// ROB instret advertisement
		tb_sfence_inv_ready = 1'b1;
        // stats
	    // hardware failure

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_ASID = 9'h000;
		expected_itlb_req_VPN = 20'h00000;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 0;
		expected_icache_req_index = 0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h000000;
	    // dtlb req
		expected_dtlb_req_bank0_valid = 1'b0;
		expected_dtlb_req_bank0_exec_mode = M_MODE;
		expected_dtlb_req_bank0_virtual_mode = 1'b0;
		expected_dtlb_req_bank0_ASID = 9'h000;
		expected_dtlb_req_bank0_MXR = 1'b0;
		expected_dtlb_req_bank0_SUM = 1'b0;
		expected_dtlb_req_bank0_VPN = 20'h00000;
		expected_dtlb_req_bank0_is_read = 1'b0;
		expected_dtlb_req_bank0_is_write = 1'b1;
		expected_dtlb_req_bank1_valid = 1'b0;
		expected_dtlb_req_bank1_exec_mode = M_MODE;
		expected_dtlb_req_bank1_virtual_mode = 1'b0;
		expected_dtlb_req_bank1_ASID = 9'h000;
		expected_dtlb_req_bank1_MXR = 1'b0;
		expected_dtlb_req_bank1_SUM = 1'b0;
		expected_dtlb_req_bank1_VPN = 20'h00000;
		expected_dtlb_req_bank1_is_read = 1'b0;
		expected_dtlb_req_bank1_is_write = 1'b1;
	    // dtlb req feedback
	    // dtlb resp
	    // dtlb miss resp
	    // dcache req
		expected_dcache_req_bank0_valid = 1'b0;
		expected_dcache_req_bank0_block_offset = 0;
		expected_dcache_req_bank0_index = 0;
		expected_dcache_req_bank0_is_ldu = 1'b0;
		expected_dcache_req_bank0_cq_index = 0;
		expected_dcache_req_bank0_is_mq = 1'b0;
		expected_dcache_req_bank0_mq_index = 0;
		expected_dcache_req_bank1_valid = 1'b0;
		expected_dcache_req_bank1_block_offset = 0;
		expected_dcache_req_bank1_index = 0;
		expected_dcache_req_bank1_is_ldu = 1'b0;
		expected_dcache_req_bank1_cq_index = 0;
		expected_dcache_req_bank1_is_mq = 1'b0;
		expected_dcache_req_bank1_mq_index = 0;
	    // dcache req feedback
	    // dcache resp
	    // dcache resp feedback
		expected_dcache_resp_bank0_hit_valid = 1'b0;
		expected_dcache_resp_bank0_hit_exclusive = 1'b1;
		expected_dcache_resp_bank0_hit_way = 1'b0;
		expected_dcache_resp_bank0_miss_valid = 1'b0;
		expected_dcache_resp_bank0_miss_prefetch = 1'b1;
		expected_dcache_resp_bank0_miss_exclusive = 1'b1;
		expected_dcache_resp_bank0_miss_tag = 22'h000000;
		expected_dcache_resp_bank1_hit_valid = 1'b0;
		expected_dcache_resp_bank1_hit_exclusive = 1'b1;
		expected_dcache_resp_bank1_hit_way = 1'b0;
		expected_dcache_resp_bank1_miss_valid = 1'b0;
		expected_dcache_resp_bank1_miss_prefetch = 1'b1;
		expected_dcache_resp_bank1_miss_exclusive = 1'b1;
		expected_dcache_resp_bank1_miss_tag = 22'h000000;
	    // dcache miss resp
	    // write buffer enq bank 0
		expected_wr_buf_enq_bank0_valid = 1'b0;
		expected_wr_buf_enq_bank0_is_amo = 1'b0;
		expected_wr_buf_enq_bank0_op = 4'b0000;
		expected_wr_buf_enq_bank0_dest_PR = 0;
		expected_wr_buf_enq_bank0_is_mem = 1'b0;
		expected_wr_buf_enq_bank0_PA_word = 32'h00000000;
		expected_wr_buf_enq_bank0_byte_mask = 4'b0000;
		expected_wr_buf_enq_bank0_data = 32'h00000000;
	    // write buffer enq feedback bank 0
	    // write buffer enq bank 1
		expected_wr_buf_enq_bank1_valid = 1'b0;
		expected_wr_buf_enq_bank1_is_amo = 1'b0;
		expected_wr_buf_enq_bank1_op = 4'b0000;
		expected_wr_buf_enq_bank1_dest_PR = 0;
		expected_wr_buf_enq_bank1_is_mem = 1'b0;
		expected_wr_buf_enq_bank1_PA_word = 32'h00000000;
		expected_wr_buf_enq_bank1_byte_mask = 4'b0000;
		expected_wr_buf_enq_bank1_data = 32'h00000000;
	    // write buffer enq feedback bank 1
	    // write buffer WB data to PRF
	    // write buffer WB feedback from PRF
		expected_wr_buf_WB_ready = 1'b1;
	    // sfence invalidation to MMU
		expected_sfence_inv_valid = 1'b0;
		expected_sfence_inv_VA = 20'h00000;
		expected_sfence_inv_ASID = 9'h000;
	    // sfence invalidation backpressure from MMU
		// ROB instret advertisement
		expected_rob_instret = 32'h0;
        // stats
        expected_alu_reg_complete_count = 32'h0;
        expected_alu_imm_complete_count = 32'h0;
        expected_branch_complete_count = 32'h0;
        expected_ldu_complete_count = 32'h0;
        expected_stamofu_complete_count = 32'h0;
        expected_sysu_complete_count = 32'h0;
        expected_wr_buf_enq_count = 32'h0;
        expected_restart_count = 32'h0;
	    // hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
		// IPC tester
			// 0x400 = 1024 cycles
        test_case = "IPC tester";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 1024; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("cycle %0d", i);
			// $display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// itlb req
			// itlb resp
			tb_itlb_resp_valid = i > 0;
			tb_itlb_resp_PPN = 22'h000000;
			tb_itlb_resp_page_fault = 1'b0;
			tb_itlb_resp_access_fault = 1'b0;
			// icache req
			// icache resp
			tb_icache_resp_valid_by_way = 2'b01;
			tb_icache_resp_tag_by_way = {22'h000000, 22'h000000};
			tb_icache_resp_instr_16B_by_way = {
				16'h0000, 16'h0000,
				16'h0000, 16'h0000,
				16'h0000, 16'h0000,
				16'h0000, 16'h0000,
            // friendly indep repeat: IPC = 3.645
                // 32'h293d0437,   // LUI x8, 0x293d0
                // 32'h407302b3,   // SUB x5, x6, x7
                // 32'h02822183,   // LW x3, 0x28(x4)
				// 32'h00410093    // ADDI x1, x2, 4
            // friendly indep repeat w/ store: IPC = 2.957 (lower because of dest PR conflicts)
                // 32'h293d0437,   // LUI x8, 0x293d0
                // 32'h10532223,   // SW x5, 0x104(x6)
                // 32'h02822183,   // LW x3, 0x28(x4)
				// 32'h00410093    // ADDI x1, x2, 4
            // friendly all reg zero's repeat: IPC = 3.645
                // 32'h293d0437,   // LUI x8, 0x293d0
                // 32'h400002b3,   // SUB x5, x0, x0
                // 32'h02802183,   // LW x3, 0x28(x0)
				// 32'h00400093    // ADDI x1, x0, 4
            // more dependent chain: IPC = 1.310
                // 32'h293d0437,   // LUI x8, 0x293d0
                // 32'h40320233,   // SUB x4, x4, x3
                // 32'h0280a183,   // LW x3, 0x28(x1)
				// 32'h00408093    // ADDI x1, x1, 4
            // highly dependent chain: IPC = 0.330
                // 32'h0021e0b3,   // OR x1, x3, x2
                // 32'h00c16193,   // ORI x3, x2, 12
                // 32'h00308133,   // ADD x2, x1, x3
				// 32'h00408093    // ADDI x1, x1, 4
            // all alu_reg indep: IPC = 0.791 (get 0.988 if increase DQ width to 5)
                // 32'h002081b3,   // ADD x3, x1, x2
                // 32'h002081b3,   // ADD x3, x1, x2
                // 32'h002081b3,   // ADD x3, x1, x2
				// 32'h002081b3    // ADD x3, x1, x2
            // all alu_imm dep: IPC = 0.330
                // 32'h00408093,   // ADDI x1, x1, 4
                // 32'h00408093,   // ADDI x1, x1, 4
                // 32'h00408093,   // ADDI x1, x1, 4
                // 32'h00408093    // ADDI x1, x1, 4
            // all stores indep: IPC = 0.785 (get 0.981 if increase DQ width to 5)
                // 32'h03092a23,   // SW x16, 0x34(x18)
                // 32'h02b6aa23,   // SW x11, 0x34(x13)
                // 32'h02642a23,   // SW x6, 0x34(x8)
                // 32'h0211aa23    // SW x1, 0x34(x3)
            // all BRU indep: IPC = 0.791 (get 0.986 if increase DQ width to 5)
                // 32'hff5ff06f,   // JAL x0, -12
                // 32'h00125e17,   // AUIPC x28, 0x125
                // 32'h08001563,   // BNE x0, x0, 0x8a
                // 32'h293d0437    // LUI x8, 0x293d0
            // 4x indep instr loop: IPC = 2.953
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h02822303,   // LW x6, 0x28(x4)
                // 32'h00410093,   // ADDI x1, x2, 4
                // 32'h00518433    // ADD x8, x3, x5
            // 4x indep instr loop w/ store: IPC = 3.570
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h10532223,   // SW x5, 0x104(x6)
                // 32'h02822183,   // LW x3, 0x28(x4)
				// 32'h00410093    // ADDI x1, x2, 4
            // 4x dep instr loop: IPC = 0.673
                // 32'hfe338ae3,   // BEQ x7, x3, -12
                // 32'h02822283,   // LW x5, 0x28(x4)
                // 32'h00410193,   // ADDI x3, x2, 4
                // 32'h00328133    // ADD x2, x5, x3
            // memcpy loop: IPC = 1.316
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h7e30aa23,   // SW x3, 0x7f4(x1)
                // 32'h0280a183,   // LW x3, 0x28(x1)
				// 32'h00408093    // ADDI x1, x1, 4
            // 3x instr loop: IPC = 2.531
                // 32'hfe938ce3,   // BEQ x7, x9, -8
                // 32'h02822303,   // LW x6, 0x28(x4)
                // 32'h00410093,   // ADDI x1, x2, 4
                // 32'h00518433    // ADD x8, x3, x5
            // 2x instr loop: IPC = 1.975
                // 32'hfe938ee3,   // BEQ x7, x9, -4
                // 32'h02822303,   // LW x6, 0x28(x4)
                // 32'h00410093,   // ADDI x1, x2, 4
                // 32'h00518433    // ADD x8, x3, x5
            // 1x instr loop: IPC = 1.010
                // 32'h00938063,   // BEQ x7, x9, 0
                // 32'h02822303,   // LW x6, 0x28(x4)
                // 32'h00410093,   // ADDI x1, x2, 4
                // 32'h00518433    // ADD x8, x3, x5
            // 1x1 store-load dep no pred: IPC = 1.004
                // 32'h0284a403,   // LW x8, 0x28(x9)
                // 32'h00430393,   // ADDI x7, x6, 4
                // 32'h004182b3,   // ADD x5, x3, x4
                // 32'h02112423    // SW x1, 0x28(x2)
            // 2x2 store-load dep no pred: IPC = 1.078
                // 32'h0282a183,   // LW x3, 0x28(x5)
                // 32'h1042a203,   // LW x4, 0x104(x5)
                // 32'h1022a223,   // SW x2, 0x104(x5)
                // 32'h0212a423    // SW x1, 0x28(x5)
            // 2x 1x1 store-load dep no pred: IPC = 0.799
                // 32'h0282a203,   // LW x4, 0x28(x5)
                // 32'h0222a423,   // SW x2, 0x28(x5)
                // 32'h0282a183,   // LW x3, 0x28(x5)
                // 32'h0212a423    // SW x1, 0x28(x5)
            // 2x 1x1 store-load dep no pred w/ reg dep: IPC = 0.662
                // 32'h02822203,   // LW x4, 0x28(x4)
                // 32'h02222423,   // SW x2, 0x28(x4)
                // 32'h02822183,   // LW x3, 0x28(x4)
                // 32'h02122423    // SW x1, 0x28(x4)
			// 1x1 store-load dep w/ pred: IPC = 1.918
                // 32'hfe838ae3,   // BEQ x7, x8, -12
                // 32'h02832283,   // LW x5, 0x28(x6)
                // 32'h00420193,   // ADDI x3, x4, 4
                // 32'h02112423    // SW x1, 0x28(x2)
			// 1x1 no store-load dep: IPC = 3.418
                // 32'hfe838ae3,   // BEQ x7, x8, -12
                // 32'h02832283,   // LW x5, 0x28(x6)
                // 32'h00420193,   // ADDI x3, x4, 4
				// 32'h10112223    // SW x1, 0x104(x2)
            // 4x indep w/ misaligned load (bank0): IPC = 0.986
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h10622183,   // LW x3, 0x106(x4)
				// 32'h02532423,   // SW x5, 0x28(x6)
				// 32'h00410093    // ADDI x1, x2, 4
            // 4x indep w/ misaligned load (bank1): IPC = 0.986
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h0e622183,   // LW x3, 0xE6(x4)
				// 32'h02532423,   // SW x5, 0x28(x6)
				// 32'h00410093    // ADDI x1, x2, 4
            // 4x indep w/ misaligned store: IPC = 1.125
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h10532323,   // SW x5, 0x106(x6)
                // 32'h02822183,   // LW x3, 0x28(x4)
				// 32'h00410093    // ADDI x1, x2, 4
            // aligned store, misaligned load: IPC = 1.043
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h02a22183,   // LW x3, 0x2A(x4)
				// 32'h02532423,   // SW x5, 0x28(x6)
				// 32'h00410093    // ADDI x1, x2, 4
            // misaligned store, aligned load: IPC = 0.261
                // 32'hfe938ae3,   // BEQ x7, x9, -12
                // 32'h02822183,   // LW x3, 0x28(x4)
				// 32'h02532523,   // SW x5, 0x2A(x6)
				// 32'h00410093    // ADDI x1, x2, 4
			// compressed friendly indep repeat: IPC = 3.785
                // 16'h647d,   // C.LUI x8, 31
                // 16'h808e,   // C.MV x1, x3
                // 16'h4544,   // C.LW x9, 12(x10)
				// 16'h103c,   // C.ADDI4SPN x15, 40
                // 16'h647d,   // C.LUI x8, 31
                // 16'h808e,   // C.MV x1, x3
                // 16'h4544,   // C.LW x9, 12(x10)
				// 16'h103c    // C.ADDI4SPN x15, 40
            // uncompressed friendly indep repeat: IPC = 3.785
                // 32'h0001f437,   // LUI x8, 31
                // 32'h003000b3,   // ADD x1, x0, x3
                // 32'h00c52483,   // LW x9, 12(x10)
				// 32'h02810793    // ADDI x15, x2, 40
            // compressed 4x indep instr loop w/ store: IPC = 1.931
                // 16'h0000,   // NONE
                // 16'h0000,   // NONE
                // 16'h0000,   // NONE
				// 16'h0000,   // NONE
                // 16'hdc6d,   // C.BEQZ x8, -6
                // 16'hc24c,   // C.SW x11, 4(x12)
                // 16'h4544,   // C.LW x9, 12(x10)
				// 16'h103c    // C.ADDI4SPN x15, 40
            // uncompressed 4x indep instr loop w/ store: IPC = 1.939
                // 32'hfe040ae3,   // BEQ x8, x0, -12
                // 32'h00b62223,   // SW x11, 4(x12)
                // 32'h00c52483,   // LW x9, 12(x10)
				// 32'h02810793    // ADDI x15, x2, 40
            // compressed 8x indep instr loop w/ store: IPC = 0.531 (BUG)
                16'hd86d,   // C.BEQZ x8, -14
                16'hc24c,   // C.SW x11, 4(x12)
                16'h4544,   // C.LW x9, 12(x10)
				16'h103c,   // C.ADDI4SPN x15, 40
                16'h647d,   // C.LUI x8, 31
                16'hc24c,   // C.SW x11, 4(x12)
                16'h4544,   // C.LW x9, 12(x10)
				16'h103c    // C.ADDI4SPN x15, 40
			};
			// icache resp feedback
			// dtlb req
			// dtlb req feedback
			tb_dtlb_req_bank0_ready = 1'b1;
			tb_dtlb_req_bank1_ready = 1'b1;
			// dtlb resp
			tb_dtlb_resp_bank0_hit = 1'b1;
			tb_dtlb_resp_bank0_PPN = 22'h000000;
			tb_dtlb_resp_bank0_is_mem = 1'b1;
			tb_dtlb_resp_bank0_page_fault = 1'b0;
			tb_dtlb_resp_bank0_access_fault = 1'b0;
			tb_dtlb_resp_bank1_hit = 1'b1;
			tb_dtlb_resp_bank1_PPN = 22'h000000;
			tb_dtlb_resp_bank1_is_mem = 1'b1;
			tb_dtlb_resp_bank1_page_fault = 1'b0;
			tb_dtlb_resp_bank1_access_fault = 1'b0;
			// dtlb miss resp
			tb_dtlb_miss_resp_valid = 1'b0;
			tb_dtlb_miss_resp_is_ldu = 1'b0;
			tb_dtlb_miss_resp_cq_index = 0;
			tb_dtlb_miss_resp_is_mq = 1'b0;
			tb_dtlb_miss_resp_mq_index = 0;
			tb_dtlb_miss_resp_PPN = 22'h000000;
			tb_dtlb_miss_resp_is_mem = 1'b0;
			tb_dtlb_miss_resp_page_fault = 1'b0;
			tb_dtlb_miss_resp_access_fault = 1'b0;
			// dcache req
			// dcache req feedback
			tb_dcache_req_bank0_ready = 1'b1;
			tb_dcache_req_bank1_ready = 1'b1;
			// dcache resp
			tb_dcache_resp_bank0_valid_by_way = 2'b01;
			tb_dcache_resp_bank0_exclusive_by_way = 2'b01;
			tb_dcache_resp_bank0_tag_by_way = {22'h000000, 22'h000000};
			tb_dcache_resp_bank0_data_by_way = {32'h00000000, 32'h00000000};
			tb_dcache_resp_bank1_valid_by_way = 2'b01;
			tb_dcache_resp_bank1_exclusive_by_way = 2'b01;
			tb_dcache_resp_bank1_tag_by_way = {22'h000000, 22'h000000};
			tb_dcache_resp_bank1_data_by_way = {32'h00000000, 32'h00000000};
			// dcache resp feedback
			// dcache miss resp
			tb_dcache_miss_resp_valid = 1'b0;
			tb_dcache_miss_resp_is_ldu = 1'b0;
			tb_dcache_miss_resp_cq_index = 0;
			tb_dcache_miss_resp_is_mq = 1'b0;
			tb_dcache_miss_resp_mq_index = 0;
			tb_dcache_miss_resp_data = 32'h00000000;
			// write buffer enq bank 0
			// write buffer enq feedback bank 0
			tb_wr_buf_enq_bank0_ready = 1'b1;
			tb_wr_buf_enq_bank0_mem_present = 1'b0;
			tb_wr_buf_enq_bank0_io_present = 1'b0;
			// write buffer enq bank 1
			// write buffer enq feedback bank 1
			tb_wr_buf_enq_bank1_ready = 1'b1;
			tb_wr_buf_enq_bank1_mem_present = 1'b0;
			tb_wr_buf_enq_bank1_io_present = 1'b0;
			// write buffer WB data to PRF
			tb_wr_buf_WB_valid = 1'b0;
			tb_wr_buf_WB_data = 32'h00000000;
			tb_wr_buf_WB_PR = 0;
			// write buffer WB feedback from PRF
			// sfence invalidation to MMU
			// sfence invalidation backpressure from MMU
			// ROB instret advertisement
			tb_sfence_inv_ready = 1'b1;
            // stats
			// hardware failure

			@(negedge CLK);

			// outputs:

			// itlb req
			expected_itlb_req_valid = 1'b1;
			expected_itlb_req_exec_mode = M_MODE;
			expected_itlb_req_virtual_mode = 1'b0;
			expected_itlb_req_ASID = 9'h000;
			expected_itlb_req_VPN = 20'h00000;
			// itlb resp
			// icache req
			expected_icache_req_valid = 1'b1;
			expected_icache_req_block_offset = i % 2;
			expected_icache_req_index = i / 2;
			// icache resp
			// icache resp feedback
			expected_icache_resp_hit_valid = i > 0;
			expected_icache_resp_hit_way = 1'b0;
			expected_icache_resp_miss_valid = 1'b0;
			expected_icache_resp_miss_tag = 22'h000000;
			// dtlb req
			expected_dtlb_req_bank0_valid = 1'b0;
			expected_dtlb_req_bank0_exec_mode = M_MODE;
			expected_dtlb_req_bank0_virtual_mode = 1'b0;
			expected_dtlb_req_bank0_ASID = 9'h000;
			expected_dtlb_req_bank0_MXR = 1'b0;
			expected_dtlb_req_bank0_SUM = 1'b0;
			expected_dtlb_req_bank0_VPN = 20'h00000;
			expected_dtlb_req_bank0_is_read = 1'b0;
			expected_dtlb_req_bank0_is_write = 1'b1;
			expected_dtlb_req_bank1_valid = 1'b0;
			expected_dtlb_req_bank1_exec_mode = M_MODE;
			expected_dtlb_req_bank1_virtual_mode = 1'b0;
			expected_dtlb_req_bank1_ASID = 9'h000;
			expected_dtlb_req_bank1_MXR = 1'b0;
			expected_dtlb_req_bank1_SUM = 1'b0;
			expected_dtlb_req_bank1_VPN = 20'h00000;
			expected_dtlb_req_bank1_is_read = 1'b0;
			expected_dtlb_req_bank1_is_write = 1'b1;
			// dtlb req feedback
			// dtlb resp
			// dtlb miss resp
			// dcache req
			expected_dcache_req_bank0_valid = 1'b0;
			expected_dcache_req_bank0_block_offset = 0;
			expected_dcache_req_bank0_index = 0;
			expected_dcache_req_bank0_is_ldu = 1'b0;
			expected_dcache_req_bank0_cq_index = 0;
			expected_dcache_req_bank0_is_mq = 1'b0;
			expected_dcache_req_bank0_mq_index = 0;
			expected_dcache_req_bank1_valid = 1'b0;
			expected_dcache_req_bank1_block_offset = 0;
			expected_dcache_req_bank1_index = 0;
			expected_dcache_req_bank1_is_ldu = 1'b0;
			expected_dcache_req_bank1_cq_index = 0;
			expected_dcache_req_bank1_is_mq = 1'b0;
			expected_dcache_req_bank1_mq_index = 0;
			// dcache req feedback
			// dcache resp
			// dcache resp feedback
			expected_dcache_resp_bank0_hit_valid = 1'b0;
			expected_dcache_resp_bank0_hit_exclusive = 1'b1;
			expected_dcache_resp_bank0_hit_way = 1'b0;
			expected_dcache_resp_bank0_miss_valid = 1'b0;
			expected_dcache_resp_bank0_miss_prefetch = 1'b1;
			expected_dcache_resp_bank0_miss_exclusive = 1'b1;
			expected_dcache_resp_bank0_miss_tag = 22'h000000;
			expected_dcache_resp_bank1_hit_valid = 1'b0;
			expected_dcache_resp_bank1_hit_exclusive = 1'b1;
			expected_dcache_resp_bank1_hit_way = 1'b0;
			expected_dcache_resp_bank1_miss_valid = 1'b0;
			expected_dcache_resp_bank1_miss_prefetch = 1'b1;
			expected_dcache_resp_bank1_miss_exclusive = 1'b1;
			expected_dcache_resp_bank1_miss_tag = 22'h000000;
			// dcache miss resp
			// write buffer enq bank 0
			expected_wr_buf_enq_bank0_valid = 1'b0;
			expected_wr_buf_enq_bank0_is_amo = 1'b0;
			expected_wr_buf_enq_bank0_op = 4'b0000;
			expected_wr_buf_enq_bank0_dest_PR = 0;
			expected_wr_buf_enq_bank0_is_mem = 1'b0;
			expected_wr_buf_enq_bank0_PA_word = 32'h00000000;
			expected_wr_buf_enq_bank0_byte_mask = 4'b0000;
			expected_wr_buf_enq_bank0_data = 32'h00000000;
			// write buffer enq feedback bank 0
			// write buffer enq bank 1
			expected_wr_buf_enq_bank1_valid = 1'b0;
			expected_wr_buf_enq_bank1_is_amo = 1'b0;
			expected_wr_buf_enq_bank1_op = 4'b0000;
			expected_wr_buf_enq_bank1_dest_PR = 0;
			expected_wr_buf_enq_bank1_is_mem = 1'b0;
			expected_wr_buf_enq_bank1_PA_word = 32'h00000000;
			expected_wr_buf_enq_bank1_byte_mask = 4'b0000;
			expected_wr_buf_enq_bank1_data = 32'h00000000;
			// write buffer enq feedback bank 1
			// write buffer WB data to PRF
			// write buffer WB feedback from PRF
			expected_wr_buf_WB_ready = 1'b1;
			// sfence invalidation to MMU
			expected_sfence_inv_valid = 1'b0;
			expected_sfence_inv_VA = 20'h00000;
			expected_sfence_inv_ASID = 9'h000;
			// sfence invalidation backpressure from MMU
			// ROB instret advertisement
			expected_rob_instret = 0;
            // stats
            expected_alu_reg_complete_count = 32'h0;
            expected_alu_imm_complete_count = 32'h0;
            expected_branch_complete_count = 32'h0;
            expected_ldu_complete_count = 32'h0;
            expected_stamofu_complete_count = 32'h0;
            expected_sysu_complete_count = 32'h0;
            expected_wr_buf_enq_count = 32'h0;
            expected_restart_count = 32'h0;
			// hardware failure
			expected_unrecoverable_fault = 1'b0;

			// check_outputs();
		end
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