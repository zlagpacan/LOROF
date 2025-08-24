/*
    Filename: core.sv
    Author: zlagpacan
    Description: RTL for CPU Core
    Spec: LOROF/spec/design/core.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module core #(
    parameter FETCH_UNIT_WAIT_FOR_RESTART_STATE = 1'b1,
    parameter ROB_RESTART_ON_RESET = 1'b1,

    parameter INIT_PC = 32'h00000000,
    parameter INIT_ASID = 9'h000,
    parameter INIT_EXEC_MODE = M_MODE,
    parameter INIT_VIRTUAL_MODE = 1'b0,
    parameter INIT_MXR = 1'b0,
    parameter INIT_SUM = 1'b0,
	parameter INIT_TRAP_SFENCE = 1'b0,
	parameter INIT_TRAP_WFI = 1'b0,
	parameter INIT_TRAP_SRET = 1'b0,
    parameter INIT_TVEC_BASE_PC = 32'h0000F000
) (
    // seq
    input logic CLK,
    input logic nRST,

    // itlb req
    output logic                    itlb_req_valid,
    output logic [1:0]              itlb_req_exec_mode,
    output logic                    itlb_req_virtual_mode,
    output logic [ASID_WIDTH-1:0]   itlb_req_ASID,
    output logic [VPN_WIDTH-1:0]    itlb_req_VPN,

    // itlb resp
    input logic                     itlb_resp_valid,
    input logic [PPN_WIDTH-1:0]     itlb_resp_PPN,
    input logic                     itlb_resp_page_fault,
    input logic                     itlb_resp_access_fault,

    // icache req
    output logic                                        icache_req_valid,
    output logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]  icache_req_block_offset,
    output logic [ICACHE_INDEX_WIDTH-1:0]               icache_req_index,

    // icache resp
    input logic [1:0]                               icache_resp_valid_by_way,
    input logic [1:0][ICACHE_TAG_WIDTH-1:0]         icache_resp_tag_by_way,
    input logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0]  icache_resp_instr_16B_by_way,

    // icache resp feedback
    output logic                            icache_resp_hit_valid,
    output logic                            icache_resp_hit_way,
    output logic                            icache_resp_miss_valid,
    output logic [ICACHE_TAG_WIDTH-1:0]     icache_resp_miss_tag,

    // write buffer WB data to PRF
    input logic                         wr_buf_WB_valid,
    input logic [31:0]                  wr_buf_WB_data,
    input logic [LOG_PR_COUNT-1:0]      wr_buf_WB_PR,

    // write buffer WB feedback from PRF
    output logic                        wr_buf_WB_ready,

    // hardware failure
    output logic unrecoverable_fault
);
    // Modules:
        // Front End
            // fetch_unit
            // istream
            // decode_unit
        // Central
            // prf
            // rob
        // Back End
            // alu_reg_mdu
                // alu_reg_mdu_dq
                // alu_reg_mdu_iq_single
                // alu_reg_pipeline_fast
                // mdu_pipeline
            // alu_imm
                // alu_imm_dq
                // alu_imm_iq
                // alu_imm_pipeline_fast
            // bru
                // bru_dq
                // bru_iq
                // bru_pipeline_fast
            // lsu
                // ldu
                    // ldu_dq
                    // ldu_iq
                    // ldu_addr_pipeline
                    // 2x ldu_launch_pipeline
                    // ldu_cq
                    // ldu_mq
                // stamofu
                    // stamofu_dq
                    // stamofu_iq
                    // stamofu_aq
                    // stamofu_addr_pipeline
                    // 2x stamofu_lq
                    // 2x stamofu_launch_pipeline
                    // stamofu_cq
                    // stamofu_mq
                // ssu
            // sysu
                // sysu_dq
                // sysu_pipeline
                // csrf

    // ----------------------------------------------------------------
    // Signals:

    // output to istream
    logic                                   istream_valid_SENQ;
    logic [7:0]                             istream_valid_by_fetch_2B_SENQ;
    logic [7:0]                             istream_one_hot_redirect_by_fetch_2B_SENQ;
    logic [7:0][15:0]                       istream_instr_2B_by_fetch_2B_SENQ;
    logic [7:0][BTB_PRED_INFO_WIDTH-1:0]    istream_pred_info_by_fetch_2B_SENQ;
    logic [7:0]                             istream_pred_lru_by_fetch_2B_SENQ;
    logic [7:0][MDPT_INFO_WIDTH-1:0]        istream_mdp_info_by_fetch_2B_SENQ;
    logic [31:0]                            istream_after_PC_SENQ;
    logic [LH_LENGTH-1:0]                   istream_LH_SENQ;
    logic [GH_LENGTH-1:0]                   istream_GH_SENQ;
    logic [RAS_INDEX_WIDTH-1:0]             istream_ras_index_SENQ;
    logic                                   istream_page_fault_SENQ;
    logic                                   istream_access_fault_SENQ;

    // istream feedback
    logic istream_stall_SENQ;

    // restart from ROB
    logic                   rob_restart_valid;
    logic [31:0]            rob_restart_PC;
    logic [ASID_WIDTH-1:0]  rob_restart_ASID;
    logic [1:0]             rob_restart_exec_mode;
    logic                   rob_restart_virtual_mode;
    logic                   rob_restart_MXR;
    logic                   rob_restart_SUM;
    logic                   rob_restart_trap_sfence;
    logic                   rob_restart_trap_wfi;
    logic                   rob_restart_trap_sret;

    // decode unit control
    logic           decode_unit_restart_valid;
    logic [31:0]    decode_unit_restart_PC;

    logic           decode_unit_trigger_wait_for_restart;

    // branch update from decode unit
    logic                               decode_unit_branch_update_valid;
    logic                               decode_unit_branch_update_has_checkpoint;
    logic                               decode_unit_branch_update_is_mispredict;
    logic                               decode_unit_branch_update_is_taken;
    logic                               decode_unit_branch_update_is_complex;
    logic                               decode_unit_branch_update_use_upct;
    logic [BTB_PRED_INFO_WIDTH-1:0]     decode_unit_branch_update_intermediate_pred_info;
    logic                               decode_unit_branch_update_pred_lru;
    logic [31:0]                        decode_unit_branch_update_start_PC;
    logic [31:0]                        decode_unit_branch_update_target_PC;
    logic [LH_LENGTH-1:0]               decode_unit_branch_update_LH;
    logic [GH_LENGTH-1:0]               decode_unit_branch_update_GH;
    logic [RAS_INDEX_WIDTH-1:0]         decode_unit_branch_update_ras_index;

    // mdpt update
    logic                           mdpt_update_valid;
    logic [31:0]                    mdpt_update_start_full_PC;
    logic [ASID_WIDTH-1:0]          mdpt_update_ASID;
    logic [MDPT_INFO_WIDTH-1:0]     mdpt_update_mdp_info;

    // input from istream
    logic                                       istream_valid_SDEQ;
    logic [3:0]                                 istream_valid_by_way_SDEQ;
    logic [3:0]                                 istream_uncompressed_by_way_SDEQ;
    logic [3:0][1:0][15:0]                      istream_instr_2B_by_way_by_chunk_SDEQ;
    logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0]   istream_pred_info_by_way_by_chunk_SDEQ;
    logic [3:0][1:0]                            istream_pred_lru_by_way_by_chunk_SDEQ;
    logic [3:0][1:0][31:0]                      istream_pred_PC_by_way_by_chunk_SDEQ;
    logic [3:0][1:0]                            istream_page_fault_by_way_by_chunk_SDEQ;
    logic [3:0][1:0]                            istream_access_fault_by_way_by_chunk_SDEQ;
    logic [3:0][MDPT_INFO_WIDTH-1:0]            istream_mdp_info_by_way_SDEQ;
    logic [3:0][31:0]                           istream_PC_by_way_SDEQ;
    logic [3:0][LH_LENGTH-1:0]                  istream_LH_by_way_SDEQ;
    logic [3:0][GH_LENGTH-1:0]                  istream_GH_by_way_SDEQ;
    logic [3:0][RAS_INDEX_WIDTH-1:0]            istream_ras_index_by_way_SDEQ;

    // feedback to istream
    logic istream_stall_SDEQ;

    // op dispatch by way:

    // 4-way ROB entry
    logic dispatch_rob_enq_valid;
	logic dispatch_rob_enq_killed;
    logic dispatch_rob_enq_ready;

    // general instr info
    logic [3:0]                             dispatch_valid_by_way;
    logic [3:0]                             dispatch_uncompressed_by_way;
    logic [3:0][31:0]                       dispatch_PC_by_way;
    logic [3:0][31:0]                       dispatch_pred_PC_by_way;
    logic [3:0]                             dispatch_is_rename_by_way;
    logic [3:0][BTB_PRED_INFO_WIDTH-1:0]    dispatch_pred_info_by_way;
    logic [3:0][MDPT_INFO_WIDTH-1:0]        dispatch_mdp_info_by_way;
    logic [3:0][3:0]                        dispatch_op_by_way;
    logic [3:0][19:0]                       dispatch_imm20_by_way;

    // ordering
    logic [3:0]                             dispatch_mem_aq_by_way;
    logic [3:0]                             dispatch_io_aq_by_way;
    logic [3:0]                             dispatch_mem_rl_by_way;
    logic [3:0]                             dispatch_io_rl_by_way;

    // exception info
    logic                                   dispatch_is_page_fault;
    logic                                   dispatch_is_access_fault;
    logic                                   dispatch_is_illegal_instr;
	logic 							        dispatch_exception_present;
	logic [1:0]						        dispatch_exception_index;
    logic [31:0]                            dispatch_illegal_instr32;

	// checkpoint info
	logic								    dispatch_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0]	    dispatch_checkpoint_index;

    // instr IQ attempts
    logic [3:0]                             dispatch_attempt_alu_reg_mdu_dq_by_way;
    logic [3:0]                             dispatch_attempt_alu_imm_dq_by_way;
    logic [3:0]                             dispatch_attempt_bru_dq_by_way;
	logic [3:0]					            dispatch_attempt_ldu_dq_by_way;
    logic [3:0]                             dispatch_attempt_stamofu_dq_by_way;
    logic [3:0]                             dispatch_attempt_sysu_dq_by_way;

    // instr FU valids
    logic [3:0]                             dispatch_valid_alu_reg_by_way;
    logic [3:0]                             dispatch_valid_mdu_by_way;
    logic [3:0]                             dispatch_valid_alu_imm_by_way;
    logic [3:0]                             dispatch_valid_bru_by_way;
    logic [3:0]                             dispatch_valid_ldu_by_way;
    logic [3:0]                             dispatch_valid_store_by_way;
    logic [3:0]                             dispatch_valid_amo_by_way;
    logic [3:0]                             dispatch_valid_fence_by_way;
    logic [3:0]                             dispatch_valid_sysu_by_way;

    // operand A
    logic [3:0][LOG_PR_COUNT-1:0]           dispatch_A_PR_by_way;
    logic [3:0]                             dispatch_A_ready_by_way;
	logic [3:0]						        dispatch_A_is_zero_by_way;
    logic [3:0]                             dispatch_A_unneeded_or_is_zero_by_way;
    logic [3:0]                             dispatch_A_is_ret_ra_by_way;

    // operand B
    logic [3:0][LOG_PR_COUNT-1:0]           dispatch_B_PR_by_way;
    logic [3:0]                             dispatch_B_ready_by_way;
	logic [3:0]						        dispatch_B_is_zero_by_way;
    logic [3:0]                             dispatch_B_unneeded_or_is_zero_by_way;

    // dest operand
    logic [3:0][4:0]            		    dispatch_dest_AR_by_way;
    logic [3:0][LOG_PR_COUNT-1:0]           dispatch_dest_old_PR_by_way;
    logic [3:0][LOG_PR_COUNT-1:0]           dispatch_dest_new_PR_by_way;
    logic [3:0]                             dispatch_dest_is_link_ra;

    // instr IQ acks
    logic [3:0] dispatch_ack_alu_reg_mdu_dq_by_way;
    logic [3:0] dispatch_ack_alu_imm_dq_by_way;
    logic [3:0] dispatch_ack_bru_dq_by_way;
    logic [3:0] dispatch_ack_ldu_dq_by_way;
    logic [3:0] dispatch_ack_stamofu_dq_by_way;
    logic [3:0] dispatch_ack_sysu_dq_by_way;

    // writeback bus by bank
    logic [PRF_BANK_COUNT-1:0]                                          WB_bus_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     WB_bus_upper_PR_by_bank;

    // ROB kill
    logic                           rob_kill_valid;
    logic [LOG_ROB_ENTRIES-1:0]     rob_kill_abs_head_index;
    logic [LOG_ROB_ENTRIES-1:0]     rob_kill_rel_kill_younger_index;

    // branch update from ROB
    logic                               rob_branch_update_valid;
    logic                               rob_branch_update_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0]  rob_branch_update_checkpoint_index;
    logic                               rob_branch_update_is_mispredict;
    logic                               rob_branch_update_is_taken;
    logic                               rob_branch_update_use_upct;
    logic [BTB_PRED_INFO_WIDTH-1:0]     rob_branch_update_intermediate_pred_info;
    logic                               rob_branch_update_pred_lru;
    logic [31:0]                        rob_branch_update_start_PC;
    logic [31:0]                        rob_branch_update_target_PC;

    // ROB control of rename
    logic                             	rob_controlling_rename;

    logic                               rob_checkpoint_map_table_restore_valid;
    logic [CHECKPOINT_INDEX_WIDTH-1:0]  rob_checkpoint_map_table_restore_index;

    logic                               rob_checkpoint_clear_valid;
    logic [CHECKPOINT_INDEX_WIDTH-1:0]  rob_checkpoint_clear_index;

    logic [3:0]                       	rob_map_table_write_valid_by_port;
    logic [3:0][LOG_AR_COUNT-1:0]     	rob_map_table_write_AR_by_port;
    logic [3:0][LOG_PR_COUNT-1:0]     	rob_map_table_write_PR_by_port;

	// ROB physical register freeing
	logic [3:0]                     rob_PR_free_req_valid_by_bank;
	logic [3:0][LOG_PR_COUNT-1:0]   rob_PR_free_req_PR_by_bank;
	logic [3:0]						rob_PR_free_resp_ack_by_bank;

    // read req info by read requester
    logic [PRF_RR_COUNT-1:0]                    prf_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]  prf_read_req_PR_by_rr;

    logic ldu_PRF_req_A_valid;
    logic alu_reg_mdu_PRF_req_A_valid;
    logic alu_reg_mdu_PRF_req_B_valid;
    logic alu_imm_PRF_req_A_valid;
    logic bru_PRF_req_A_valid;
    logic bru_PRF_req_B_valid;
    logic stamofu_PRF_req_A_valid;
    logic stamofu_PRF_req_B_valid;
    logic sysu_PRF_req_A_valid;

    logic ldu_PRF_req_A_PR;
    logic alu_reg_mdu_PRF_req_A_PR;
    logic alu_reg_mdu_PRF_req_B_PR;
    logic alu_imm_PRF_req_A_PR;
    logic bru_PRF_req_A_PR;
    logic bru_PRF_req_B_PR;
    logic stamofu_PRF_req_A_PR;
    logic stamofu_PRF_req_B_PR;
    logic sysu_PRF_req_A_PR;

    // read resp info by read requestor
    logic [PRF_RR_COUNT-1:0]    prf_read_resp_ack_by_rr;
    logic [PRF_RR_COUNT-1:0]    prf_read_resp_port_by_rr;

    // read data by bank
    logic [PRF_BANK_COUNT-1:0][1:0][31:0] prf_read_data_by_bank_by_port;

    // writeback info by write requestor
    logic [PRF_WR_COUNT-1:0]                        WB_valid_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  WB_data_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      WB_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   WB_ROB_index_by_wr;

    logic stamofu_WB_valid;
    logic ldu_bank0_WB_valid;
    logic ldu_bank1_WB_valid;
    logic alu_reg_WB_valid;
    logic mdu_WB_valid;
    logic alu_imm_WB_valid;
    logic bru_WB_valid;
    logic sysu_WB_valid;

    // writeback feedback by write requestor
    logic [PRF_WR_COUNT-1:0] WB_ready_by_wr;

    // forward data by bank
    logic [PRF_BANK_COUNT-1:0][31:0] prf_forward_data_bus_by_bank;

    // complete bus by bank
    logic [PRF_BANK_COUNT-1:0]                          prf_complete_bus_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]     prf_complete_bus_ROB_index_by_bank;

    // ----------------------------------------------------------------
    // Front End Modules:

    // fetch unit
    fetch_unit #(
        .INIT_PC(INIT_PC),
        .INIT_ASID(INIT_ASID),
        .INIT_EXEC_MODE(INIT_EXEC_MODE),
        .INIT_VIRTUAL_MODE(INIT_VIRTUAL_MODE),
        .FETCH_UNIT_WAIT_FOR_RESTART_STATE(FETCH_UNIT_WAIT_FOR_RESTART_STATE) 
    ) FETCH_UNIT (
        // seq
        .CLK(CLK),
        .nRST(nRST),

	    // itlb req
		.itlb_req_valid(itlb_req_valid),
		.itlb_req_exec_mode(itlb_req_exec_mode),
		.itlb_req_virtual_mode(itlb_req_virtual_mode),
		.itlb_req_VPN(itlb_req_VPN),
		.itlb_req_ASID(itlb_req_ASID),

	    // itlb resp
		.itlb_resp_valid(itlb_resp_valid),
		.itlb_resp_PPN(itlb_resp_PPN),
		.itlb_resp_page_fault(itlb_resp_page_fault),
		.itlb_resp_access_fault(itlb_resp_access_fault),

	    // icache req
		.icache_req_valid(icache_req_valid),
		.icache_req_block_offset(icache_req_block_offset),
		.icache_req_index(icache_req_index),

	    // icache resp
		.icache_resp_valid_by_way(icache_resp_valid_by_way),
		.icache_resp_tag_by_way(icache_resp_tag_by_way),
		.icache_resp_instr_16B_by_way(icache_resp_instr_16B_by_way),

	    // icache resp feedback
		.icache_resp_hit_valid(icache_resp_hit_valid),
		.icache_resp_hit_way(icache_resp_hit_way),
		.icache_resp_miss_valid(icache_resp_miss_valid),
		.icache_resp_miss_tag(icache_resp_miss_tag),

	    // output to istream
		.istream_valid_SENQ(istream_valid_SENQ),
		.istream_valid_by_fetch_2B_SENQ(istream_valid_by_fetch_2B_SENQ),
		.istream_one_hot_redirect_by_fetch_2B_SENQ(istream_one_hot_redirect_by_fetch_2B_SENQ),
		.istream_instr_2B_by_fetch_2B_SENQ(istream_instr_2B_by_fetch_2B_SENQ),
		.istream_pred_info_by_fetch_2B_SENQ(istream_pred_info_by_fetch_2B_SENQ),
		.istream_pred_lru_by_fetch_2B_SENQ(istream_pred_lru_by_fetch_2B_SENQ),
		.istream_mdp_info_by_fetch_2B_SENQ(istream_mdp_info_by_fetch_2B_SENQ),
		.istream_after_PC_SENQ(istream_after_PC_SENQ),
		.istream_LH_SENQ(istream_LH_SENQ),
		.istream_GH_SENQ(istream_GH_SENQ),
		.istream_ras_index_SENQ(istream_ras_index_SENQ),
		.istream_page_fault_SENQ(istream_page_fault_SENQ),
		.istream_access_fault_SENQ(istream_access_fault_SENQ),

	    // istream feedback
		.istream_stall_SENQ(istream_stall_SENQ),

	    // fetch + decode restart from ROB
		.rob_restart_valid(rob_restart_valid),
		.rob_restart_PC(rob_restart_PC),
		.rob_restart_ASID(rob_restart_ASID),
		.rob_restart_exec_mode(rob_restart_exec_mode),
		.rob_restart_virtual_mode(rob_restart_virtual_mode),

	    // decode unit control
		.decode_unit_restart_valid(decode_unit_restart_valid),
		.decode_unit_restart_PC(decode_unit_restart_PC),
		.decode_unit_trigger_wait_for_restart(decode_unit_trigger_wait_for_restart),

	    // branch update from decode unit
		.decode_unit_branch_update_valid(decode_unit_branch_update_valid),
		.decode_unit_branch_update_has_checkpoint(decode_unit_branch_update_has_checkpoint),
		.decode_unit_branch_update_is_mispredict(decode_unit_branch_update_is_mispredict),
		.decode_unit_branch_update_is_taken(decode_unit_branch_update_is_taken),
		.decode_unit_branch_update_is_complex(decode_unit_branch_update_is_complex),
		.decode_unit_branch_update_use_upct(decode_unit_branch_update_use_upct),
		.decode_unit_branch_update_intermediate_pred_info(decode_unit_branch_update_intermediate_pred_info),
		.decode_unit_branch_update_pred_lru(decode_unit_branch_update_pred_lru),
		.decode_unit_branch_update_start_PC(decode_unit_branch_update_start_PC),
		.decode_unit_branch_update_target_PC(decode_unit_branch_update_target_PC),
		.decode_unit_branch_update_LH(decode_unit_branch_update_LH),
		.decode_unit_branch_update_GH(decode_unit_branch_update_GH),
		.decode_unit_branch_update_ras_index(decode_unit_branch_update_ras_index),

	    // mdpt update
		.mdpt_update_valid(mdpt_update_valid),
		.mdpt_update_start_full_PC(mdpt_update_start_full_PC),
		.mdpt_update_ASID(mdpt_update_ASID),
		.mdpt_update_mdp_info(mdpt_update_mdp_info)
    );

    // istream
	istream #(
		.ISTREAM_SETS(ISTREAM_SETS),
		.INIT_PC(INIT_PC)
	) ISTREAM (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // SENQ stage
		.valid_SENQ(istream_valid_SENQ),
		.valid_by_fetch_2B_SENQ(istream_valid_by_fetch_2B_SENQ),
		.one_hot_redirect_by_fetch_2B_SENQ(istream_one_hot_redirect_by_fetch_2B_SENQ),
		.instr_2B_by_fetch_2B_SENQ(istream_instr_2B_by_fetch_2B_SENQ),
		.pred_info_by_fetch_2B_SENQ(istream_pred_info_by_fetch_2B_SENQ),
		.pred_lru_by_fetch_2B_SENQ(istream_pred_lru_by_fetch_2B_SENQ),
		.mdp_info_by_fetch_2B_SENQ(istream_mdp_info_by_fetch_2B_SENQ),
		.after_PC_SENQ(istream_after_PC_SENQ),
		.LH_SENQ(istream_LH_SENQ),
		.GH_SENQ(istream_GH_SENQ),
		.ras_index_SENQ(istream_ras_index_SENQ),
		.page_fault_SENQ(istream_page_fault_SENQ),
		.access_fault_SENQ(istream_access_fault_SENQ),

	    // SENQ feedback
		.stall_SENQ(istream_stall_SENQ),

	    // SDEQ stage
		.valid_SDEQ(istream_valid_SDEQ),
		.valid_by_way_SDEQ(istream_valid_by_way_SDEQ),
		.uncompressed_by_way_SDEQ(istream_uncompressed_by_way_SDEQ),
		.instr_2B_by_way_by_chunk_SDEQ(istream_instr_2B_by_way_by_chunk_SDEQ),
		.pred_info_by_way_by_chunk_SDEQ(istream_pred_info_by_way_by_chunk_SDEQ),
		.pred_lru_by_way_by_chunk_SDEQ(istream_pred_lru_by_way_by_chunk_SDEQ),
		// .redirect_by_way_by_chunk_SDEQ(), // unused
		.pred_PC_by_way_by_chunk_SDEQ(istream_pred_PC_by_way_by_chunk_SDEQ),
		.page_fault_by_way_by_chunk_SDEQ(istream_page_fault_by_way_by_chunk_SDEQ),
		.access_fault_by_way_by_chunk_SDEQ(istream_access_fault_by_way_by_chunk_SDEQ),
		.mdp_info_by_way_SDEQ(istream_mdp_info_by_way_SDEQ),
		.PC_by_way_SDEQ(istream_PC_by_way_SDEQ),
		.LH_by_way_SDEQ(istream_LH_by_way_SDEQ),
		.GH_by_way_SDEQ(istream_GH_by_way_SDEQ),
		.ras_index_by_way_SDEQ(istream_ras_index_by_way_SDEQ),

	    // SDEQ feedback
		.stall_SDEQ(istream_stall_SDEQ),

	    // control
		.restart(rob_restart_valid),
		.restart_PC(rob_restart_PC)
	);

    // decode_unit
    decode_unit #(
		.INIT_EXEC_MODE(INIT_EXEC_MODE),
		.INIT_TRAP_SFENCE(INIT_TRAP_SFENCE),
		.INIT_TRAP_WFI(INIT_TRAP_WFI),
		.INIT_TRAP_SRET(INIT_TRAP_SRET)
	) DECODE_UNIT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // input from istream
		.istream_valid_SDEQ(istream_valid_SDEQ),
		.istream_valid_by_way_SDEQ(istream_valid_by_way_SDEQ),
		.istream_uncompressed_by_way_SDEQ(istream_uncompressed_by_way_SDEQ),
		.istream_instr_2B_by_way_by_chunk_SDEQ(istream_instr_2B_by_way_by_chunk_SDEQ),
		.istream_pred_info_by_way_by_chunk_SDEQ(istream_pred_info_by_way_by_chunk_SDEQ),
		.istream_pred_lru_by_way_by_chunk_SDEQ(istream_pred_lru_by_way_by_chunk_SDEQ),
		.istream_pred_PC_by_way_by_chunk_SDEQ(istream_pred_PC_by_way_by_chunk_SDEQ),
		.istream_page_fault_by_way_by_chunk_SDEQ(istream_page_fault_by_way_by_chunk_SDEQ),
		.istream_access_fault_by_way_by_chunk_SDEQ(istream_access_fault_by_way_by_chunk_SDEQ),
		.istream_mdp_info_by_way_SDEQ(istream_mdp_info_by_way_SDEQ),
		.istream_PC_by_way_SDEQ(istream_PC_by_way_SDEQ),
		.istream_LH_by_way_SDEQ(istream_LH_by_way_SDEQ),
		.istream_GH_by_way_SDEQ(istream_GH_by_way_SDEQ),
		.istream_ras_index_by_way_SDEQ(istream_ras_index_by_way_SDEQ),

	    // feedback to istream
		.istream_stall_SDEQ(istream_stall_SDEQ),

	    // op dispatch by way:

	    // 4-way ROB entry
		.dispatch_rob_enq_valid(dispatch_rob_enq_valid),
		.dispatch_rob_enq_killed(dispatch_rob_enq_killed),
		.dispatch_rob_enq_ready(dispatch_rob_enq_ready),

	    // general instr info
		.dispatch_valid_by_way(dispatch_valid_by_way),
		.dispatch_uncompressed_by_way(dispatch_uncompressed_by_way),
		.dispatch_PC_by_way(dispatch_PC_by_way),
		.dispatch_pred_PC_by_way(dispatch_pred_PC_by_way),
		.dispatch_is_rename_by_way(dispatch_is_rename_by_way),
		.dispatch_pred_info_by_way(dispatch_pred_info_by_way),
		.dispatch_mdp_info_by_way(dispatch_mdp_info_by_way),
		.dispatch_op_by_way(dispatch_op_by_way),
		.dispatch_imm20_by_way(dispatch_imm20_by_way),

	    // ordering
		.dispatch_mem_aq_by_way(dispatch_mem_aq_by_way),
		.dispatch_io_aq_by_way(dispatch_io_aq_by_way),
		.dispatch_mem_rl_by_way(dispatch_mem_rl_by_way),
		.dispatch_io_rl_by_way(dispatch_io_rl_by_way),

	    // exception info
		.dispatch_is_page_fault(dispatch_is_page_fault),
		.dispatch_is_access_fault(dispatch_is_access_fault),
		.dispatch_is_illegal_instr(dispatch_is_illegal_instr),
		.dispatch_exception_present(dispatch_exception_present),
		.dispatch_exception_index(dispatch_exception_index),
		.dispatch_illegal_instr32(dispatch_illegal_instr32),

		// checkpoint info
		.dispatch_has_checkpoint(dispatch_has_checkpoint),
		.dispatch_checkpoint_index(dispatch_checkpoint_index),

	    // instr IQ attempts
		.dispatch_attempt_alu_reg_mdu_dq_by_way(dispatch_attempt_alu_reg_mdu_dq_by_way),
		.dispatch_attempt_alu_imm_dq_by_way(dispatch_attempt_alu_imm_dq_by_way),
		.dispatch_attempt_bru_dq_by_way(dispatch_attempt_bru_dq_by_way),
		.dispatch_attempt_ldu_dq_by_way(dispatch_attempt_ldu_dq_by_way),
		.dispatch_attempt_stamofu_dq_by_way(dispatch_attempt_stamofu_dq_by_way),
		.dispatch_attempt_sysu_dq_by_way(dispatch_attempt_sysu_dq_by_way),

	    // instr FU valids
		.dispatch_valid_alu_reg_by_way(dispatch_valid_alu_reg_by_way),
		.dispatch_valid_mdu_by_way(dispatch_valid_mdu_by_way),
		.dispatch_valid_alu_imm_by_way(dispatch_valid_alu_imm_by_way),
		.dispatch_valid_bru_by_way(dispatch_valid_bru_by_way),
		.dispatch_valid_ldu_by_way(dispatch_valid_ldu_by_way),
		.dispatch_valid_store_by_way(dispatch_valid_store_by_way),
		.dispatch_valid_amo_by_way(dispatch_valid_amo_by_way),
		.dispatch_valid_fence_by_way(dispatch_valid_fence_by_way),
		.dispatch_valid_sysu_by_way(dispatch_valid_sysu_by_way),

	    // operand A
		.dispatch_A_PR_by_way(dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(dispatch_A_ready_by_way),
		.dispatch_A_is_zero_by_way(dispatch_A_is_zero_by_way),
		.dispatch_A_unneeded_or_is_zero_by_way(dispatch_A_unneeded_or_is_zero_by_way),
		.dispatch_A_is_ret_ra_by_way(dispatch_A_is_ret_ra_by_way),

	    // operand B
		.dispatch_B_PR_by_way(dispatch_B_PR_by_way),
		.dispatch_B_ready_by_way(dispatch_B_ready_by_way),
		.dispatch_B_is_zero_by_way(dispatch_B_is_zero_by_way),
		.dispatch_B_unneeded_or_is_zero_by_way(dispatch_B_unneeded_or_is_zero_by_way),

	    // dest operand
		.dispatch_dest_AR_by_way(dispatch_dest_AR_by_way),
		.dispatch_dest_old_PR_by_way(dispatch_dest_old_PR_by_way),
		.dispatch_dest_new_PR_by_way(dispatch_dest_new_PR_by_way),
		.dispatch_dest_is_link_ra(dispatch_dest_is_link_ra),

	    // instr IQ acks
		.dispatch_ack_alu_reg_mdu_dq_by_way(dispatch_ack_alu_reg_mdu_dq_by_way),
		.dispatch_ack_alu_imm_dq_by_way(dispatch_ack_alu_imm_dq_by_way),
		.dispatch_ack_bru_dq_by_way(dispatch_ack_bru_dq_by_way),
		.dispatch_ack_ldu_dq_by_way(dispatch_ack_ldu_dq_by_way),
		.dispatch_ack_stamofu_dq_by_way(dispatch_ack_stamofu_dq_by_way),
		.dispatch_ack_sysu_dq_by_way(dispatch_ack_sysu_dq_by_way),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(WB_bus_upper_PR_by_bank),

	    // fetch + decode restart from ROB
		.rob_restart_valid(rob_restart_valid),
		.rob_restart_exec_mode(rob_restart_exec_mode),
		.rob_restart_trap_sfence(rob_restart_trap_sfence),
		.rob_restart_trap_wfi(rob_restart_trap_wfi),
		.rob_restart_trap_sret(rob_restart_trap_sret),

		// kill from ROB
		.rob_kill_valid(rob_kill_valid),

	    // branch update from ROB
		.rob_branch_update_valid(rob_branch_update_valid),
		.rob_branch_update_has_checkpoint(rob_branch_update_has_checkpoint),
		.rob_branch_update_checkpoint_index(rob_branch_update_checkpoint_index),
		.rob_branch_update_is_mispredict(rob_branch_update_is_mispredict),
		.rob_branch_update_is_taken(rob_branch_update_is_taken),
		.rob_branch_update_use_upct(rob_branch_update_use_upct),
		.rob_branch_update_intermediate_pred_info(rob_branch_update_intermediate_pred_info),
		.rob_branch_update_pred_lru(rob_branch_update_pred_lru),
		.rob_branch_update_start_PC(rob_branch_update_start_PC),
		.rob_branch_update_target_PC(rob_branch_update_target_PC),

	    // ROB control of rename
		.rob_controlling_rename(rob_controlling_rename),

		.rob_checkpoint_map_table_restore_valid(rob_checkpoint_map_table_restore_valid),
		.rob_checkpoint_map_table_restore_index(rob_checkpoint_map_table_restore_index),

		.rob_checkpoint_clear_valid(rob_checkpoint_clear_valid),
		.rob_checkpoint_clear_index(rob_checkpoint_clear_index),

		.rob_map_table_write_valid_by_port(rob_map_table_write_valid_by_port),
		.rob_map_table_write_AR_by_port(rob_map_table_write_AR_by_port),
		.rob_map_table_write_PR_by_port(rob_map_table_write_PR_by_port),

		// ROB physical register freeing
		.rob_PR_free_req_valid_by_bank(rob_PR_free_req_valid_by_bank),
		.rob_PR_free_req_PR_by_bank(rob_PR_free_req_PR_by_bank),
		.rob_PR_free_resp_ack_by_bank(rob_PR_free_resp_ack_by_bank),

	    // branch update to fetch unit
		.decode_unit_branch_update_valid(decode_unit_branch_update_valid),
		.decode_unit_branch_update_has_checkpoint(decode_unit_branch_update_has_checkpoint),
		.decode_unit_branch_update_is_mispredict(decode_unit_branch_update_is_mispredict),
		.decode_unit_branch_update_is_taken(decode_unit_branch_update_is_taken),
		.decode_unit_branch_update_is_complex(decode_unit_branch_update_is_complex),
		.decode_unit_branch_update_use_upct(decode_unit_branch_update_use_upct),
		.decode_unit_branch_update_intermediate_pred_info(decode_unit_branch_update_intermediate_pred_info),
		.decode_unit_branch_update_pred_lru(decode_unit_branch_update_pred_lru),
		.decode_unit_branch_update_start_PC(decode_unit_branch_update_start_PC),
		.decode_unit_branch_update_target_PC(decode_unit_branch_update_target_PC),
		.decode_unit_branch_update_LH(decode_unit_branch_update_LH),
		.decode_unit_branch_update_GH(decode_unit_branch_update_GH),
		.decode_unit_branch_update_ras_index(decode_unit_branch_update_ras_index),

	    // decode unit control
		.decode_unit_restart_valid(decode_unit_restart_valid),
		.decode_unit_restart_PC(decode_unit_restart_PC),

		.decode_unit_trigger_wait_for_restart(decode_unit_trigger_wait_for_restart),

		// hardware failure
		.unrecoverable_fault(unrecoverable_fault)
	);

    // ----------------------------------------------------------------
    // Central Modules:

    // prf
    always_comb begin

        // read priority:
            // LDU A
            // ALU Reg-Reg / MDU A
            // ALU Reg-Reg / MDU B
            // ALU Reg-Imm A
            // BRU A
            // BRU B
            // STAMOFU A
            // STAMOFU B
            // SYSU A
        prf_read_req_valid_by_rr = {
            sysu_PRF_req_A_valid,
            stamofu_PRF_req_B_valid,
            stamofu_PRF_req_A_valid,
            bru_PRF_req_B_valid,
            bru_PRF_req_A_valid,
            alu_imm_PRF_req_A_valid,
            alu_reg_mdu_PRF_req_B_valid,
            alu_reg_mdu_PRF_req_A_valid,
            ldu_PRF_req_A_valid
        };
        prf_read_req_PR_by_rr = {
            sysu_PRF_req_A_PR,
            stamofu_PRF_req_B_PR,
            stamofu_PRF_req_A_PR,
            bru_PRF_req_B_PR,
            bru_PRF_req_A_PR,
            alu_imm_PRF_req_A_PR,
            alu_reg_mdu_PRF_req_B_PR,
            alu_reg_mdu_PRF_req_A_PR,
            ldu_PRF_req_A_PR
        };
        
        // write priority:
            // STAMOFU
            // LDU bank 0
            // LDU bank 1
            // ALU Reg-Reg
            // MDU
            // ALU Reg-Imm
            // BRU
            // SYSU
        WB_valid_by_wr = {

        };
        WB_data_by_wr = {

        };
        WB_PR_by_wr = {

        };
        WB_ROB_index_by_wr = {

        };

        stamofu_WB_ready = WB_ready_by_wr[0];

        // sysu PRF req hardwired for now
        sysu_PRF_req_A_valid = 1'b0;
        sysu_PRF_req_A_PR = 7'h00;
    end
    prf #(
        .PR_COUNT(PR_COUNT),
        .PRF_BANK_COUNT(PRF_BANK_COUNT),
        .PRF_RR_COUNT(9),
        .PRF_WR_COUNT(7),
        .USE_BRAM(0)
    ) PRF (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // reg read req by read requester
		.read_req_valid_by_rr(read_req_valid_by_rr),
		.read_req_PR_by_rr(read_req_PR_by_rr),

	    // reg read info by read requestor
		.read_resp_ack_by_rr(read_resp_ack_by_rr),
		.read_resp_port_by_rr(read_resp_port_by_rr),

	    // reg read data by bank
		.read_data_by_bank_by_port(read_data_by_bank_by_port),

	    // writeback data by write requestor
		.WB_valid_by_wr(WB_valid_by_wr),
		.WB_data_by_wr(WB_data_by_wr),
		.WB_PR_by_wr(WB_PR_by_wr),
		.WB_ROB_index_by_wr(WB_ROB_index_by_wr),

	    // writeback backpressure by write requestor
		.WB_ready_by_wr(WB_ready_by_wr),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(WB_bus_upper_PR_by_bank),

	    // forward data from PRF
		.forward_data_bus_by_bank(forward_data_bus_by_bank),

		// complete bus by bank
		.complete_bus_valid_by_bank(complete_bus_valid_by_bank),
		.complete_bus_ROB_index_by_bank(complete_bus_ROB_index_by_bank)
    );

    // rob

    // ----------------------------------------------------------------
    // Backend Modules:

    // ----------------------------------------------------------------
    // alu_reg_mdu:

    // alu_reg_mdu_dq
    // alu_reg_mdu_iq_single
    // alu_reg_pipeline_fast
    // mdu_pipeline

    // ----------------------------------------------------------------
    // alu_imm:

    // alu_imm_dq
    // alu_imm_iq
    // alu_imm_pipeline_fast

    // ----------------------------------------------------------------
    // bru:

    // bru_dq
    // bru_iq
    // bru_pipeline_fast

    // ----------------------------------------------------------------
    // lsu:

    // ----------------------------------------------------------------
    // ldu:

    // ldu_dq
    // ldu_iq
    // ldu_addr_pipeline
    // ldu_launch_pipeline bank 0
    // ldu_launch_pipeline bank 1
    // ldu_cq
    // ldu_mq

    // ----------------------------------------------------------------
    // stamofu:

    // stamofu_dq
    // stamofu_iq
    // stamofu_aq
    // stamofu_addr_pipeline
    // stamofu_lq bank 0
    // stamofu_lq bank 1
    // stamofu_launch_pipeline bank 0
    // stamofu_launch_pipeline bank 1
    // stamofu_cq
    // stamofu_mq

    // ssu

    // ----------------------------------------------------------------
    // sysu:
    
    // sysu_dq
    // sysu_pipeline
    // csrf


endmodule