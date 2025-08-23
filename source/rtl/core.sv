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
    parameter INIT_TVEC_BASE_PC = 32'h0000F000,
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
            // lsq
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
                // sysu
                // csrf

    // ----------------------------------------------------------------
    // Signals:

    // output to istream
    logic                                   istream_valid_SENQ;
    logic [7:0]                             istream_valid_by_fetch_2B_SENQ;
    logic [7:0]                             istream_one_hot_redirect_by_fetch_2B_SENQ;
    logic [7:0][15:0]                       istream_instr_2B_by_fetch_2B_SENQ;
    logic [7:0][BTB_PRED_INFO_WIDTH-1:0]       istream_pred_info_by_fetch_2B_SENQ;
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

    // fetch + decode restart from ROB
    logic                   rob_restart_valid;
    logic [31:0]            rob_restart_PC;
    logic [ASID_WIDTH-1:0]  rob_restart_ASID;
    logic [1:0]             rob_restart_exec_mode;
    logic                   rob_restart_virtual_mode;

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

    // ----------------------------------------------------------------
    // Modules:

    fetch_unit #(
        .INIT_PC(INIT_PC),
        .INIT_ASID(INIT_ASID),
        .INIT_EXEC_MODE(INIT_EXEC_MODE),
        .INIT_VIRTUAL_MODE(INIT_VIRTUAL_MODE),
        .INIT_WAIT_FOR_RESTART_STATE(INIT_WAIT_FOR_RESTART_STATE) 
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


endmodule