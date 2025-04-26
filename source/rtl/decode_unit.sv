/*
    Filename: decode_unit.sv
    Author: zlagpacan
    Description: RTL for Decode Unit
    Spec: LOROF/spec/design/decode_unit.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module decode_unit #(
    parameter INIT_EXEC_MODE = M_MODE
) (

    // seq
    input logic CLK,
    input logic nRST,

    // input from istream
    input logic                                    		istream_valid_SDEQ,
    input logic [3:0]                              		istream_valid_by_way_SDEQ,
    input logic [3:0]                              		istream_uncompressed_by_way_SDEQ,
    input logic [3:0][1:0][15:0]                   		istream_instr_2B_by_way_by_chunk_SDEQ,
    input logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0]		istream_pred_info_by_way_by_chunk_SDEQ,
    input logic [3:0][1:0]                         		istream_pred_lru_by_way_by_chunk_SDEQ,
    input logic [3:0][1:0]                         		istream_redirect_by_way_by_chunk_SDEQ,
    input logic [3:0][1:0][31:0]                   		istream_pred_PC_by_way_by_chunk_SDEQ,
    input logic [3:0][1:0]                         		istream_page_fault_by_way_by_chunk_SDEQ,
    input logic [3:0][1:0]                         		istream_access_fault_by_way_by_chunk_SDEQ,
    input logic [3:0][MDPT_INFO_WIDTH-1:0]         		istream_mdp_info_by_way_SDEQ,
    input logic [3:0][31:0]                        		istream_PC_by_way_SDEQ,
    input logic [3:0][LH_LENGTH-1:0]               		istream_LH_by_way_SDEQ,
    input logic [3:0][GH_LENGTH-1:0]               		istream_GH_by_way_SDEQ,
    input logic [3:0][RAS_INDEX_WIDTH-1:0]         		istream_ras_index_by_way_SDEQ,

    // feedback to istream
    output logic istream_stall_SDEQ,

    // op dispatch by way:

    // 4-way ROB entry valid
    output logic                                  	dispatch_rob_valid,

    // general instr info
    output logic [3:0]                              dispatch_valid_by_way,
    output logic [3:0]                              dispatch_uncompressed_by_way,
    output logic [31:0]                             dispatch_PC_by_way,
    output logic [3:0]                              dispatch_is_rename_by_way,
    output logic [3:0][BTB_PRED_INFO_WIDTH-1:0]		dispatch_pred_info_by_way,
    output logic [3:0][MDPT_INFO_WIDTH-1:0]         dispatch_mdp_info_by_way,
    output logic [3:0][3:0]                         dispatch_op_by_way,
    output logic [19:0]                             dispatch_imm20_by_way,

    // ordering
    output logic [3:0]                              dispatch_mem_aq_by_way,
    output logic [3:0]                              dispatch_io_aq_by_way,
    output logic [3:0]                              dispatch_mem_rl_by_way,
    output logic [3:0]                              dispatch_io_rl_by_way,

    // instr fetch + decode exceptions
    output logic [3:0]                              dispatch_page_fault_by_way,
    output logic [3:0]                              dispatch_access_fault_by_way,
    output logic [3:0]                              dispatch_illegal_instr_by_way,
    output logic [31:0]                             dispatch_excepting_illegal_instr,

    // instr IQ attempts
    output logic [3:0]                              dispatch_attempt_alu_reg_mdu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_alu_imm_ldu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_bru_iq_by_way,
    output logic [3:0]                              dispatch_attempt_stamofu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_sys_iq_by_way,

    // instr FU valids
    output logic [3:0]                              dispatch_valid_alu_reg_by_way,
    output logic [3:0]                              dispatch_valid_mdu_by_way,
    output logic [3:0]                              dispatch_valid_alu_imm_by_way,
    output logic [3:0]                              dispatch_valid_ldu_by_way,
    output logic [3:0]                              dispatch_valid_bru_by_way,
    output logic [3:0]                              dispatch_valid_store_by_way,
    output logic [3:0]                              dispatch_valid_amo_by_way,
    output logic [3:0]                              dispatch_valid_fence_by_way,
    output logic [3:0]                              dispatch_valid_sys_by_way,

    // operand A
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_A_PR_by_way,
    output logic [3:0]                              dispatch_A_ready_by_way,
    output logic [3:0]                              dispatch_A_unneeded_or_is_zero_by_way,
    output logic [3:0]                              dispatch_A_is_ret_ra_by_way,

    // operand B
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_B_PR_by_way,
    output logic [3:0]                              dispatch_B_ready_by_way,
    output logic [3:0]                              dispatch_B_unneeded_or_is_zero_by_way,

    // dest operand
    output logic [3:0][LOG_AR_COUNT-1:0]            dispatch_dest_AR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_old_PR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_new_PR_by_way,
    output logic [3:0]                              dispatch_dest_is_zero_by_way,
    output logic [3:0]                              dispatch_dest_is_link_ra,

    // 4-way ROB entry open
    input logic dispatch_rob_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // instr IQ acks
    input logic [3:0]   dispatch_ack_alu_reg_mdu_iq_by_way,
    input logic [3:0]   dispatch_ack_alu_imm_iq_by_way,
    input logic [3:0]   dispatch_ack_ldu_iq_by_way,
    input logic [3:0]   dispatch_ack_bru_iq_by_way,
    input logic [3:0]   dispatch_ack_stamofu_iq_by_way,
    input logic [3:0]   dispatch_ack_sys_iq_by_way,

    // fetch + decode restart from ROB
    input logic       	rob_restart_valid,
    input logic [1:0] 	rob_restart_exec_mode,
    input logic      	rob_restart_trap_sfence,
    input logic      	rob_restart_trap_wfi,
    input logic      	rob_restart_trap_sret,

    // decode unit control
    output logic       		decode_unit_restart_valid,
    output logic [31:0]		decode_unit_restart_PC,
    output logic       		decode_unit_trigger_wait_for_restart,

    // branch update to fetch unit
    output logic                          	decode_unit_branch_update_valid,
    output logic                          	decode_unit_branch_update_has_checkpoint,
    output logic                          	decode_unit_branch_update_is_mispredict,
    output logic                          	decode_unit_branch_update_is_taken,
    output logic                          	decode_unit_branch_update_is_complex,
    output logic                          	decode_unit_branch_update_use_upct,
    output logic [BTB_PRED_INFO_WIDTH-1:0]	decode_unit_branch_update_intermediate_pred_info,
    output logic                          	decode_unit_branch_update_pred_lru,
    output logic [31:0]                   	decode_unit_branch_update_start_PC,
    output logic [31:0]                   	decode_unit_branch_update_target_PC,
    output logic [LH_LENGTH-1:0]          	decode_unit_branch_update_LH,
    output logic [GH_LENGTH-1:0]          	decode_unit_branch_update_GH,
    output logic [RAS_INDEX_WIDTH-1:0]    	decode_unit_branch_update_ras_index
);

	// need to send decode_unit restart to fetch_unit AFTER decode_unit update has finished
    // don't want another mispred

endmodule