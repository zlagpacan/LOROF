/*
    Filename: decode_unit_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around decode_unit module. 
    Spec: LOROF/spec/design/decode_unit.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module decode_unit_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // input from istream
	input logic next_istream_valid_SDEQ,
	input logic [3:0] next_istream_valid_by_way_SDEQ,
	input logic [3:0] next_istream_uncompressed_by_way_SDEQ,
	input logic [3:0][1:0][15:0] next_istream_instr_2B_by_way_by_chunk_SDEQ,
	input logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0] next_istream_pred_info_by_way_by_chunk_SDEQ,
	input logic [3:0][1:0] next_istream_pred_lru_by_way_by_chunk_SDEQ,
    // input logic [3:0][1:0]                           	istream_redirect_by_way_by_chunk_SDEQ, // unused
	input logic [3:0][1:0][31:0] next_istream_pred_PC_by_way_by_chunk_SDEQ,
	input logic [3:0][1:0] next_istream_page_fault_by_way_by_chunk_SDEQ,
	input logic [3:0][1:0] next_istream_access_fault_by_way_by_chunk_SDEQ,
	input logic [3:0][MDPT_INFO_WIDTH-1:0] next_istream_mdp_info_by_way_SDEQ,
	input logic [3:0][31:0] next_istream_PC_by_way_SDEQ,
	input logic [3:0][LH_LENGTH-1:0] next_istream_LH_by_way_SDEQ,
	input logic [3:0][GH_LENGTH-1:0] next_istream_GH_by_way_SDEQ,
	input logic [3:0][RAS_INDEX_WIDTH-1:0] next_istream_ras_index_by_way_SDEQ,

    // feedback to istream
	output logic last_istream_stall_SDEQ,

    // op dispatch by way:

    // 4-way ROB entry
	output logic last_dispatch_rob_enqueue_valid,
	input logic next_dispatch_rob_enqueue_ready,

    // general instr info
	output logic [3:0] last_dispatch_valid_by_way,
	output logic [3:0] last_dispatch_uncompressed_by_way,
	output logic [3:0][31:0] last_dispatch_PC_by_way,
	output logic [3:0][31:0] last_dispatch_pred_PC_by_way,
	output logic [3:0] last_dispatch_is_rename_by_way,
	output logic [3:0][BTB_PRED_INFO_WIDTH-1:0] last_dispatch_pred_info_by_way,
	output logic [3:0][MDPT_INFO_WIDTH-1:0] last_dispatch_mdp_info_by_way,
	output logic [3:0][3:0] last_dispatch_op_by_way,
	output logic [3:0][19:0] last_dispatch_imm20_by_way,

    // ordering
	output logic [3:0] last_dispatch_mem_aq_by_way,
	output logic [3:0] last_dispatch_io_aq_by_way,
	output logic [3:0] last_dispatch_mem_rl_by_way,
	output logic [3:0] last_dispatch_io_rl_by_way,

    // exception info
	output logic last_dispatch_is_page_fault,
	output logic last_dispatch_is_access_fault,
	output logic last_dispatch_is_illegal_instr,
	output logic last_dispatch_exception_present,
	output logic [1:0] last_dispatch_exception_index,
	output logic [31:0] last_dispatch_illegal_instr32,

	// checkpoint info
	output logic last_dispatch_has_checkpoint,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0] last_dispatch_checkpoint_index,

    // instr IQ attempts
	output logic [3:0] last_dispatch_attempt_alu_reg_mdu_dq_by_way,
	output logic [3:0] last_dispatch_attempt_alu_imm_dq_by_way,
	output logic [3:0] last_dispatch_attempt_bru_dq_by_way,
	output logic [3:0] last_dispatch_attempt_ldu_dq_by_way,
	output logic [3:0] last_dispatch_attempt_stamofu_dq_by_way,
	output logic [3:0] last_dispatch_attempt_sysu_dq_by_way,

    // instr FU valids
	output logic [3:0] last_dispatch_valid_alu_reg_by_way,
	output logic [3:0] last_dispatch_valid_mdu_by_way,
	output logic [3:0] last_dispatch_valid_alu_imm_by_way,
	output logic [3:0] last_dispatch_valid_bru_by_way,
	output logic [3:0] last_dispatch_valid_ldu_by_way,
	output logic [3:0] last_dispatch_valid_store_by_way,
	output logic [3:0] last_dispatch_valid_amo_by_way,
	output logic [3:0] last_dispatch_valid_fence_by_way,
	output logic [3:0] last_dispatch_valid_sysu_by_way,

    // operand A
	output logic [3:0][LOG_PR_COUNT-1:0] last_dispatch_A_PR_by_way,
	output logic [3:0] last_dispatch_A_ready_by_way,
	output logic [3:0] last_dispatch_A_is_zero_by_way,
	output logic [3:0] last_dispatch_A_unneeded_or_is_zero_by_way,
	output logic [3:0] last_dispatch_A_is_ret_ra_by_way,

    // operand B
	output logic [3:0][LOG_PR_COUNT-1:0] last_dispatch_B_PR_by_way,
	output logic [3:0] last_dispatch_B_ready_by_way,
	output logic [3:0] last_dispatch_B_is_zero_by_way,
	output logic [3:0] last_dispatch_B_unneeded_or_is_zero_by_way,

    // dest operand
	output logic [3:0][4:0] last_dispatch_dest_AR_by_way,
	output logic [3:0][LOG_PR_COUNT-1:0] last_dispatch_dest_old_PR_by_way,
	output logic [3:0][LOG_PR_COUNT-1:0] last_dispatch_dest_new_PR_by_way,
	output logic [3:0] last_dispatch_dest_is_link_ra,

    // instr IQ acks
	input logic [3:0] next_dispatch_ack_alu_reg_mdu_dq_by_way,
	input logic [3:0] next_dispatch_ack_alu_imm_dq_by_way,
	input logic [3:0] next_dispatch_ack_bru_dq_by_way,
	input logic [3:0] next_dispatch_ack_ldu_dq_by_way,
	input logic [3:0] next_dispatch_ack_stamofu_dq_by_way,
	input logic [3:0] next_dispatch_ack_sysu_dq_by_way,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // fetch + decode restart from ROB
	input logic next_rob_restart_valid,
	input logic [1:0] next_rob_restart_exec_mode,
	input logic next_rob_restart_trap_sfence,
	input logic next_rob_restart_trap_wfi,
	input logic next_rob_restart_trap_sret,

    // branch update from ROB
	input logic next_rob_branch_update_valid,
	input logic next_rob_branch_update_has_checkpoint,
	input logic next_rob_branch_update_is_mispredict,
	input logic next_rob_branch_update_is_taken,
	input logic next_rob_branch_update_use_upct,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_rob_branch_update_intermediate_pred_info,
	input logic next_rob_branch_update_pred_lru,
	input logic [31:0] next_rob_branch_update_start_PC,
	input logic [31:0] next_rob_branch_update_target_PC,

    // ROB control of rename
	input logic next_rob_controlling_rename,
	input logic next_rob_checkpoint_restore_valid,
	input logic next_rob_checkpoint_restore_clear,
	input logic [CHECKPOINT_INDEX_WIDTH-1:0] next_rob_checkpoint_restore_index,
	input logic [3:0] next_rob_map_table_write_valid_by_port,
	input logic [3:0][LOG_AR_COUNT-1:0] next_rob_map_table_write_AR_by_port,
	input logic [3:0][LOG_PR_COUNT-1:0] next_rob_map_table_write_PR_by_port,

	// ROB physical register freeing
	input logic [3:0] next_rob_PR_free_req_valid_by_bank,
	input logic [3:0][LOG_PR_COUNT-1:0] next_rob_PR_free_req_PR_by_bank,
	output logic [3:0] last_rob_PR_free_resp_ack_by_bank,

    // branch update to fetch unit
	output logic last_decode_unit_branch_update_valid,
	output logic last_decode_unit_branch_update_has_checkpoint,
	output logic last_decode_unit_branch_update_is_mispredict,
	output logic last_decode_unit_branch_update_is_taken,
	output logic last_decode_unit_branch_update_is_complex,
	output logic last_decode_unit_branch_update_use_upct,
	output logic [BTB_PRED_INFO_WIDTH-1:0] last_decode_unit_branch_update_intermediate_pred_info,
	output logic last_decode_unit_branch_update_pred_lru,
	output logic [31:0] last_decode_unit_branch_update_start_PC,
	output logic [31:0] last_decode_unit_branch_update_target_PC,
	output logic [LH_LENGTH-1:0] last_decode_unit_branch_update_LH,
	output logic [GH_LENGTH-1:0] last_decode_unit_branch_update_GH,
	output logic [RAS_INDEX_WIDTH-1:0] last_decode_unit_branch_update_ras_index,

    // decode unit control
	output logic last_decode_unit_restart_valid,
	output logic [31:0] last_decode_unit_restart_PC,

	output logic last_decode_unit_trigger_wait_for_restart,

	// hardware failure
	output logic last_unrecoverable_fault
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // input from istream
	logic istream_valid_SDEQ;
	logic [3:0] istream_valid_by_way_SDEQ;
	logic [3:0] istream_uncompressed_by_way_SDEQ;
	logic [3:0][1:0][15:0] istream_instr_2B_by_way_by_chunk_SDEQ;
	logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0] istream_pred_info_by_way_by_chunk_SDEQ;
	logic [3:0][1:0] istream_pred_lru_by_way_by_chunk_SDEQ;
    // input logic [3:0][1:0]                           	istream_redirect_by_way_by_chunk_SDEQ, // unused
	logic [3:0][1:0][31:0] istream_pred_PC_by_way_by_chunk_SDEQ;
	logic [3:0][1:0] istream_page_fault_by_way_by_chunk_SDEQ;
	logic [3:0][1:0] istream_access_fault_by_way_by_chunk_SDEQ;
	logic [3:0][MDPT_INFO_WIDTH-1:0] istream_mdp_info_by_way_SDEQ;
	logic [3:0][31:0] istream_PC_by_way_SDEQ;
	logic [3:0][LH_LENGTH-1:0] istream_LH_by_way_SDEQ;
	logic [3:0][GH_LENGTH-1:0] istream_GH_by_way_SDEQ;
	logic [3:0][RAS_INDEX_WIDTH-1:0] istream_ras_index_by_way_SDEQ;

    // feedback to istream
	logic istream_stall_SDEQ;

    // op dispatch by way:

    // 4-way ROB entry
	logic dispatch_rob_enqueue_valid;
	logic dispatch_rob_enqueue_ready;

    // general instr info
	logic [3:0] dispatch_valid_by_way;
	logic [3:0] dispatch_uncompressed_by_way;
	logic [3:0][31:0] dispatch_PC_by_way;
	logic [3:0][31:0] dispatch_pred_PC_by_way;
	logic [3:0] dispatch_is_rename_by_way;
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0] dispatch_pred_info_by_way;
	logic [3:0][MDPT_INFO_WIDTH-1:0] dispatch_mdp_info_by_way;
	logic [3:0][3:0] dispatch_op_by_way;
	logic [3:0][19:0] dispatch_imm20_by_way;

    // ordering
	logic [3:0] dispatch_mem_aq_by_way;
	logic [3:0] dispatch_io_aq_by_way;
	logic [3:0] dispatch_mem_rl_by_way;
	logic [3:0] dispatch_io_rl_by_way;

    // exception info
	logic dispatch_is_page_fault;
	logic dispatch_is_access_fault;
	logic dispatch_is_illegal_instr;
	logic dispatch_exception_present;
	logic [1:0] dispatch_exception_index;
	logic [31:0] dispatch_illegal_instr32;

	// checkpoint info
	logic dispatch_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] dispatch_checkpoint_index;

    // instr IQ attempts
	logic [3:0] dispatch_attempt_alu_reg_mdu_dq_by_way;
	logic [3:0] dispatch_attempt_alu_imm_dq_by_way;
	logic [3:0] dispatch_attempt_bru_dq_by_way;
	logic [3:0] dispatch_attempt_ldu_dq_by_way;
	logic [3:0] dispatch_attempt_stamofu_dq_by_way;
	logic [3:0] dispatch_attempt_sysu_dq_by_way;

    // instr FU valids
	logic [3:0] dispatch_valid_alu_reg_by_way;
	logic [3:0] dispatch_valid_mdu_by_way;
	logic [3:0] dispatch_valid_alu_imm_by_way;
	logic [3:0] dispatch_valid_bru_by_way;
	logic [3:0] dispatch_valid_ldu_by_way;
	logic [3:0] dispatch_valid_store_by_way;
	logic [3:0] dispatch_valid_amo_by_way;
	logic [3:0] dispatch_valid_fence_by_way;
	logic [3:0] dispatch_valid_sysu_by_way;

    // operand A
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_way;
	logic [3:0] dispatch_A_ready_by_way;
	logic [3:0] dispatch_A_is_zero_by_way;
	logic [3:0] dispatch_A_unneeded_or_is_zero_by_way;
	logic [3:0] dispatch_A_is_ret_ra_by_way;

    // operand B
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_B_PR_by_way;
	logic [3:0] dispatch_B_ready_by_way;
	logic [3:0] dispatch_B_is_zero_by_way;
	logic [3:0] dispatch_B_unneeded_or_is_zero_by_way;

    // dest operand
	logic [3:0][4:0] dispatch_dest_AR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_old_PR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_new_PR_by_way;
	logic [3:0] dispatch_dest_is_link_ra;

    // instr IQ acks
	logic [3:0] dispatch_ack_alu_reg_mdu_dq_by_way;
	logic [3:0] dispatch_ack_alu_imm_dq_by_way;
	logic [3:0] dispatch_ack_bru_dq_by_way;
	logic [3:0] dispatch_ack_ldu_dq_by_way;
	logic [3:0] dispatch_ack_stamofu_dq_by_way;
	logic [3:0] dispatch_ack_sysu_dq_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // fetch + decode restart from ROB
	logic rob_restart_valid;
	logic [1:0] rob_restart_exec_mode;
	logic rob_restart_trap_sfence;
	logic rob_restart_trap_wfi;
	logic rob_restart_trap_sret;

    // branch update from ROB
	logic rob_branch_update_valid;
	logic rob_branch_update_has_checkpoint;
	logic rob_branch_update_is_mispredict;
	logic rob_branch_update_is_taken;
	logic rob_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] rob_branch_update_intermediate_pred_info;
	logic rob_branch_update_pred_lru;
	logic [31:0] rob_branch_update_start_PC;
	logic [31:0] rob_branch_update_target_PC;

    // ROB control of rename
	logic rob_controlling_rename;
	logic rob_checkpoint_restore_valid;
	logic rob_checkpoint_restore_clear;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] rob_checkpoint_restore_index;
	logic [3:0] rob_map_table_write_valid_by_port;
	logic [3:0][LOG_AR_COUNT-1:0] rob_map_table_write_AR_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] rob_map_table_write_PR_by_port;

	// ROB physical register freeing
	logic [3:0] rob_PR_free_req_valid_by_bank;
	logic [3:0][LOG_PR_COUNT-1:0] rob_PR_free_req_PR_by_bank;
	logic [3:0] rob_PR_free_resp_ack_by_bank;

    // branch update to fetch unit
	logic decode_unit_branch_update_valid;
	logic decode_unit_branch_update_has_checkpoint;
	logic decode_unit_branch_update_is_mispredict;
	logic decode_unit_branch_update_is_taken;
	logic decode_unit_branch_update_is_complex;
	logic decode_unit_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] decode_unit_branch_update_intermediate_pred_info;
	logic decode_unit_branch_update_pred_lru;
	logic [31:0] decode_unit_branch_update_start_PC;
	logic [31:0] decode_unit_branch_update_target_PC;
	logic [LH_LENGTH-1:0] decode_unit_branch_update_LH;
	logic [GH_LENGTH-1:0] decode_unit_branch_update_GH;
	logic [RAS_INDEX_WIDTH-1:0] decode_unit_branch_update_ras_index;

    // decode unit control
	logic decode_unit_restart_valid;
	logic [31:0] decode_unit_restart_PC;

	logic decode_unit_trigger_wait_for_restart;

	// hardware failure
	logic unrecoverable_fault;

    // ----------------------------------------------------------------
    // Module Instantiation:

    decode_unit #(
		.INIT_EXEC_MODE(M_MODE),
		.INIT_TRAP_SFENCE(1'b0),
		.INIT_TRAP_WFI(1'b0),
		.INIT_TRAP_SRET(1'b0)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // input from istream
			istream_valid_SDEQ <= '0;
			istream_valid_by_way_SDEQ <= '0;
			istream_uncompressed_by_way_SDEQ <= '0;
			istream_instr_2B_by_way_by_chunk_SDEQ <= '0;
			istream_pred_info_by_way_by_chunk_SDEQ <= '0;
			istream_pred_lru_by_way_by_chunk_SDEQ <= '0;
		    // input logic [3:0][1:0]                           	istream_redirect_by_way_by_chunk_SDEQ, // unused
			istream_pred_PC_by_way_by_chunk_SDEQ <= '0;
			istream_page_fault_by_way_by_chunk_SDEQ <= '0;
			istream_access_fault_by_way_by_chunk_SDEQ <= '0;
			istream_mdp_info_by_way_SDEQ <= '0;
			istream_PC_by_way_SDEQ <= '0;
			istream_LH_by_way_SDEQ <= '0;
			istream_GH_by_way_SDEQ <= '0;
			istream_ras_index_by_way_SDEQ <= '0;

		    // feedback to istream
			last_istream_stall_SDEQ <= '0;

		    // op dispatch by way:

		    // 4-way ROB entry
			last_dispatch_rob_enqueue_valid <= '0;
			dispatch_rob_enqueue_ready <= '0;

		    // general instr info
			last_dispatch_valid_by_way <= '0;
			last_dispatch_uncompressed_by_way <= '0;
			last_dispatch_PC_by_way <= '0;
			last_dispatch_pred_PC_by_way <= '0;
			last_dispatch_is_rename_by_way <= '0;
			last_dispatch_pred_info_by_way <= '0;
			last_dispatch_mdp_info_by_way <= '0;
			last_dispatch_op_by_way <= '0;
			last_dispatch_imm20_by_way <= '0;

		    // ordering
			last_dispatch_mem_aq_by_way <= '0;
			last_dispatch_io_aq_by_way <= '0;
			last_dispatch_mem_rl_by_way <= '0;
			last_dispatch_io_rl_by_way <= '0;

		    // exception info
			last_dispatch_is_page_fault <= '0;
			last_dispatch_is_access_fault <= '0;
			last_dispatch_is_illegal_instr <= '0;
			last_dispatch_exception_present <= '0;
			last_dispatch_exception_index <= '0;
			last_dispatch_illegal_instr32 <= '0;

			// checkpoint info
			last_dispatch_has_checkpoint <= '0;
			last_dispatch_checkpoint_index <= '0;

		    // instr IQ attempts
			last_dispatch_attempt_alu_reg_mdu_dq_by_way <= '0;
			last_dispatch_attempt_alu_imm_dq_by_way <= '0;
			last_dispatch_attempt_bru_dq_by_way <= '0;
			last_dispatch_attempt_ldu_dq_by_way <= '0;
			last_dispatch_attempt_stamofu_dq_by_way <= '0;
			last_dispatch_attempt_sysu_dq_by_way <= '0;

		    // instr FU valids
			last_dispatch_valid_alu_reg_by_way <= '0;
			last_dispatch_valid_mdu_by_way <= '0;
			last_dispatch_valid_alu_imm_by_way <= '0;
			last_dispatch_valid_bru_by_way <= '0;
			last_dispatch_valid_ldu_by_way <= '0;
			last_dispatch_valid_store_by_way <= '0;
			last_dispatch_valid_amo_by_way <= '0;
			last_dispatch_valid_fence_by_way <= '0;
			last_dispatch_valid_sysu_by_way <= '0;

		    // operand A
			last_dispatch_A_PR_by_way <= '0;
			last_dispatch_A_ready_by_way <= '0;
			last_dispatch_A_is_zero_by_way <= '0;
			last_dispatch_A_unneeded_or_is_zero_by_way <= '0;
			last_dispatch_A_is_ret_ra_by_way <= '0;

		    // operand B
			last_dispatch_B_PR_by_way <= '0;
			last_dispatch_B_ready_by_way <= '0;
			last_dispatch_B_is_zero_by_way <= '0;
			last_dispatch_B_unneeded_or_is_zero_by_way <= '0;

		    // dest operand
			last_dispatch_dest_AR_by_way <= '0;
			last_dispatch_dest_old_PR_by_way <= '0;
			last_dispatch_dest_new_PR_by_way <= '0;
			last_dispatch_dest_is_link_ra <= '0;

		    // instr IQ acks
			dispatch_ack_alu_reg_mdu_dq_by_way <= '0;
			dispatch_ack_alu_imm_dq_by_way <= '0;
			dispatch_ack_bru_dq_by_way <= '0;
			dispatch_ack_ldu_dq_by_way <= '0;
			dispatch_ack_stamofu_dq_by_way <= '0;
			dispatch_ack_sysu_dq_by_way <= '0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= '0;
			WB_bus_upper_PR_by_bank <= '0;

		    // fetch + decode restart from ROB
			rob_restart_valid <= '0;
			rob_restart_exec_mode <= '0;
			rob_restart_trap_sfence <= '0;
			rob_restart_trap_wfi <= '0;
			rob_restart_trap_sret <= '0;

		    // branch update from ROB
			rob_branch_update_valid <= '0;
			rob_branch_update_has_checkpoint <= '0;
			rob_branch_update_is_mispredict <= '0;
			rob_branch_update_is_taken <= '0;
			rob_branch_update_use_upct <= '0;
			rob_branch_update_intermediate_pred_info <= '0;
			rob_branch_update_pred_lru <= '0;
			rob_branch_update_start_PC <= '0;
			rob_branch_update_target_PC <= '0;

		    // ROB control of rename
			rob_controlling_rename <= '0;
			rob_checkpoint_restore_valid <= '0;
			rob_checkpoint_restore_clear <= '0;
			rob_checkpoint_restore_index <= '0;
			rob_map_table_write_valid_by_port <= '0;
			rob_map_table_write_AR_by_port <= '0;
			rob_map_table_write_PR_by_port <= '0;

			// ROB physical register freeing
			rob_PR_free_req_valid_by_bank <= '0;
			rob_PR_free_req_PR_by_bank <= '0;
			last_rob_PR_free_resp_ack_by_bank <= '0;

		    // branch update to fetch unit
			last_decode_unit_branch_update_valid <= '0;
			last_decode_unit_branch_update_has_checkpoint <= '0;
			last_decode_unit_branch_update_is_mispredict <= '0;
			last_decode_unit_branch_update_is_taken <= '0;
			last_decode_unit_branch_update_is_complex <= '0;
			last_decode_unit_branch_update_use_upct <= '0;
			last_decode_unit_branch_update_intermediate_pred_info <= '0;
			last_decode_unit_branch_update_pred_lru <= '0;
			last_decode_unit_branch_update_start_PC <= '0;
			last_decode_unit_branch_update_target_PC <= '0;
			last_decode_unit_branch_update_LH <= '0;
			last_decode_unit_branch_update_GH <= '0;
			last_decode_unit_branch_update_ras_index <= '0;

		    // decode unit control
			last_decode_unit_restart_valid <= '0;
			last_decode_unit_restart_PC <= '0;

			last_decode_unit_trigger_wait_for_restart <= '0;

			// hardware failure
			last_unrecoverable_fault <= '0;
        end
        else begin


		    // input from istream
			istream_valid_SDEQ <= next_istream_valid_SDEQ;
			istream_valid_by_way_SDEQ <= next_istream_valid_by_way_SDEQ;
			istream_uncompressed_by_way_SDEQ <= next_istream_uncompressed_by_way_SDEQ;
			istream_instr_2B_by_way_by_chunk_SDEQ <= next_istream_instr_2B_by_way_by_chunk_SDEQ;
			istream_pred_info_by_way_by_chunk_SDEQ <= next_istream_pred_info_by_way_by_chunk_SDEQ;
			istream_pred_lru_by_way_by_chunk_SDEQ <= next_istream_pred_lru_by_way_by_chunk_SDEQ;
		    // input logic [3:0][1:0]                           	istream_redirect_by_way_by_chunk_SDEQ, // unused
			istream_pred_PC_by_way_by_chunk_SDEQ <= next_istream_pred_PC_by_way_by_chunk_SDEQ;
			istream_page_fault_by_way_by_chunk_SDEQ <= next_istream_page_fault_by_way_by_chunk_SDEQ;
			istream_access_fault_by_way_by_chunk_SDEQ <= next_istream_access_fault_by_way_by_chunk_SDEQ;
			istream_mdp_info_by_way_SDEQ <= next_istream_mdp_info_by_way_SDEQ;
			istream_PC_by_way_SDEQ <= next_istream_PC_by_way_SDEQ;
			istream_LH_by_way_SDEQ <= next_istream_LH_by_way_SDEQ;
			istream_GH_by_way_SDEQ <= next_istream_GH_by_way_SDEQ;
			istream_ras_index_by_way_SDEQ <= next_istream_ras_index_by_way_SDEQ;

		    // feedback to istream
			last_istream_stall_SDEQ <= istream_stall_SDEQ;

		    // op dispatch by way:

		    // 4-way ROB entry
			last_dispatch_rob_enqueue_valid <= dispatch_rob_enqueue_valid;
			dispatch_rob_enqueue_ready <= next_dispatch_rob_enqueue_ready;

		    // general instr info
			last_dispatch_valid_by_way <= dispatch_valid_by_way;
			last_dispatch_uncompressed_by_way <= dispatch_uncompressed_by_way;
			last_dispatch_PC_by_way <= dispatch_PC_by_way;
			last_dispatch_pred_PC_by_way <= dispatch_pred_PC_by_way;
			last_dispatch_is_rename_by_way <= dispatch_is_rename_by_way;
			last_dispatch_pred_info_by_way <= dispatch_pred_info_by_way;
			last_dispatch_mdp_info_by_way <= dispatch_mdp_info_by_way;
			last_dispatch_op_by_way <= dispatch_op_by_way;
			last_dispatch_imm20_by_way <= dispatch_imm20_by_way;

		    // ordering
			last_dispatch_mem_aq_by_way <= dispatch_mem_aq_by_way;
			last_dispatch_io_aq_by_way <= dispatch_io_aq_by_way;
			last_dispatch_mem_rl_by_way <= dispatch_mem_rl_by_way;
			last_dispatch_io_rl_by_way <= dispatch_io_rl_by_way;

		    // exception info
			last_dispatch_is_page_fault <= dispatch_is_page_fault;
			last_dispatch_is_access_fault <= dispatch_is_access_fault;
			last_dispatch_is_illegal_instr <= dispatch_is_illegal_instr;
			last_dispatch_exception_present <= dispatch_exception_present;
			last_dispatch_exception_index <= dispatch_exception_index;
			last_dispatch_illegal_instr32 <= dispatch_illegal_instr32;

			// checkpoint info
			last_dispatch_has_checkpoint <= dispatch_has_checkpoint;
			last_dispatch_checkpoint_index <= dispatch_checkpoint_index;

		    // instr IQ attempts
			last_dispatch_attempt_alu_reg_mdu_dq_by_way <= dispatch_attempt_alu_reg_mdu_dq_by_way;
			last_dispatch_attempt_alu_imm_dq_by_way <= dispatch_attempt_alu_imm_dq_by_way;
			last_dispatch_attempt_bru_dq_by_way <= dispatch_attempt_bru_dq_by_way;
			last_dispatch_attempt_ldu_dq_by_way <= dispatch_attempt_ldu_dq_by_way;
			last_dispatch_attempt_stamofu_dq_by_way <= dispatch_attempt_stamofu_dq_by_way;
			last_dispatch_attempt_sysu_dq_by_way <= dispatch_attempt_sysu_dq_by_way;

		    // instr FU valids
			last_dispatch_valid_alu_reg_by_way <= dispatch_valid_alu_reg_by_way;
			last_dispatch_valid_mdu_by_way <= dispatch_valid_mdu_by_way;
			last_dispatch_valid_alu_imm_by_way <= dispatch_valid_alu_imm_by_way;
			last_dispatch_valid_bru_by_way <= dispatch_valid_bru_by_way;
			last_dispatch_valid_ldu_by_way <= dispatch_valid_ldu_by_way;
			last_dispatch_valid_store_by_way <= dispatch_valid_store_by_way;
			last_dispatch_valid_amo_by_way <= dispatch_valid_amo_by_way;
			last_dispatch_valid_fence_by_way <= dispatch_valid_fence_by_way;
			last_dispatch_valid_sysu_by_way <= dispatch_valid_sysu_by_way;

		    // operand A
			last_dispatch_A_PR_by_way <= dispatch_A_PR_by_way;
			last_dispatch_A_ready_by_way <= dispatch_A_ready_by_way;
			last_dispatch_A_is_zero_by_way <= dispatch_A_is_zero_by_way;
			last_dispatch_A_unneeded_or_is_zero_by_way <= dispatch_A_unneeded_or_is_zero_by_way;
			last_dispatch_A_is_ret_ra_by_way <= dispatch_A_is_ret_ra_by_way;

		    // operand B
			last_dispatch_B_PR_by_way <= dispatch_B_PR_by_way;
			last_dispatch_B_ready_by_way <= dispatch_B_ready_by_way;
			last_dispatch_B_is_zero_by_way <= dispatch_B_is_zero_by_way;
			last_dispatch_B_unneeded_or_is_zero_by_way <= dispatch_B_unneeded_or_is_zero_by_way;

		    // dest operand
			last_dispatch_dest_AR_by_way <= dispatch_dest_AR_by_way;
			last_dispatch_dest_old_PR_by_way <= dispatch_dest_old_PR_by_way;
			last_dispatch_dest_new_PR_by_way <= dispatch_dest_new_PR_by_way;
			last_dispatch_dest_is_link_ra <= dispatch_dest_is_link_ra;

		    // instr IQ acks
			dispatch_ack_alu_reg_mdu_dq_by_way <= next_dispatch_ack_alu_reg_mdu_dq_by_way;
			dispatch_ack_alu_imm_dq_by_way <= next_dispatch_ack_alu_imm_dq_by_way;
			dispatch_ack_bru_dq_by_way <= next_dispatch_ack_bru_dq_by_way;
			dispatch_ack_ldu_dq_by_way <= next_dispatch_ack_ldu_dq_by_way;
			dispatch_ack_stamofu_dq_by_way <= next_dispatch_ack_stamofu_dq_by_way;
			dispatch_ack_sysu_dq_by_way <= next_dispatch_ack_sysu_dq_by_way;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // fetch + decode restart from ROB
			rob_restart_valid <= next_rob_restart_valid;
			rob_restart_exec_mode <= next_rob_restart_exec_mode;
			rob_restart_trap_sfence <= next_rob_restart_trap_sfence;
			rob_restart_trap_wfi <= next_rob_restart_trap_wfi;
			rob_restart_trap_sret <= next_rob_restart_trap_sret;

		    // branch update from ROB
			rob_branch_update_valid <= next_rob_branch_update_valid;
			rob_branch_update_has_checkpoint <= next_rob_branch_update_has_checkpoint;
			rob_branch_update_is_mispredict <= next_rob_branch_update_is_mispredict;
			rob_branch_update_is_taken <= next_rob_branch_update_is_taken;
			rob_branch_update_use_upct <= next_rob_branch_update_use_upct;
			rob_branch_update_intermediate_pred_info <= next_rob_branch_update_intermediate_pred_info;
			rob_branch_update_pred_lru <= next_rob_branch_update_pred_lru;
			rob_branch_update_start_PC <= next_rob_branch_update_start_PC;
			rob_branch_update_target_PC <= next_rob_branch_update_target_PC;

		    // ROB control of rename
			rob_controlling_rename <= next_rob_controlling_rename;
			rob_checkpoint_restore_valid <= next_rob_checkpoint_restore_valid;
			rob_checkpoint_restore_clear <= next_rob_checkpoint_restore_clear;
			rob_checkpoint_restore_index <= next_rob_checkpoint_restore_index;
			rob_map_table_write_valid_by_port <= next_rob_map_table_write_valid_by_port;
			rob_map_table_write_AR_by_port <= next_rob_map_table_write_AR_by_port;
			rob_map_table_write_PR_by_port <= next_rob_map_table_write_PR_by_port;

			// ROB physical register freeing
			rob_PR_free_req_valid_by_bank <= next_rob_PR_free_req_valid_by_bank;
			rob_PR_free_req_PR_by_bank <= next_rob_PR_free_req_PR_by_bank;
			last_rob_PR_free_resp_ack_by_bank <= rob_PR_free_resp_ack_by_bank;

		    // branch update to fetch unit
			last_decode_unit_branch_update_valid <= decode_unit_branch_update_valid;
			last_decode_unit_branch_update_has_checkpoint <= decode_unit_branch_update_has_checkpoint;
			last_decode_unit_branch_update_is_mispredict <= decode_unit_branch_update_is_mispredict;
			last_decode_unit_branch_update_is_taken <= decode_unit_branch_update_is_taken;
			last_decode_unit_branch_update_is_complex <= decode_unit_branch_update_is_complex;
			last_decode_unit_branch_update_use_upct <= decode_unit_branch_update_use_upct;
			last_decode_unit_branch_update_intermediate_pred_info <= decode_unit_branch_update_intermediate_pred_info;
			last_decode_unit_branch_update_pred_lru <= decode_unit_branch_update_pred_lru;
			last_decode_unit_branch_update_start_PC <= decode_unit_branch_update_start_PC;
			last_decode_unit_branch_update_target_PC <= decode_unit_branch_update_target_PC;
			last_decode_unit_branch_update_LH <= decode_unit_branch_update_LH;
			last_decode_unit_branch_update_GH <= decode_unit_branch_update_GH;
			last_decode_unit_branch_update_ras_index <= decode_unit_branch_update_ras_index;

		    // decode unit control
			last_decode_unit_restart_valid <= decode_unit_restart_valid;
			last_decode_unit_restart_PC <= decode_unit_restart_PC;

			last_decode_unit_trigger_wait_for_restart <= decode_unit_trigger_wait_for_restart;

			// hardware failure
			last_unrecoverable_fault <= unrecoverable_fault;
        end
    end

endmodule