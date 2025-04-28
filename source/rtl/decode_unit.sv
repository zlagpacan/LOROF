/*
    Filename: decode_unit.sv
    Author: zlagpacan
    Description: RTL for Decode Unit
    Spec: LOROF/spec/design/decode_unit.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module decode_unit #(
    parameter INIT_EXEC_MODE = M_MODE,
	parameter INIT_TRAP_SFENCE = 1'b0,
	parameter INIT_TRAP_WFI = 1'b0,
	parameter INIT_TRAP_SRET = 1'b0
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

    // 4-way ROB entry
    output logic                                  	rob_dispatch_valid,
	output logic									rob_dispatch_has_checkpoint,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0]		rob_dispatch_checkpoint_index,

    // general instr info
    output logic [3:0]                              dispatch_valid_by_way,
    output logic [3:0]                              dispatch_uncompressed_by_way,
    output logic [31:0]                             dispatch_PC_by_way,
    output logic [31:0]                             dispatch_pred_PC_by_way,
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

    // instr IQ acks
    input logic [3:0]   dispatch_ack_alu_reg_mdu_iq_by_way,
    input logic [3:0]   dispatch_ack_alu_imm_iq_by_way,
    input logic [3:0]   dispatch_ack_ldu_iq_by_way,
    input logic [3:0]   dispatch_ack_bru_iq_by_way,
    input logic [3:0]   dispatch_ack_stamofu_iq_by_way,
    input logic [3:0]   dispatch_ack_sys_iq_by_way,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // fetch + decode restart from ROB
    input logic       	rob_restart_valid,
    input logic [1:0] 	rob_restart_exec_mode,
    input logic      	rob_restart_trap_sfence,
    input logic      	rob_restart_trap_wfi,
    input logic      	rob_restart_trap_sret,

    // branch update from ROB
    input logic                             rob_branch_update_valid,
    input logic                             rob_branch_update_has_checkpoint,
    input logic                             rob_branch_update_is_mispredict,
    input logic                             rob_branch_update_is_taken,
    input logic                             rob_branch_update_use_upct,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   rob_branch_update_intermediate_pred_info,
    input logic                             rob_branch_update_pred_lru,
    input logic [31:0]                      rob_branch_update_start_PC,
    input logic [31:0]                      rob_branch_update_target_PC,

    // ROB control of rename
    input logic                             	rob_controlling_rename,
    input logic                                 rob_checkpoint_restore_valid,
    input logic                                 rob_checkpoint_restore_clear,
    input logic [CHECKPOINT_INDEX_WIDTH-1:0]    rob_checkpoint_restore_index,
    input logic [3:0]                       	rob_map_table_write_valid_by_port,
    input logic [3:0][LOG_AR_COUNT-1:0]     	rob_map_table_write_AR_by_port,
    input logic [3:0][LOG_PR_COUNT-1:0]     	rob_map_table_write_PR_by_port,

	// ROB physical register freeing
	input logic [3:0]	rob_PR_free_req_valid_by_bank,
	input logic [3:0]	rob_PR_free_req_PR_by_bank,
	output logic [3:0]	rob_PR_free_resp_ack_by_bank,

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
    output logic [RAS_INDEX_WIDTH-1:0]    	decode_unit_branch_update_ras_index,

    // decode unit control
    output logic       		decode_unit_restart_valid,
    output logic [31:0]		decode_unit_restart_PC,

    output logic       		decode_unit_trigger_wait_for_restart,

	// hardware failure
	output logic unrecoverable_fault
);

	// need to send decode_unit restart to fetch_unit AFTER decode_unit update has finished
    // don't want another mispred

    // ----------------------------------------------------------------
    // Signals:

	/////////////////
	// SDEQ Stage: //
	/////////////////
		// Stream Dequeue

	// state:
	logic valid_DEC_from_SDEQ;

	// control:
	logic stall_SDEQ;

	// SDEQ/DEC pipeline reg's:
	logic [3:0]                              	valid_by_way_DEC, next_valid_by_way_DEC;
	logic [3:0]                              	uncompressed_by_way_DEC, next_uncompressed_by_way_DEC;
	logic [3:0][1:0][15:0]                   	instr_2B_by_way_by_chunk_DEC, next_instr_2B_by_way_by_chunk_DEC;
	logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0]	pred_info_by_way_by_chunk_DEC, next_pred_info_by_way_by_chunk_DEC;
	logic [3:0][1:0]                         	pred_lru_by_way_by_chunk_DEC, next_pred_lru_by_way_by_chunk_DEC;
	logic [3:0][1:0][31:0]                   	pred_PC_by_way_DEC, next_pred_PC_by_way_DEC;
	logic [3:0][1:0]                         	page_fault_by_way_DEC, next_page_fault_by_way_DEC;
	logic [3:0][1:0]                         	access_fault_by_way_DEC, next_access_fault_by_way_DEC;
	logic [3:0][MDPT_INFO_WIDTH-1:0]         	mdp_info_by_way_DEC, next_mdp_info_by_way_DEC;
	logic [3:0][31:0]                        	PC_by_way_DEC, next_PC_by_way_DEC;
	logic [3:0][LH_LENGTH-1:0]               	LH_by_way_DEC, next_LH_by_way_DEC;
	logic [3:0][GH_LENGTH-1:0]               	GH_by_way_DEC, next_GH_by_way_DEC;
	logic [3:0][RAS_INDEX_WIDTH-1:0]         	ras_index_by_way_DEC, next_ras_index_by_way_DEC;

	// modules:

	////////////////
	// DEC Stage: //
	////////////////
		// Decode

	// state:
	logic valid_RNM_from_DEC;

	typedef enum logic [2:0] {
		DEC_IDLE,
		DEC_ACTIVE,
		DEC_TRIGGER_WFR,
		DEC_RESTART_0,
		DEC_RESTART_1,
		DEC_RESTART_2
	} DEC_state_t;
	
	DEC_state_t state_DEC, next_state_DEC;

	// control:
	logic stall_DEC;
	logic restart_present_DEC;
	logic wfr_present_DEC;
	logic [1:0] restart_wfr_saved_index_DEC, next_restart_wfr_saved_index_DEC;
	logic [31:0] restart_wfr_saved_branch_notif_PC_DEC, next_restart_wfr_saved_branch_notif_PC_DEC;
	logic [31:0] restart_wfr_saved_restart_PC_DEC, next_restart_wfr_saved_restart_PC_DEC;
	logic restart_wfr_saved_pred_lru_DEC, next_restart_wfr_saved_pred_lru_DEC;
	logic [3:0] cancel_by_way_DEC;

    logic [1:0]	exec_mode_DEC;
    logic      	trap_sfence_DEC;
    logic      	trap_wfi_DEC;
    logic      	trap_sret_DEC;

	// DEC stage control of branch update
	logic                          		DEC_decode_unit_branch_update_valid;
    logic                          		DEC_decode_unit_branch_update_has_checkpoint;
    logic                          		DEC_decode_unit_branch_update_is_complex;
    logic                          		DEC_decode_unit_branch_update_use_upct;
    logic [BTB_PRED_INFO_WIDTH-1:0]		DEC_decode_unit_branch_update_intermediate_pred_info;
    logic                          		DEC_decode_unit_branch_update_pred_lru;
    logic [31:0]                   		DEC_decode_unit_branch_update_start_PC;

	// DEC/RNM pipeline reg's:

	// non-decoder
	logic [3:0] 		valid_by_way_RNM, next_valid_by_way_RNM;
	logic [3:0][31:0] 	PC_by_way_RNM, next_PC_by_way_RNM;
	logic [3:0][31:0] 	pred_PC_by_way_RNM, next_pred_PC_by_way_RNM;

	// FU select
	logic [3:0] is_alu_reg_by_way_RNM, next_is_alu_reg_by_way_RNM;
	logic [3:0] is_alu_imm_by_way_RNM, next_is_alu_imm_by_way_RNM;
	logic [3:0] is_bru_by_way_RNM, next_is_bru_by_way_RNM;
	logic [3:0] is_mdu_by_way_RNM, next_is_mdu_by_way_RNM;
	logic [3:0] is_ldu_by_way_RNM, next_is_ldu_by_way_RNM;
	logic [3:0] is_store_by_way_RNM, next_is_store_by_way_RNM;
	logic [3:0] is_amo_by_way_RNM, next_is_amo_by_way_RNM;
	logic [3:0] is_fence_by_way_RNM, next_is_fence_by_way_RNM;
	logic [3:0] is_sys_by_way_RNM, next_is_sys_by_way_RNM;
	logic [3:0] is_illegal_instr_by_way_RNM, next_is_illegal_instr_by_way_RNM;
	// op
	logic [3:0][3:0]	op_by_way_RNM, next_op_by_way_RNM;
	logic [3:0]     	is_reg_write_by_way_RNM, next_is_reg_write_by_way_RNM;
	// A operand
	logic [3:0][4:0]	A_AR_by_way_RNM, next_A_AR_by_way_RNM;
	logic [3:0]     	A_unneeded_by_way_RNM, next_A_unneeded_by_way_RNM;
	logic [3:0]     	A_is_zero_by_way_RNM, next_A_is_zero_by_way_RNM;
	logic [3:0]     	A_is_ret_ra_by_way_RNM, next_A_is_ret_ra_by_way_RNM;
	// B operand
	logic [3:0][4:0]	B_AR_by_way_RNM, next_B_AR_by_way_RNM;
	logic [3:0]     	B_unneeded_by_way_RNM, next_B_unneeded_by_way_RNM;
	logic [3:0]     	B_is_zero_by_way_RNM, next_B_is_zero_by_way_RNM;
	// dest operand
	logic [3:0][4:0]	dest_AR_by_way_RNM, next_dest_AR_by_way_RNM;
	logic [3:0]     	dest_is_zero_by_way_RNM, next_dest_is_zero_by_way_RNM;
	logic [3:0]     	dest_is_link_ra_by_way_RNM, next_dest_is_link_ra_by_way_RNM;
	// imm
	logic [3:0][19:0] decoder_imm20_by_way_RNM, next_decoder_imm20_by_way_RNM;
	// pred info out
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0]  pred_info_out_by_way_RNM, next_pred_info_out_by_way_RNM;
	logic [3:0]                           missing_pred_by_way_RNM, next_missing_pred_by_way_RNM;
	// ordering
	logic [3:0] wait_for_restart_by_way_RNM, next_wait_for_restart_by_way_RNM;
	logic [3:0] mem_aq_by_way_RNM, next_mem_aq_by_way_RNM;
	logic [3:0] io_aq_by_way_RNM, next_io_aq_by_way_RNM;
	logic [3:0] mem_rl_by_way_RNM, next_mem_rl_by_way_RNM;
	logic [3:0] io_rl_by_way_RNM, next_io_rl_by_way_RNM;
	// faults
	logic [3:0] instr_yield_by_way_RNM, next_instr_yield_by_way_RNM;
	logic [3:0] non_branch_notif_chunk0_by_way_RNM, next_non_branch_notif_chunk0_by_way_RNM;
	logic [3:0] non_branch_notif_chunk1_by_way_RNM, next_non_branch_notif_chunk1_by_way_RNM;
	logic [3:0] restart_on_chunk0_by_way_RNM, next_restart_on_chunk0_by_way_RNM;
	logic [3:0] restart_after_chunk0_by_way_RNM, next_restart_after_chunk0_by_way_RNM;
	logic [3:0] restart_after_chunk1_by_way_RNM, next_restart_after_chunk1_by_way_RNM;
	logic [3:0] unrecoverable_fault_by_way_RNM, next_unrecoverable_fault_by_way_RNM;

	// modules:

	// decoder by way:

		// environment info
		logic [3:0][1:0]  	decoder_env_exec_mode_by_way;
		logic [3:0]       	decoder_env_trap_sfence_by_way;
		logic [3:0]       	decoder_env_trap_wfi_by_way;
		logic [3:0]       	decoder_env_trap_sret_by_way;

		// instr info
		logic [3:0]                          	decoder_uncompressed_by_way;
		logic [3:0][31:0]                    	decoder_instr32_by_way;
		logic [3:0][BTB_PRED_INFO_WIDTH-1:0] 	decoder_pred_info_chunk0_by_way;
		logic [3:0][BTB_PRED_INFO_WIDTH-1:0] 	decoder_pred_info_chunk1_by_way;

		// FU select
		logic [3:0] decoder_is_alu_reg_by_way;
		logic [3:0] decoder_is_alu_imm_by_way;
		logic [3:0] decoder_is_bru_by_way;
		logic [3:0] decoder_is_mdu_by_way;
		logic [3:0] decoder_is_ldu_by_way;
		logic [3:0] decoder_is_store_by_way;
		logic [3:0] decoder_is_amo_by_way;
		logic [3:0] decoder_is_fence_by_way;
		logic [3:0] decoder_is_sys_by_way;
		logic [3:0] decoder_is_illegal_instr_by_way;

		// op
		logic [3:0][3:0]	decoder_op_by_way;
		logic [3:0]     	decoder_is_reg_write_by_way;
		
		// A operand
		logic [3:0][4:0]	decoder_A_AR_by_way;
		logic [3:0]     	decoder_A_unneeded_by_way;
		logic [3:0]     	decoder_A_is_zero_by_way;
		logic [3:0]     	decoder_A_is_ret_ra_by_way;

		// B operand
		logic [3:0][4:0]	decoder_B_AR_by_way;
		logic [3:0]     	decoder_B_unneeded_by_way;
		logic [3:0]     	decoder_B_is_zero_by_way;

		// dest operand
		logic [3:0][4:0]	decoder_dest_AR_by_way;
		logic [3:0]     	decoder_dest_is_zero_by_way;
		logic [3:0]     	decoder_dest_is_link_ra_by_way;

		// imm
		logic [3:0][19:0] decoder_imm20_by_way;

		// pred info out
		logic [3:0][BTB_PRED_INFO_WIDTH-1:0]  decoder_pred_info_out_by_way;
		logic [3:0]                           decoder_missing_pred_by_way;

		// ordering
		logic [3:0] decoder_wait_for_restart_by_way;
		logic [3:0] decoder_mem_aq_by_way;
		logic [3:0] decoder_io_aq_by_way;
		logic [3:0] decoder_mem_rl_by_way;
		logic [3:0] decoder_io_rl_by_way;

		// faults
		logic [3:0] decoder_instr_yield_by_way;
		logic [3:0] decoder_non_branch_notif_chunk0_by_way;
		logic [3:0] decoder_non_branch_notif_chunk1_by_way;
		logic [3:0] decoder_restart_on_chunk0_by_way;
		logic [3:0] decoder_restart_after_chunk0_by_way;
		logic [3:0] decoder_restart_after_chunk1_by_way;
		logic [3:0] decoder_unrecoverable_fault_by_way;

	////////////////
	// RNM Stage: //
	////////////////
		// Rename

	// state:
	logic active_RNM, next_active_RNM;
	logic perform_RNM;

	// control:
	logic stall_RNM;
	logic valid_DISP_from_RNM;

	// RNM/DISP pipeline reg's:

	// modules:

	// free_list:

		// enqueue request
		logic [FREE_LIST_BANK_COUNT-1:0]                  	free_list_enq_req_valid_by_bank;
		logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]	free_list_enq_req_PR_by_bank;

		// enqueue feedback
		logic [FREE_LIST_BANK_COUNT-1:0] 					free_list_enq_resp_ack_by_bank;

		// dequeue request
		logic [FREE_LIST_BANK_COUNT-1:0]                  	free_list_deq_req_valid_by_bank;
		logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]	free_list_deq_req_PR_by_bank;

		// dequeue feedback
		logic [FREE_LIST_BANK_COUNT-1:0]					free_list_deq_resp_ready_by_bank;

	// map_table:

		// 12x read ports
		logic [11:0][LOG_AR_COUNT-1:0]	map_table_read_AR_by_port;
		logic [11:0][LOG_PR_COUNT-1:0]	map_table_read_PR_by_port;

		// 4x write ports
		logic [3:0]                  	map_table_write_valid_by_port;
		logic [3:0][LOG_AR_COUNT-1:0]	map_table_write_AR_by_port;
		logic [3:0][LOG_PR_COUNT-1:0]	map_table_write_PR_by_port;

		// checkpoint save
		logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]	map_table_save_map_table;

		// checkpoint restore
		logic                                 	map_table_restore_valid;
		logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]	map_table_restore_map_table;

	// checkpoint_array:

		// checkpoint save
		logic                                  	checkpoint_array_save_valid;
		logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] 	checkpoint_array_save_map_table;
		logic [LH_LENGTH-1:0]                  	checkpoint_array_save_LH;
		logic [GH_LENGTH-1:0]                  	checkpoint_array_save_GH;
		logic [RAS_INDEX_WIDTH-1:0]            	checkpoint_array_save_ras_index;

		logic                              		checkpoint_array_save_ready;
		logic [CHECKPOINT_INDEX_WIDTH-1:0] 		checkpoint_array_save_index;

		// checkpoint restore
		logic                                 	checkpoint_array_restore_valid;
		logic [CHECKPOINT_INDEX_WIDTH-1:0]    	checkpoint_array_restore_index;

		logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] 	checkpoint_array_restore_map_table;
		logic [LH_LENGTH-1:0]                  	checkpoint_array_restore_LH;
		logic [GH_LENGTH-1:0]                  	checkpoint_array_restore_GH;
		logic [RAS_INDEX_WIDTH-1:0]            	checkpoint_array_restore_ras_index;

		// advertized threshold
		logic checkpoint_array_above_threshold;

	// ar_dep_check:

		// inputs by way
		logic [3:0][4:0]	ar_dep_check_A_AR_by_way;
		logic [3:0][4:0]	ar_dep_check_B_AR_by_way;
		logic [3:0]     	ar_dep_check_regwrite_by_way;
		logic [3:0][4:0]	ar_dep_check_dest_AR_by_way;

		// outputs by way
		logic [3:0]       	ar_dep_check_A_PR_dep_by_way;
		logic [3:0][1:0]  	ar_dep_check_A_PR_sel_by_way;
		logic [3:0]       	ar_dep_check_B_PR_dep_by_way;
		logic [3:0][1:0]  	ar_dep_check_B_PR_sel_by_way;

	/////////////////
	// DISP Stage: //
	/////////////////
		// Dispatch

	// state:
	logic valid_DISP, next_valid_DISP;

	// control:
	logic stall_DISP;

	// pipeline reg's:

	// modules:

	// ready_table:

		// 8x read ports
		logic [7:0][LOG_PR_COUNT-1:0]	ready_table_read_PR_by_port;
		logic [7:0]                     ready_table_read_ready_by_port;

		// 4x set ports
		logic [3:0]                   	ready_table_set_valid_by_port;
		logic [3:0][LOG_PR_COUNT-1:0]   ready_table_set_PR_by_port;

		// 4x clear ports
		logic [3:0]                   	ready_table_clear_valid_by_port;
		logic [3:0][LOG_PR_COUNT-1:0] 	ready_table_clear_PR_by_port;

    // ----------------------------------------------------------------
    // Logic:

	/////////////////
	// SDEQ Stage: //
	/////////////////

	assign stall_SDEQ = stall_DEC;
	assign istream_stall_SDEQ = stall_SDEQ;
	assign valid_DEC_from_SDEQ = istream_valid_SDEQ & ~stall_SDEQ;

	// SDEQ/DEC pipeline reg inputs
	always_comb begin
		next_valid_by_way_DEC = istream_valid_by_way_SDEQ;
		next_uncompressed_by_way_DEC = istream_uncompressed_by_way_SDEQ;
		next_instr_2B_by_way_by_chunk_DEC = istream_instr_2B_by_way_by_chunk_SDEQ;
		next_pred_info_by_way_by_chunk_DEC = istream_pred_info_by_way_by_chunk_SDEQ;
		next_pred_lru_by_way_by_chunk_DEC = istream_pred_lru_by_way_by_chunk_SDEQ;
		next_mdp_info_by_way_DEC = istream_mdp_info_by_way_SDEQ;
		next_PC_by_way_DEC = istream_PC_by_way_SDEQ;
		next_LH_by_way_DEC = istream_LH_by_way_SDEQ;
		next_GH_by_way_DEC = istream_GH_by_way_SDEQ;
		next_ras_index_by_way_DEC = istream_ras_index_by_way_SDEQ;

		for (int way = 0; way < 4; way++) begin
			// use pred PC of upper chunk
			if (istream_uncompressed_by_way_SDEQ[way]) begin
				next_pred_PC_by_way_DEC[way] = istream_pred_PC_by_way_by_chunk_SDEQ[way][1];
			end
			else begin
				next_pred_PC_by_way_DEC[way] = istream_pred_PC_by_way_by_chunk_SDEQ[way][0];
			end

			// reduce page fault and access fault
			next_page_fault_by_way_DEC[way] = |istream_page_fault_by_way_by_chunk_SDEQ[way];
			next_access_fault_by_way_DEC[way] = |istream_access_fault_by_way_by_chunk_SDEQ[way];
		end
	end

	////////////////
	// DEC Stage: //
	////////////////

	// SDEQ/DEC pipeline reg outputs:
	always_ff @ (posedge CLK, negedge nRST) begin
		if (~nRST) begin
			valid_by_way_DEC <= '0;
			uncompressed_by_way_DEC <= '0;
			instr_2B_by_way_by_chunk_DEC <= '0;
			pred_info_by_way_by_chunk_DEC <= '0;
			pred_lru_by_way_by_chunk_DEC <= '0;
			redirect_by_way_by_chunk_DEC <= '0;
			pred_PC_by_way_by_chunk_DEC <= '0;
			page_fault_by_way_by_chunk_DEC <= '0;
			access_fault_by_way_by_chunk_DEC <= '0;
			mdp_info_by_way_DEC <= '0;
			PC_by_way_DEC <= '0;
			LH_by_way_DEC <= '0;
			GH_by_way_DEC <= '0;
			ras_index_by_way_DEC <= '0;
		end
		else if (stall_DEC) begin
			valid_by_way_DEC <= valid_by_way_DEC & ~cancel_by_way_DEC;
			uncompressed_by_way_DEC <= uncompressed_by_way_DEC;
			instr_2B_by_way_by_chunk_DEC <= instr_2B_by_way_by_chunk_DEC;
			pred_info_by_way_by_chunk_DEC <= pred_info_by_way_by_chunk_DEC;
			pred_lru_by_way_by_chunk_DEC <= pred_lru_by_way_by_chunk_DEC;
			pred_PC_by_way_DEC <= pred_PC_by_way_DEC;
			page_fault_by_way_DEC <= page_fault_by_way_DEC;
			access_fault_by_way_DEC <= access_fault_by_way_DEC;
			mdp_info_by_way_DEC <= mdp_info_by_way_DEC;
			PC_by_way_DEC <= PC_by_way_DEC;
			LH_by_way_DEC <= LH_by_way_DEC;
			GH_by_way_DEC <= GH_by_way_DEC;
			ras_index_by_way_DEC <= ras_index_by_way_DEC;
		end
		else begin
			valid_by_way_DEC <= next_valid_by_way_DEC;
			uncompressed_by_way_DEC <= next_uncompressed_by_way_DEC;
			instr_2B_by_way_by_chunk_DEC <= next_instr_2B_by_way_by_chunk_DEC;
			pred_info_by_way_by_chunk_DEC <= next_pred_info_by_way_by_chunk_DEC;
			pred_lru_by_way_by_chunk_DEC <= next_pred_lru_by_way_by_chunk_DEC;
			pred_PC_by_way_DEC <= next_pred_PC_by_way_DEC;
			page_fault_by_way_DEC <= next_page_fault_by_way_DEC;
			access_fault_by_way_DEC <= next_access_fault_by_way_DEC;
			mdp_info_by_way_DEC <= next_mdp_info_by_way_DEC;
			PC_by_way_DEC <= next_PC_by_way_DEC;
			LH_by_way_DEC <= next_LH_by_way_DEC;
			GH_by_way_DEC <= next_GH_by_way_DEC;
			ras_index_by_way_DEC <= next_ras_index_by_way_DEC;
		end
	end

	always_ff @ (posedge CLK, negedge nRST) begin
		if (~nRST) begin
			unrecoverable_fault <= 1'b0;
		end
		else begin
			unrecoverable_fault <= unrecoverable_fault | |decoder_unrecoverable_fault_by_way;
		end
	end

	always_ff @ (posedge CLK, negedge nRST) begin
		if (~nRST) begin
			state_DEC <= DEC_IDLE;
			restart_wfr_saved_index_DEC <= 2'h0;
			restart_wfr_saved_PC_DEC <= 32'h0;

			exec_mode_DEC <= M_MODE;
			trap_sfence_DEC <= INIT_TRAP_SFENCE;
			trap_wfi_DEC <= INIT_TRAP_WFI;
			trap_sret_DEC <= INIT_TRAP_SRET;
		end
		else begin
			// restart short circuits to IDLE
			if (rob_restart_valid) begin
				state_DEC <= next_state_DEC;
			end
			else begin
				state_DEC <= next_state_DEC;
			end

			// save new restart wfr info if currently active
			if (state_DEC == DEC_ACTIVE) begin
				restart_wfr_saved_index_DEC <= next_restart_wfr_saved_index_DEC;
				restart_wfr_saved_branch_notif_PC_DEC <= next_restart_wfr_saved_branch_notif_PC_DEC;
				restart_wfr_saved_restart_PC_DEC <= next_restart_wfr_saved_restart_PC_DEC;
			end

			// update decode state on rob restart
			if (rob_restart_valid) begin
				exec_mode_DEC <= rob_restart_exec_mode;
				trap_sfence_DEC <= rob_restart_trap_sfence;
				trap_wfi_DEC <= rob_restart_trap_wfi;
				trap_sret_DEC <= rob_restart_trap_sret;
			end
		end
	end

	always_comb begin
		cancel_by_way_DEC = 4'b0000;

		next_restart_wfr_saved_index_DEC = 2'h0;
		next_restart_wfr_saved_restart_PC_DEC = PC_by_way_DEC[way];
		next_restart_wfr_saved_branch_notif_PC_DEC = PC_by_way_DEC[way];
		next_restart_wfr_saved_pred_lru_DEC = lru_by

		// iter way 0:3, oldest to youngest checking for restart or wfr
		restart_present_DEC = 1'b0;
		wfr_present_DEC = 1'b0;
		for (int way = 0; way < 4; way++) begin

			if (~restart_present_DEC & ~wfr_present_DEC) begin

				// check restart
				if (valid_by_way_DEC[way]
					& (decoder_restart_on_chunk0_by_way[way]
						| decoder_restart_after_chunk0_by_way[way]
						| decoder_restart_after_chunk1_by_way[way])
				) begin
					restart_present_DEC = 1'b1;
					cancel_by_way_DEC[way] = ~decoder_instr_yield_by_way[way];

					next_restart_wfr_saved_index_DEC = way;

					// set restart PC
					if (decoder_restart_on_chunk0_by_way[way]) begin
						next_restart_wfr_saved_restart_PC_DEC = PC_by_way_DEC[way];
					end
					else if (decoder_restart_after_chunk0_by_way[way]) begin
						next_restart_wfr_saved_restart_PC_DEC = {PC_by_way_DEC + 2}[way];
					end
					else begin
						next_restart_wfr_saved_restart_PC_DEC = {PC_by_way_DEC + 4}[way];
					end
					
					// set branch notif PC
						// guaranteed have branch notif if have restart
					if (decoder_non_branch_notif_chunk0_by_way[way]) begin
						next_restart_wfr_saved_branch_notif_PC_DEC = PC_by_way_DEC[way];
						next_restart_wfr_saved_pred_lru_DEC = pred_lru_by_way_by_chunk_DEC[way][0];
					end
					else begin
						next_restart_wfr_saved_branch_notif_PC_DEC = {PC_by_way_DEC + 2}[way];
						next_restart_wfr_saved_pred_lru_DEC = pred_lru_by_way_by_chunk_DEC[way][1];
					end
				end

				// check wfr
					// also check for illegal instr here
				else if (valid_by_way_DEC[way]
					& (decoder_wait_for_restart_by_way[way]
						| decoder_is_illegal_instr_by_way[way])
				) begin
					wfr_present_DEC = 1'b1;
					next_restart_wfr_saved_index_DEC = way;
					cancel_by_way_DEC[way] = 1'b0;
						// only cancel after wfr
				end

				// check good instr or inv
				else begin
					cancel_by_way_DEC[way] = 1'b0;
				end
			end

			// guaranteed cancel since after restart or wfr
			else begin
				cancel_by_way_DEC[way] = 1'b1;
			end
		end
	end

	// state machine
	always_comb begin

		stall_DEC = 1'b0;
		valid_RNM_from_DEC = 1'b0;
		next_state_DEC = state_DEC;

		decode_unit_restart_valid = 1'b0;
		decode_unit_restart_PC = restart_wfr_saved_restart_PC_DEC;

		decode_unit_trigger_wait_for_restart = 1'b0;

		DEC_decode_unit_branch_update_valid = 1'b0;
		DEC_decode_unit_branch_update_has_checkpoint = 1'b0;
		DEC_decode_unit_branch_update_is_complex = 1'b0;
		DEC_decode_unit_branch_update_use_upct = 1'b0;
		DEC_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		DEC_decode_unit_branch_update_pred_lru = restart_wfr_saved_pred_lru_DEC;
		DEC_decode_unit_branch_update_start_PC = restart_wfr_saved_branch_notif_PC_DEC;

		case (state_DEC)

			DEC_IDLE:
			begin
				// guaranteed no stall nor yield since invalid
				stall_DEC = 1'b0;
				valid_RNM_from_DEC = 1'b0;

				// check for trigger from istream
				if (valid_DEC_from_SDEQ) begin
					next_state_DEC = DEC_ACTIVE;
				end
			end

			DEC_ACTIVE:
			begin
				// check propagate stall and do nothing
					// could do a restart or wfr but wouldn't be able to yield
					// this simplifies restart and wfr functionality tho since can guarantee downstream is open
				if (stall_RNM) begin
					stall_DEC = 1'b1;
					valid_RNM_from_DEC = 1'b0;
					next_state_DEC = DEC_ACTIVE;
				end

				// check for restart
				else if (restart_present_DEC) begin
					stall_DEC = 1'b1;
					valid_RNM_from_DEC = 1'b0;
					next_state_DEC = DEC_RESTART_0;
				end

				// check for wfr
				else if (restart_wfr_present_DEC) begin
					stall_DEC = 1'b1;
					valid_RNM_from_DEC = 1'b0;
					next_state_DEC = DEC_TRIGGER_WFR;
				end

				// otherwise, good yield
				else begin
					stall_DEC = 1'b0;
					valid_RNM_from_DEC = 1'b1;

					// check for trigger from istream
					if (valid_DEC_from_SDEQ) begin
						next_state_DEC = DEC_ACTIVE;
					end
					else begin
						next_state_DEC = DEC_IDLE;
					end
				end
			end
			
			DEC_TRIGGER_WFR:
			begin
				// yield everything before and including WFR'ing instr
					// no stall since had to have been no stall when in DEC_ACTIVE
				stall_DEC = 1'b0;
				valid_RNM_from_DEC = 1'b1;
				next_state_DEC = IDLE;
				
				// send WFR trigger info this cycle
				decode_unit_trigger_wait_for_restart = 1'b1;
			end

			DEC_RESTART_0:
			begin
				// no yield
				stall_DEC = 1'b1;
				valid_RNM_from_DEC = 1'b0;
				next_state_DEC = DEC_RESTART_1;

				// send branch update this cycle
					// this one can be overpowered by rob branch update
				DEC_decode_unit_branch_update_valid = 1'b1;
			end
			
			DEC_RESTART_1:
			begin
				// no yield
				stall_DEC = 1'b1;
				valid_RNM_from_DEC = 1'b0;
				next_state_DEC = DEC_RESTART_1;
			end
			
			DEC_RESTART_2:
			begin
				// yield anything that's left valid
					// no stall since had to have been no stall when in DEC_ACTIVE
				stall_DEC = 1'b0;
				valid_RNM_from_DEC = |valid_by_way_DEC;

				// check for trigger from istream
				if (valid_DEC_from_SDEQ) begin
					next_state_DEC = DEC_ACTIVE;
				end
				else begin
					next_state_DEC = DEC_IDLE;
				end

				// send decode restart this cycle
				decode_unit_restart_valid = 1'b1;
			end

		endcase
	end

	// module connections:
	always_comb begin

		// decoder by way:
		for (int way = 0; way < 4; way++) begin
			decoder_env_exec_mode_by_way[way] = exec_mode_DEC;
			decoder_env_trap_sfence_by_way[way] = trap_sfence_DEC;
			decoder_env_trap_wfi_by_way[way] = trap_wfi_DEC;
			decoder_env_trap_sret_by_way[way] = trap_sret_DEC;

			decoder_uncompressed_by_way[way] = uncompressed_by_way_DEC[way];
			decoder_instr32_by_way[way] = instr_2B_by_way_by_chunk_DEC[way];
			decoder_pred_info_chunk0_by_way[way] = pred_info_by_way_by_chunk_DEC[way][0];
			decoder_pred_info_chunk1_by_way[way] = pred_info_by_way_by_chunk_DEC[way][1];
		end
	end

	// modules:

	genvar decoder_i;
	generate
		for (decoder_i = 0; decoder_i < 4; decoder_i++) begin

			decoder DECODER_I (
				// environment info
				.env_exec_mode(decoder_env_exec_mode_by_way[decoder_i]),
				.env_trap_sfence(decoder_env_trap_sfence_by_way[decoder_i]),
				.env_trap_wfi(decoder_env_trap_wfi_by_way[decoder_i]),
				.env_trap_sret(decoder_env_trap_sret_by_way[decoder_i]),
				// instr info
				.uncompressed(decoder_uncompressed_by_way[decoder_i]),
				.instr32(decoder_instr32_by_way[decoder_i]),
				.pred_info_chunk0(decoder_pred_info_chunk0_by_way[decoder_i]),
				.pred_info_chunk1(decoder_pred_info_chunk1_by_way[decoder_i]),
				// FU select
				.is_alu_reg(decoder_is_alu_reg_by_way[decoder_i]),
				.is_alu_imm(decoder_is_alu_imm_by_way[decoder_i]),
				.is_bru(decoder_is_bru_by_way[decoder_i]),
				.is_mdu(decoder_is_mdu_by_way[decoder_i]),
				.is_ldu(decoder_is_ldu_by_way[decoder_i]),
				.is_store(decoder_is_store_by_way[decoder_i]),
				.is_amo(decoder_is_amo_by_way[decoder_i]),
				.is_fence(decoder_is_fence_by_way[decoder_i]),
				.is_sys(decoder_is_sys_by_way[decoder_i]),
				.is_illegal_instr(decoder_is_illegal_instr_by_way[decoder_i]),
				// op
				.op(decoder_op_by_way[decoder_i]),
				.is_reg_write(decoder_is_reg_write_by_way[decoder_i]),
				// A operand
				.A_AR(decoder_A_AR_by_way[decoder_i]),
				.A_unneeded(decoder_A_unneeded_by_way[decoder_i]),
				.A_is_zero(decoder_A_is_zero_by_way[decoder_i]),
				.A_is_ret_ra(decoder_A_is_ret_ra_by_way[decoder_i]),
				// B operand
				.B_AR(decoder_B_AR_by_way[decoder_i]),
				.B_unneeded(decoder_B_unneeded_by_way[decoder_i]),
				.B_is_zero(decoder_B_is_zero_by_way[decoder_i]),
				// dest operand
				.dest_AR(decoder_dest_AR_by_way[decoder_i]),
				.dest_is_zero(decoder_dest_is_zero_by_way[decoder_i]),
				.dest_is_link_ra(decoder_dest_is_link_ra_by_way[decoder_i]),
				// imm
				.imm20(decoder_imm20_by_way[decoder_i]),
				// pred info out
				.pred_info_out(decoder_pred_info_out_by_way[decoder_i]),
				.missing_pred(decoder_missing_pred_by_way[decoder_i]),
				// ordering
				.wait_for_restart(decoder_wait_for_restart_by_way[decoder_i]),
				.mem_aq(decoder_mem_aq_by_way[decoder_i]),
				.io_aq(decoder_io_aq_by_way[decoder_i]),
				.mem_rl(decoder_mem_rl_by_way[decoder_i]),
				.io_rl(decoder_io_rl_by_way[decoder_i]),
				// faults
				.instr_yield(decoder_instr_yield_by_way[decoder_i]),
				.non_branch_notif_chunk0(decoder_non_branch_notif_chunk0_by_way[decoder_i]),
				.non_branch_notif_chunk1(decoder_non_branch_notif_chunk1_by_way[decoder_i]),
				.restart_on_chunk0(decoder_restart_on_chunk0_by_way[decoder_i]),
				.restart_after_chunk0(decoder_restart_after_chunk0_by_way[decoder_i]),
				.restart_after_chunk1(decoder_restart_after_chunk1_by_way[decoder_i]),
				.unrecoverable_fault(decoder_unrecoverable_fault_by_way[decoder_i])
			);
		end
	endgenerate;

	// DEC/RNM pipeline reg inputs:
	always_comb begin

		// non-decoder:
		next_valid_by_way_RNM = valid_by_way_DEC;
		next_PC_by_way_RNM = PC_by_way_DEC;
		next_pred_PC_by_way_RNM = pred_PC_by_way_DEC;

		// decoder:
		next_is_alu_reg_by_way_RNM = decoder_is_alu_reg_by_way;
		next_is_alu_imm_by_way_RNM = decoder_is_alu_imm_by_way;
		next_is_bru_by_way_RNM = decoder_is_bru_by_way;
		next_is_mdu_by_way_RNM = decoder_is_mdu_by_way;
		next_is_ldu_by_way_RNM = decoder_is_ldu_by_way;
		next_is_store_by_way_RNM = decoder_is_store_by_way;
		next_is_amo_by_way_RNM = decoder_is_amo_by_way;
		next_is_fence_by_way_RNM = decoder_is_fence_by_way;
		next_is_sys_by_way_RNM = decoder_is_sys_by_way;
		next_is_illegal_instr_by_way_RNM = decoder_is_illegal_instr_by_way;

		next_op_by_way_RNM = decoder_op_by_way;
		next_is_reg_write_by_way_RNM = decoder_is_reg_write_by_way;

		next_A_AR_by_way_RNM = decoder_A_AR_by_way;
		next_A_unneeded_by_way_RNM = decoder_A_unneeded_by_way;
		next_A_is_zero_by_way_RNM = decoder_A_is_zero_by_way;
		next_A_is_ret_ra_by_way_RNM = decoder_A_is_ret_ra_by_way;

		next_B_AR_by_way_RNM = decoder_B_AR_by_way;
		next_B_unneeded_by_way_RNM = decoder_B_unneeded_by_way;
		next_B_is_zero_by_way_RNM = decoder_B_is_zero_by_way;

		next_dest_AR_by_way_RNM = decoder_dest_AR_by_way;
		next_dest_is_zero_by_way_RNM = decoder_dest_is_zero_by_way;
		next_dest_is_link_ra_by_way_RNM = decoder_dest_is_link_ra_by_way;

		next_decoder_imm20_by_way_RNM = decoder_imm20_by_way;

		next_pred_info_out_by_way_RNM = decoder_pred_info_out_by_way;
		next_missing_pred_by_way_RNM = decoder_missing_pred_by_way;

		next_wait_for_restart_by_way_RNM = decoder_wait_for_restart_by_way;
		next_mem_aq_by_way_RNM = decoder_mem_aq_by_way;
		next_io_aq_by_way_RNM = decoder_io_aq_by_way;
		next_mem_rl_by_way_RNM = decoder_mem_rl_by_way;
		next_io_rl_by_way_RNM = decoder_io_rl_by_way;
		
		next_instr_yield_by_way_RNM = decoder_instr_yield_by_way;
		next_non_branch_notif_chunk0_by_way_RNM = decoder_non_branch_notif_chunk0_by_way;
		next_non_branch_notif_chunk1_by_way_RNM = decoder_non_branch_notif_chunk1_by_way;
		next_restart_on_chunk0_by_way_RNM = decoder_restart_on_chunk0_by_way;
		next_restart_after_chunk0_by_way_RNM = decoder_restart_after_chunk0_by_way;
		next_restart_after_chunk1_by_way_RNM = decoder_restart_after_chunk1_by_way;
		next_unrecoverable_fault_by_way_RNM = decoder_unrecoverable_fault_by_way;
	end

	////////////////
	// RNM Stage: //
	////////////////

	// DEC/RNM pipeline reg outputs:
	always_ff @ (posedge CLK, negedge nRST) begin
		if (~nRST) begin
			// non-decoder:
			valid_by_way_RNM <= '0;
			PC_by_way_RNM <= '0;
			pred_PC_by_way_RNM <= '0;

			// decoder:
			is_alu_reg_by_way_RNM <= '0;
			is_alu_imm_by_way_RNM <= '0;
			is_bru_by_way_RNM <= '0;
			is_mdu_by_way_RNM <= '0;
			is_ldu_by_way_RNM <= '0;
			is_store_by_way_RNM <= '0;
			is_amo_by_way_RNM <= '0;
			is_fence_by_way_RNM <= '0;
			is_sys_by_way_RNM <= '0;
			is_illegal_instr_by_way_RNM <= '0;

			op_by_way_RNM <= '0;
			is_reg_write_by_way_RNM <= '0;

			A_AR_by_way_RNM <= '0;
			A_unneeded_by_way_RNM <= '0;
			A_is_zero_by_way_RNM <= '0;
			A_is_ret_ra_by_way_RNM <= '0;

			B_AR_by_way_RNM <= '0;
			B_unneeded_by_way_RNM <= '0;
			B_is_zero_by_way_RNM <= '0;

			dest_AR_by_way_RNM <= '0;
			dest_is_zero_by_way_RNM <= '0;
			dest_is_link_ra_by_way_RNM <= '0;

			decoder_imm20_by_way_RNM <= '0;

			pred_info_out_by_way_RNM <= '0;
			missing_pred_by_way_RNM <= '0;

			wait_for_restart_by_way_RNM <= '0;
			mem_aq_by_way_RNM <= '0;
			io_aq_by_way_RNM <= '0;
			mem_rl_by_way_RNM <= '0;
			io_rl_by_way_RNM <= '0;
			
			instr_yield_by_way_RNM <= '0;
			non_branch_notif_chunk0_by_way_RNM <= '0;
			non_branch_notif_chunk1_by_way_RNM <= '0;
			restart_on_chunk0_by_way_RNM <= '0;
			restart_after_chunk0_by_way_RNM <= '0;
			restart_after_chunk1_by_way_RNM <= '0;
			unrecoverable_fault_by_way_RNM <= '0;
		end
		else if (stall_RNM) begin
			// non-decoder:
			valid_by_way_RNM <= valid_by_way_RNM;
			PC_by_way_RNM <= PC_by_way_RNM;
			pred_PC_by_way_RNM <= pred_PC_by_way_RNM;

			// decoder:
			is_alu_reg_by_way_RNM <= is_alu_reg_by_way_RNM;
			is_alu_imm_by_way_RNM <= is_alu_imm_by_way_RNM;
			is_bru_by_way_RNM <= is_bru_by_way_RNM;
			is_mdu_by_way_RNM <= is_mdu_by_way_RNM;
			is_ldu_by_way_RNM <= is_ldu_by_way_RNM;
			is_store_by_way_RNM <= is_store_by_way_RNM;
			is_amo_by_way_RNM <= is_amo_by_way_RNM;
			is_fence_by_way_RNM <= is_fence_by_way_RNM;
			is_sys_by_way_RNM <= is_sys_by_way_RNM;
			is_illegal_instr_by_way_RNM <= is_illegal_instr_by_way_RNM;

			op_by_way_RNM <= op_by_way_RNM;
			is_reg_write_by_way_RNM <= is_reg_write_by_way_RNM;

			A_AR_by_way_RNM <= A_AR_by_way_RNM;
			A_unneeded_by_way_RNM <= A_unneeded_by_way_RNM;
			A_is_zero_by_way_RNM <= A_is_zero_by_way_RNM;
			A_is_ret_ra_by_way_RNM <= A_is_ret_ra_by_way_RNM;

			B_AR_by_way_RNM <= B_AR_by_way_RNM;
			B_unneeded_by_way_RNM <= B_unneeded_by_way_RNM;
			B_is_zero_by_way_RNM <= B_is_zero_by_way_RNM;

			dest_AR_by_way_RNM <= dest_AR_by_way_RNM;
			dest_is_zero_by_way_RNM <= dest_is_zero_by_way_RNM;
			dest_is_link_ra_by_way_RNM <= dest_is_link_ra_by_way_RNM;

			decoder_imm20_by_way_RNM <= decoder_imm20_by_way_RNM;

			pred_info_out_by_way_RNM <= pred_info_out_by_way_RNM;
			missing_pred_by_way_RNM <= missing_pred_by_way_RNM;

			wait_for_restart_by_way_RNM <= wait_for_restart_by_way_RNM;
			mem_aq_by_way_RNM <= mem_aq_by_way_RNM;
			io_aq_by_way_RNM <= io_aq_by_way_RNM;
			mem_rl_by_way_RNM <= mem_rl_by_way_RNM;
			io_rl_by_way_RNM <= io_rl_by_way_RNM;
			
			instr_yield_by_way_RNM <= instr_yield_by_way_RNM;
			non_branch_notif_chunk0_by_way_RNM <= non_branch_notif_chunk0_by_way_RNM;
			non_branch_notif_chunk1_by_way_RNM <= non_branch_notif_chunk1_by_way_RNM;
			restart_on_chunk0_by_way_RNM <= restart_on_chunk0_by_way_RNM;
			restart_after_chunk0_by_way_RNM <= restart_after_chunk0_by_way_RNM;
			restart_after_chunk1_by_way_RNM <= restart_after_chunk1_by_way_RNM;
			unrecoverable_fault_by_way_RNM <= unrecoverable_fault_by_way_RNM;
		end
		else begin
			// non-decoder:
			valid_by_way_RNM <= next_valid_by_way_RNM;
			PC_by_way_RNM <= next_PC_by_way_RNM;
			pred_PC_by_way_RNM <= next_pred_PC_by_way_RNM;

			// decoder:
			is_alu_reg_by_way_RNM <= next_is_alu_reg_by_way_RNM;
			is_alu_imm_by_way_RNM <= next_is_alu_imm_by_way_RNM;
			is_bru_by_way_RNM <= next_is_bru_by_way_RNM;
			is_mdu_by_way_RNM <= next_is_mdu_by_way_RNM;
			is_ldu_by_way_RNM <= next_is_ldu_by_way_RNM;
			is_store_by_way_RNM <= next_is_store_by_way_RNM;
			is_amo_by_way_RNM <= next_is_amo_by_way_RNM;
			is_fence_by_way_RNM <= next_is_fence_by_way_RNM;
			is_sys_by_way_RNM <= next_is_sys_by_way_RNM;
			is_illegal_instr_by_way_RNM <= next_is_illegal_instr_by_way_RNM;

			op_by_way_RNM <= next_op_by_way_RNM;
			is_reg_write_by_way_RNM <= next_is_reg_write_by_way_RNM;

			A_AR_by_way_RNM <= next_A_AR_by_way_RNM;
			A_unneeded_by_way_RNM <= next_A_unneeded_by_way_RNM;
			A_is_zero_by_way_RNM <= next_A_is_zero_by_way_RNM;
			A_is_ret_ra_by_way_RNM <= next_A_is_ret_ra_by_way_RNM;

			B_AR_by_way_RNM <= next_B_AR_by_way_RNM;
			B_unneeded_by_way_RNM <= next_B_unneeded_by_way_RNM;
			B_is_zero_by_way_RNM <= next_B_is_zero_by_way_RNM;

			dest_AR_by_way_RNM <= next_dest_AR_by_way_RNM;
			dest_is_zero_by_way_RNM <= next_dest_is_zero_by_way_RNM;
			dest_is_link_ra_by_way_RNM <= next_dest_is_link_ra_by_way_RNM;

			decoder_imm20_by_way_RNM <= next_decoder_imm20_by_way_RNM;

			pred_info_out_by_way_RNM <= next_pred_info_out_by_way_RNM;
			missing_pred_by_way_RNM <= next_missing_pred_by_way_RNM;

			wait_for_restart_by_way_RNM <= next_wait_for_restart_by_way_RNM;
			mem_aq_by_way_RNM <= next_mem_aq_by_way_RNM;
			io_aq_by_way_RNM <= next_io_aq_by_way_RNM;
			mem_rl_by_way_RNM <= next_mem_rl_by_way_RNM;
			io_rl_by_way_RNM <= next_io_rl_by_way_RNM;
			
			instr_yield_by_way_RNM <= next_instr_yield_by_way_RNM;
			non_branch_notif_chunk0_by_way_RNM <= next_non_branch_notif_chunk0_by_way_RNM;
			non_branch_notif_chunk1_by_way_RNM <= next_non_branch_notif_chunk1_by_way_RNM;
			restart_on_chunk0_by_way_RNM <= next_restart_on_chunk0_by_way_RNM;
			restart_after_chunk0_by_way_RNM <= next_restart_after_chunk0_by_way_RNM;
			restart_after_chunk1_by_way_RNM <= next_restart_after_chunk1_by_way_RNM;
			unrecoverable_fault_by_way_RNM <= next_unrecoverable_fault_by_way_RNM;
		end
	end

	// simple active state + comb modification to say if making arch state modifications and yielding
	always_ff @ (posedge CLK, negedge nRST) begin
		if (~nRST) begin
			active_RNM <= 1'b0;
		end
		else begin
			active_RNM <= next_active_RNM;
		end
	end
	always_comb begin

		// check active state
		if (active_RNM 
			& ~stall_RNM 
			& ~rob_restart_valid 
			& ~rob_controlling_rename
		) begin
			perform_RNM = 1'b1;
		end
		else begin
			perform_RNM = 1'b0;
		end

		// check active next cycle
		if (rob_restart_valid | rob_controlling_rename) begin
			next_active_RNM = 1'b0;
		end
		else if (~stall_RNM & valid_RNM_from_DEC) begin
			next_active_RNM = 1'b1;
		end
		else begin
			next_active_RNM = 1'b0;
		end
	end

	assign stall_RNM = stall_DISP;
	assign valid_DISP_from_RNM = perform_RNM;

	// restart means clear input pipeline reg's and prevent arch state changes

	// rob controlling RNM means prevent arch state changes
		// should be impossible anyway since rob would have restart before
	// and stall RNM since map table not ready for new renames

	// only perform arch state changes on non-restart, non-stall

	// module connections:
	always_comb begin

		// start with only reason to stall being DISP. add reasons as go
		stall_RNM = stall_DISP;

		// free_list:
		free_list_enq_req_valid_by_bank = rob_PR_free_req_valid_by_bank;
		free_list_enq_req_PR_by_bank = rob_PR_free_req_PR_by_bank;
		rob_PR_free_resp_ack_by_bank = free_list_enq_resp_ack_by_bank;

		free_list_deq_req_valid_by_bank = {4{perform_RNM}} 
			& valid_by_way_RNM 
			& is_reg_write_by_way_RNM
			& ~dest_is_zero_by_way_RNM;
		
		// map_table:

		// checkpoint_array:

		// 
	end

	// modules:


	// RNM/DISP pipeline reg inputs:
	always_comb begin

	end

	/////////////////
	// DISP Stage: //
	/////////////////

	// dispatch attempt = type & valid
	// dispatch valid = type & valid & ack_mask 

	// check for stall (and maybe no rob enQ) depending on if dispatch's are ack'd

	// ignore restarts since arch state changes have been made and ROB must undo them

endmodule