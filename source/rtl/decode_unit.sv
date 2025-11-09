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
    output logic                                  	dispatch_rob_enq_valid,
	output logic									dispatch_rob_enq_killed,
    input logic 									dispatch_rob_enq_ready,

    // general instr info
    output logic [3:0]                              dispatch_valid_by_way,
    output logic [3:0]                              dispatch_uncompressed_by_way,
    output logic [3:0][31:0]                        dispatch_PC_by_way,
    output logic [3:0][31:0]                        dispatch_pred_PC_by_way,
    output logic [3:0]                              dispatch_is_rename_by_way,
    output logic [3:0][BTB_PRED_INFO_WIDTH-1:0]		dispatch_pred_info_by_way,
    output logic [3:0]                              dispatch_pred_lru_by_way,
    output logic [3:0][MDPT_INFO_WIDTH-1:0]         dispatch_mdp_info_by_way,
    output logic [3:0][3:0]                         dispatch_op_by_way,
    output logic [3:0][19:0]                       	dispatch_imm20_by_way,

    // ordering
    output logic [3:0]                              dispatch_mem_aq_by_way,
    output logic [3:0]                              dispatch_io_aq_by_way,
    output logic [3:0]                              dispatch_mem_rl_by_way,
    output logic [3:0]                              dispatch_io_rl_by_way,

    // exception info
    output logic                             		dispatch_is_page_fault,
    output logic                             		dispatch_is_access_fault,
    output logic                             		dispatch_is_illegal_instr,
	output logic 									dispatch_exception_present,
	output logic [1:0]								dispatch_exception_index,
    output logic [31:0]                             dispatch_illegal_instr32,

	// checkpoint info
	output logic									dispatch_has_checkpoint,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0]		dispatch_checkpoint_index,

    // instr IQ attempts
    output logic [3:0]                              dispatch_attempt_alu_reg_mdu_dq_by_way,
    output logic [3:0]                              dispatch_attempt_alu_imm_dq_by_way,
    output logic [3:0]                              dispatch_attempt_bru_dq_by_way,
	output logic [3:0]								dispatch_attempt_ldu_dq_by_way,
    output logic [3:0]                              dispatch_attempt_stamofu_dq_by_way,
    output logic [3:0]                              dispatch_attempt_sysu_dq_by_way,

    // instr FU valids
    output logic [3:0]                              dispatch_valid_alu_reg_by_way,
    output logic [3:0]                              dispatch_valid_mdu_by_way,
    output logic [3:0]                              dispatch_valid_alu_imm_by_way,
    output logic [3:0]                              dispatch_valid_bru_by_way,
    output logic [3:0]                              dispatch_valid_ldu_by_way,
    output logic [3:0]                              dispatch_valid_store_by_way,
    output logic [3:0]                              dispatch_valid_amo_by_way,
    output logic [3:0]                              dispatch_valid_fence_by_way,
    output logic [3:0]                              dispatch_valid_sysu_by_way,

    // operand A
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_A_PR_by_way,
    output logic [3:0]                              dispatch_A_ready_by_way,
	output logic [3:0]								dispatch_A_is_zero_by_way,
    output logic [3:0]                              dispatch_A_unneeded_or_is_zero_by_way,
    output logic [3:0]                              dispatch_A_is_ret_ra_by_way,

    // operand B
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_B_PR_by_way,
    output logic [3:0]                              dispatch_B_ready_by_way,
	output logic [3:0]								dispatch_B_is_zero_by_way,
    output logic [3:0]                              dispatch_B_unneeded_or_is_zero_by_way,

    // dest operand
    output logic [3:0][4:0]            				dispatch_dest_AR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_old_PR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_new_PR_by_way,
    output logic [3:0]                              dispatch_dest_is_link_ra_by_way,

    // instr IQ acks
    input logic [3:0] dispatch_ack_alu_reg_mdu_dq_by_way,
    input logic [3:0] dispatch_ack_alu_imm_dq_by_way,
    input logic [3:0] dispatch_ack_bru_dq_by_way,
    input logic [3:0] dispatch_ack_ldu_dq_by_way,
    input logic [3:0] dispatch_ack_stamofu_dq_by_way,
    input logic [3:0] dispatch_ack_sysu_dq_by_way,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // fetch + decode restart from ROB
    input logic       	rob_restart_valid,
    input logic [1:0] 	rob_restart_exec_mode,
    input logic      	rob_restart_trap_sfence,
    input logic      	rob_restart_trap_wfi,
    input logic      	rob_restart_trap_sret,

	// kill from ROB
	input logic rob_kill_valid,

    // branch update from ROB
    input logic                             	rob_branch_update_valid,
    input logic                             	rob_branch_update_has_checkpoint,
	input logic [CHECKPOINT_INDEX_WIDTH-1:0]	rob_branch_update_checkpoint_index,
    input logic                             	rob_branch_update_is_mispredict,
    input logic                             	rob_branch_update_is_taken,
    input logic                             	rob_branch_update_use_upct,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   	rob_branch_update_intermediate_pred_info,
    input logic                             	rob_branch_update_pred_lru,
    input logic [31:0]                      	rob_branch_update_start_PC,
    input logic [31:0]                      	rob_branch_update_target_PC,

    // ROB control of rename
    input logic                             	rob_controlling_rename,

    input logic                                 rob_checkpoint_map_table_restore_valid,
    input logic [CHECKPOINT_INDEX_WIDTH-1:0]    rob_checkpoint_map_table_restore_index,

    input logic                                 rob_checkpoint_clear_valid,
    input logic [CHECKPOINT_INDEX_WIDTH-1:0]    rob_checkpoint_clear_index,

    input logic [3:0]                       	rob_map_table_write_valid_by_port,
    input logic [3:0][LOG_AR_COUNT-1:0]     	rob_map_table_write_AR_by_port,
    input logic [3:0][LOG_PR_COUNT-1:0]     	rob_map_table_write_PR_by_port,

	// ROB physical register freeing
	input logic [3:0]						rob_PR_free_req_valid_by_bank,
	input logic [3:0][LOG_PR_COUNT-1:0]		rob_PR_free_req_PR_by_bank,
	output logic [3:0]						rob_PR_free_resp_ack_by_bank,

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
	logic [3:0][31:0]                   		pred_PC_by_way_DEC, next_pred_PC_by_way_DEC;
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
	logic 			stall_DEC;
	logic 			restart_present_DEC;
	logic 			wfr_present_DEC;
	logic [1:0] 	restart_wfr_saved_index_DEC, next_restart_wfr_saved_index_DEC;
	logic [31:0] 	restart_wfr_saved_branch_notif_PC_DEC, next_restart_wfr_saved_branch_notif_PC_DEC;
	logic [31:0] 	restart_wfr_saved_restart_PC_DEC, next_restart_wfr_saved_restart_PC_DEC;
	logic 			restart_wfr_saved_pred_lru_DEC, next_restart_wfr_saved_pred_lru_DEC;
	logic [3:0] 	cancel_by_way_DEC;

    logic [1:0]		exec_mode_DEC;
    logic      		trap_sfence_DEC;
    logic      		trap_wfi_DEC;
    logic      		trap_sret_DEC;

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
	logic [3:0] 						valid_by_way_RNM, next_valid_by_way_RNM;
	logic [3:0]                        	uncompressed_by_way_RNM, next_uncompressed_by_way_RNM;
	logic [3:0][31:0] 					PC_by_way_RNM, next_PC_by_way_RNM;
	logic [3:0][31:0] 					pred_PC_by_way_RNM, next_pred_PC_by_way_RNM;
	logic [3:0]							pred_lru_by_way_RNM, next_pred_lru_by_way_RNM;
	logic [3:0][MDPT_INFO_WIDTH-1:0]	mdp_info_by_way_RNM, next_mdp_info_by_way_RNM;

	// info to condense
	logic			is_access_fault_RNM, next_is_access_fault_RNM;
	logic			is_page_fault_RNM, next_is_page_fault_RNM;
	logic			is_illegal_instr_RNM, next_is_illegal_instr_RNM;
	logic			exception_present_RNM, next_exception_present_RNM;
	logic [1:0]		exception_index_RNM, next_exception_index_RNM;
	logic [31:0]	illegal_instr32_RNM, next_illegal_instr32_RNM;
	logic [3:0] 	is_exception_by_way_RNM, next_is_exception_by_way_RNM;

	logic								checkpoint_marked_RNM, next_checkpoint_marked_RNM;
	logic [3:0][LH_LENGTH-1:0]      	LH_RNM, next_LH_RNM;
	logic [3:0][GH_LENGTH-1:0]      	GH_RNM, next_GH_RNM;
	logic [3:0][RAS_INDEX_WIDTH-1:0]	ras_index_RNM, next_ras_index_RNM;

	// FU select
	logic [3:0] is_alu_reg_by_way_RNM, next_is_alu_reg_by_way_RNM;
	logic [3:0] is_alu_imm_by_way_RNM, next_is_alu_imm_by_way_RNM;
	logic [3:0] is_bru_by_way_RNM, next_is_bru_by_way_RNM;
	logic [3:0] is_mdu_by_way_RNM, next_is_mdu_by_way_RNM;
	logic [3:0] is_ldu_by_way_RNM, next_is_ldu_by_way_RNM;
	logic [3:0] is_store_by_way_RNM, next_is_store_by_way_RNM;
	logic [3:0] is_amo_by_way_RNM, next_is_amo_by_way_RNM;
	logic [3:0] is_fence_by_way_RNM, next_is_fence_by_way_RNM;
	logic [3:0] is_sysu_by_way_RNM, next_is_sysu_by_way_RNM;
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
	// logic [3:0]     	dest_is_zero_by_way_RNM, next_dest_is_zero_by_way_RNM; // condensed info with is_reg_write_by_way_RNM
	logic [3:0]     	dest_is_link_ra_by_way_RNM, next_dest_is_link_ra_by_way_RNM;
	// imm
	logic [3:0][19:0] 	imm20_by_way_RNM, next_imm20_by_way_RNM;
	// pred info out
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0]  	pred_info_out_by_way_RNM, next_pred_info_out_by_way_RNM;
	// ordering
	logic [3:0] mem_aq_by_way_RNM, next_mem_aq_by_way_RNM;
	logic [3:0] io_aq_by_way_RNM, next_io_aq_by_way_RNM;
	logic [3:0] mem_rl_by_way_RNM, next_mem_rl_by_way_RNM;
	logic [3:0] io_rl_by_way_RNM, next_io_rl_by_way_RNM;

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
		logic [3:0] decoder_is_sysu_by_way;
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
		logic [3:0][BTB_PRED_INFO_WIDTH-1:0]  	decoder_pred_info_out_by_way;
		logic [3:0]								decoder_missing_pred_by_way;

		// ordering
		logic [3:0] decoder_wait_for_restart_by_way;
		logic [3:0] decoder_mem_aq_by_way;
		logic [3:0] decoder_io_aq_by_way;
		logic [3:0] decoder_mem_rl_by_way;
		logic [3:0] decoder_io_rl_by_way;

		// faults
		logic [3:0] decoder_instr_yield_by_way;
		logic [3:0] decoder_non_branch_notif_chunk0_by_way;
		logic [3:0] decoder_non_branch_notif_chunk1_by_way; // unused
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
	logic [3:0] 							valid_by_way_DISP, next_valid_by_way_DISP;
	logic [3:0]                            	uncompressed_by_way_DISP, next_uncompressed_by_way_DISP;
	logic [3:0][31:0] 						PC_by_way_DISP, next_PC_by_way_DISP;
	logic [3:0][31:0] 						pred_PC_by_way_DISP, next_pred_PC_by_way_DISP;
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0]	pred_info_by_way_DISP, next_pred_info_by_way_DISP;
	logic [3:0]								pred_lru_by_way_DISP, next_pred_lru_by_way_DISP;
	logic [3:0][MDPT_INFO_WIDTH-1:0]		mdp_info_by_way_DISP, next_mdp_info_by_way_DISP;

	logic			is_access_fault_DISP, next_is_access_fault_DISP;
	logic			is_page_fault_DISP, next_is_page_fault_DISP;
	logic			is_illegal_instr_DISP, next_is_illegal_instr_DISP;
	logic			exception_present_DISP, next_exception_present_DISP;
	logic [1:0]		exception_index_DISP, next_exception_index_DISP;
	logic [31:0]	illegal_instr32_DISP, next_illegal_instr32_DISP;
	logic [3:0] 	is_exception_by_way_DISP, next_is_exception_by_way_DISP;

	logic 								checkpoint_saved_DISP, next_checkpoint_saved_DISP;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] 	checkpoint_saved_index_DISP, next_checkpoint_saved_index_DISP;

	logic [3:0] is_alu_reg_by_way_DISP, next_is_alu_reg_by_way_DISP;
	logic [3:0] is_alu_imm_by_way_DISP, next_is_alu_imm_by_way_DISP;
	logic [3:0] is_bru_by_way_DISP, next_is_bru_by_way_DISP;
	logic [3:0] is_mdu_by_way_DISP, next_is_mdu_by_way_DISP;
	logic [3:0] is_ldu_by_way_DISP, next_is_ldu_by_way_DISP;
	logic [3:0] is_store_by_way_DISP, next_is_store_by_way_DISP;
	logic [3:0] is_amo_by_way_DISP, next_is_amo_by_way_DISP;
	logic [3:0] is_fence_by_way_DISP, next_is_fence_by_way_DISP;
	logic [3:0] is_sysu_by_way_DISP, next_is_sysu_by_way_DISP;

	logic [3:0][3:0]	op_by_way_DISP, next_op_by_way_DISP;
	logic [3:0]     	is_reg_write_by_way_DISP, next_is_reg_write_by_way_DISP;
	
	logic [3:0][LOG_PR_COUNT-1:0]	A_PR_by_way_DISP, next_A_PR_by_way_DISP;
	logic [3:0]     				A_unneeded_by_way_DISP, next_A_unneeded_by_way_DISP;
	logic [3:0]     				A_is_zero_by_way_DISP, next_A_is_zero_by_way_DISP;
	logic [3:0]     				A_is_ret_ra_by_way_DISP, next_A_is_ret_ra_by_way_DISP;
	
	logic [3:0][LOG_PR_COUNT-1:0]	B_PR_by_way_DISP, next_B_PR_by_way_DISP;
	logic [3:0]     				B_unneeded_by_way_DISP, next_B_unneeded_by_way_DISP;
	logic [3:0]     				B_is_zero_by_way_DISP, next_B_is_zero_by_way_DISP;

	logic [3:0][4:0]				dest_AR_by_way_DISP, next_dest_AR_by_way_DISP;
	logic [3:0][LOG_PR_COUNT-1:0]	dest_old_PR_by_way_DISP, next_dest_old_PR_by_way_DISP;
	logic [3:0][LOG_PR_COUNT-1:0]	dest_new_PR_by_way_DISP, next_dest_new_PR_by_way_DISP;
	logic [3:0]     				dest_is_link_ra_by_way_DISP, next_dest_is_link_ra_by_way_DISP;
	
	logic [3:0][19:0] 	imm20_by_way_DISP, next_imm20_by_way_DISP;

	logic [3:0] mem_aq_by_way_DISP, next_mem_aq_by_way_DISP;
	logic [3:0] io_aq_by_way_DISP, next_io_aq_by_way_DISP;
	logic [3:0] mem_rl_by_way_DISP, next_mem_rl_by_way_DISP;
	logic [3:0] io_rl_by_way_DISP, next_io_rl_by_way_DISP;

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

		// map table restore
		logic [CHECKPOINT_INDEX_WIDTH-1:0]    	checkpoint_array_map_table_restore_index;
		logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]  checkpoint_array_map_table_restore_map_table;

		// branch info restore
		logic [CHECKPOINT_INDEX_WIDTH-1:0]	checkpoint_array_branch_info_restore_index;
		logic [LH_LENGTH-1:0]              	checkpoint_array_branch_info_restore_LH;
		logic [GH_LENGTH-1:0]           	checkpoint_array_branch_info_restore_GH;
		logic [RAS_INDEX_WIDTH-1:0]        	checkpoint_array_branch_info_restore_ras_index;

		// checkpoint clear
		logic                             	checkpoint_array_clear_valid;
    	logic [CHECKPOINT_INDEX_WIDTH-1:0]	checkpoint_array_clear_index;

		// // checkpoint restore
		// logic [CHECKPOINT_INDEX_WIDTH-1:0]    	checkpoint_array_restore_index;
		// logic                                 	checkpoint_array_restore_clear;

		// logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] 	checkpoint_array_restore_map_table;
		// logic [LH_LENGTH-1:0]                  	checkpoint_array_restore_LH;
		// logic [GH_LENGTH-1:0]                  	checkpoint_array_restore_GH;
		// logic [RAS_INDEX_WIDTH-1:0]            	checkpoint_array_restore_ras_index;

		// advertized threshold
		logic checkpoint_array_above_threshold; // unused for now

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
		logic [3:0]       	ar_dep_check_dest_PR_dep_by_way;
		logic [3:0][1:0]  	ar_dep_check_dest_PR_sel_by_way;

	/////////////////
	// DISP Stage: //
	/////////////////
		// Dispatch

	// state:
	logic active_DISP, next_active_DISP;
	logic perform_DISP;
	logic killed_DISP, next_killed_DISP;

	// control:
	logic stall_DISP;

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
			// reduce page fault and access fault
			if (istream_uncompressed_by_way_SDEQ[way]) begin
				next_pred_PC_by_way_DEC[way] = istream_pred_PC_by_way_by_chunk_SDEQ[way][1];
				next_page_fault_by_way_DEC[way] = |istream_page_fault_by_way_by_chunk_SDEQ[way];
				next_access_fault_by_way_DEC[way] = |istream_access_fault_by_way_by_chunk_SDEQ[way];
			end
			else begin
				next_pred_PC_by_way_DEC[way] = istream_pred_PC_by_way_by_chunk_SDEQ[way][0];
				next_page_fault_by_way_DEC[way] = istream_page_fault_by_way_by_chunk_SDEQ[way][0];
				next_access_fault_by_way_DEC[way] = istream_access_fault_by_way_by_chunk_SDEQ[way][0];
			end
		end
	end

	////////////////
	// DEC Stage: //
	////////////////

	// SDEQ/DEC pipeline reg outputs:
	// always_ff @ (posedge CLK, negedge nRST) begin
	always_ff @ (posedge CLK) begin
		if (~nRST) begin
			valid_by_way_DEC <= '0;
			uncompressed_by_way_DEC <= '0;
			instr_2B_by_way_by_chunk_DEC <= '0;
			pred_info_by_way_by_chunk_DEC <= '0;
			pred_lru_by_way_by_chunk_DEC <= '0;
			pred_PC_by_way_DEC <= '0;
			page_fault_by_way_DEC <= '0;
			access_fault_by_way_DEC <= '0;
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

	// always_ff @ (posedge CLK, negedge nRST) begin
	always_ff @ (posedge CLK) begin
		if (~nRST) begin
			unrecoverable_fault <= 1'b0;
		end
		else begin
			unrecoverable_fault <= (state_DEC == DEC_ACTIVE) & |decoder_unrecoverable_fault_by_way;
		end
	end

	// always_ff @ (posedge CLK, negedge nRST) begin
	always_ff @ (posedge CLK) begin
		if (~nRST) begin
			state_DEC <= DEC_IDLE;

			restart_wfr_saved_index_DEC <= 2'h0;
			restart_wfr_saved_branch_notif_PC_DEC <= 32'h0;
			restart_wfr_saved_restart_PC_DEC <= 32'h0;
			restart_wfr_saved_pred_lru_DEC <= 1'b0;

			exec_mode_DEC <= M_MODE;
			trap_sfence_DEC <= INIT_TRAP_SFENCE;
			trap_wfi_DEC <= INIT_TRAP_WFI;
			trap_sret_DEC <= INIT_TRAP_SRET;
		end
		else begin
			// restart short circuits to IDLE
			if (rob_restart_valid) begin
				state_DEC <= DEC_IDLE;
			end
			else begin
				state_DEC <= next_state_DEC;
			end

			// save new restart wfr info if currently active
			if (state_DEC == DEC_ACTIVE) begin
				restart_wfr_saved_index_DEC <= next_restart_wfr_saved_index_DEC;
				restart_wfr_saved_branch_notif_PC_DEC <= next_restart_wfr_saved_branch_notif_PC_DEC;
				restart_wfr_saved_restart_PC_DEC <= next_restart_wfr_saved_restart_PC_DEC;
				restart_wfr_saved_pred_lru_DEC <= next_restart_wfr_saved_pred_lru_DEC;
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
		next_restart_wfr_saved_restart_PC_DEC = PC_by_way_DEC[0];
		next_restart_wfr_saved_branch_notif_PC_DEC = PC_by_way_DEC[0];
		next_restart_wfr_saved_pred_lru_DEC = pred_lru_by_way_by_chunk_DEC[0][0];

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
						next_restart_wfr_saved_restart_PC_DEC = PC_by_way_DEC[way] + 32'h2;
					end
					else begin
						next_restart_wfr_saved_restart_PC_DEC = PC_by_way_DEC[way] + 32'h4;
					end
					
					// set branch notif PC
						// guaranteed have branch notif if have restart
					if (decoder_non_branch_notif_chunk0_by_way[way]) begin
						next_restart_wfr_saved_branch_notif_PC_DEC = PC_by_way_DEC[way];
						next_restart_wfr_saved_pred_lru_DEC = pred_lru_by_way_by_chunk_DEC[way][0];
					end
					else begin
						next_restart_wfr_saved_branch_notif_PC_DEC = PC_by_way_DEC[way] + 32'h2;
						next_restart_wfr_saved_pred_lru_DEC = pred_lru_by_way_by_chunk_DEC[way][1];
					end
				end

				// check wfr
					// also check for exceptions here
						// illegal instr
						// page fault
						// access fault
				else if (valid_by_way_DEC[way]
					& (decoder_wait_for_restart_by_way[way]
						| decoder_is_illegal_instr_by_way[way]
						| page_fault_by_way_DEC[way]
						| access_fault_by_way_DEC[way])
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
				else if (wfr_present_DEC) begin
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

				// check for trigger from istream
				if (valid_DEC_from_SDEQ) begin
					next_state_DEC = DEC_ACTIVE;
				end
				else begin
					next_state_DEC = DEC_IDLE;
				end
				
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
				next_state_DEC = DEC_RESTART_2;
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
		decoder_uncompressed_by_way = uncompressed_by_way_DEC;
		decoder_instr32_by_way = instr_2B_by_way_by_chunk_DEC;

		for (int way = 0; way < 4; way++) begin
			decoder_env_exec_mode_by_way[way] = exec_mode_DEC;
			decoder_env_trap_sfence_by_way[way] = trap_sfence_DEC;
			decoder_env_trap_wfi_by_way[way] = trap_wfi_DEC;
			decoder_env_trap_sret_by_way[way] = trap_sret_DEC;

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
				.is_sysu(decoder_is_sysu_by_way[decoder_i]),
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
		next_uncompressed_by_way_RNM = uncompressed_by_way_DEC;
		next_PC_by_way_RNM = PC_by_way_DEC;
		next_pred_PC_by_way_RNM = pred_PC_by_way_DEC;
		next_mdp_info_by_way_RNM = mdp_info_by_way_DEC;
		for (int way = 0; way < 4; way++) begin
			if (uncompressed_by_way_DEC[way]) begin
				next_pred_lru_by_way_RNM[way] = pred_lru_by_way_by_chunk_DEC[way][1];
			end
			else begin
				next_pred_lru_by_way_RNM[way] = pred_lru_by_way_by_chunk_DEC[way][0];
			end
		end
		
		next_is_access_fault_RNM = 1'b0;
		next_is_page_fault_RNM = 1'b0;
		next_is_illegal_instr_RNM = 1'b0;
		next_exception_present_RNM = 1'b0;
		next_exception_index_RNM = 2'h0;
		next_illegal_instr32_RNM = instr_2B_by_way_by_chunk_DEC[0];
		for (int way = 0; way < 4; way++) begin
			if (~next_exception_present_RNM & valid_by_way_DEC[way]) begin
				// exception priority order: access fault > page fault > illegal instr
				if (access_fault_by_way_DEC[way]) begin
					next_is_access_fault_RNM = 1'b1;
					next_exception_present_RNM = 1'b1;
					next_exception_index_RNM = way;
				end
				else if (page_fault_by_way_DEC[way]) begin
					next_is_page_fault_RNM = 1'b1;
					next_exception_present_RNM = 1'b1;
					next_exception_index_RNM = way;
				end
				else if (decoder_is_illegal_instr_by_way[way]) begin
					next_is_illegal_instr_RNM = 1'b1;
					next_exception_present_RNM = 1'b1;
					next_exception_index_RNM = way;
					next_illegal_instr32_RNM[15:0] = instr_2B_by_way_by_chunk_DEC[way][0];
					if (uncompressed_by_way_DEC[way]) begin
						next_illegal_instr32_RNM[31:16] = instr_2B_by_way_by_chunk_DEC[way][1];
					end
					else begin
						next_illegal_instr32_RNM[31:16] = 16'h0;
					end
				end
			end
		end

		// mark single oldest instr in 4-way for checkpoint
			// maybe want to improve this to allow checkpoints from multiple instr's in same 4-way 
			// OR launch multiple 4-way's
			// not considering checkpoint count threshold right now
		next_checkpoint_marked_RNM = 1'b0;
		next_LH_RNM = LH_by_way_DEC[0];
		next_GH_RNM = GH_by_way_DEC[0];
		next_ras_index_RNM = ras_index_by_way_DEC[0];
		for (int way = 0; way < 4; way++) begin
			if (~next_checkpoint_marked_RNM) begin
				if (valid_by_way_DEC[way] 
					& (
						decoder_missing_pred_by_way[way]
						| decoder_pred_info_out_by_way[way][7:6] == 2'b11)
				) begin
					next_checkpoint_marked_RNM = 1'b1;
					next_LH_RNM = LH_by_way_DEC[way];
					next_GH_RNM = GH_by_way_DEC[way];
					next_ras_index_RNM = ras_index_by_way_DEC[way];
				end
			end
		end

		// decoder:
		next_is_exception_by_way_RNM = valid_by_way_DEC
			& (access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
			
		next_is_alu_reg_by_way_RNM = decoder_is_alu_reg_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_alu_imm_by_way_RNM = decoder_is_alu_imm_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_bru_by_way_RNM = decoder_is_bru_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_mdu_by_way_RNM = decoder_is_mdu_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_ldu_by_way_RNM = decoder_is_ldu_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_store_by_way_RNM = decoder_is_store_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_amo_by_way_RNM = decoder_is_amo_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_fence_by_way_RNM = decoder_is_fence_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);
		next_is_sysu_by_way_RNM = decoder_is_sysu_by_way
			& valid_by_way_DEC
			& ~(access_fault_by_way_DEC | page_fault_by_way_DEC | decoder_is_illegal_instr_by_way);

		next_op_by_way_RNM = decoder_op_by_way;
		next_is_reg_write_by_way_RNM = decoder_is_reg_write_by_way & ~decoder_dest_is_zero_by_way;
			// true reg write only if dest not r0

		next_A_AR_by_way_RNM = decoder_A_AR_by_way;
		next_A_unneeded_by_way_RNM = decoder_A_unneeded_by_way;
		next_A_is_zero_by_way_RNM = decoder_A_is_zero_by_way;
		next_A_is_ret_ra_by_way_RNM = decoder_A_is_ret_ra_by_way;

		next_B_AR_by_way_RNM = decoder_B_AR_by_way;
		next_B_unneeded_by_way_RNM = decoder_B_unneeded_by_way;
		next_B_is_zero_by_way_RNM = decoder_B_is_zero_by_way;

		next_dest_AR_by_way_RNM = decoder_dest_AR_by_way;
		// next_dest_is_zero_by_way_RNM = decoder_dest_is_zero_by_way;
		next_dest_is_link_ra_by_way_RNM = decoder_dest_is_link_ra_by_way;

		next_imm20_by_way_RNM = decoder_imm20_by_way;

		next_pred_info_out_by_way_RNM = decoder_pred_info_out_by_way;

		next_mem_aq_by_way_RNM = decoder_mem_aq_by_way;
		next_io_aq_by_way_RNM = decoder_io_aq_by_way;
		next_mem_rl_by_way_RNM = decoder_mem_rl_by_way;
		next_io_rl_by_way_RNM = decoder_io_rl_by_way;
	end

	////////////////
	// RNM Stage: //
	////////////////

	// DEC/RNM pipeline reg outputs:
	// always_ff @ (posedge CLK, negedge nRST) begin
	always_ff @ (posedge CLK) begin
		if (~nRST) begin
			// non-decoder:
			valid_by_way_RNM <= '0;
			uncompressed_by_way_RNM <= '0;
			PC_by_way_RNM <= '0;
			pred_PC_by_way_RNM <= '0;
			pred_lru_by_way_RNM <= '0;
			mdp_info_by_way_RNM <= '0;
			
			is_access_fault_RNM <= '0;
			is_page_fault_RNM <= '0;
			is_illegal_instr_RNM <= '0;
			exception_present_RNM <= '0;
			exception_index_RNM <= '0;
			illegal_instr32_RNM <= '0;
			is_exception_by_way_RNM <= '0;

			checkpoint_marked_RNM <= '0;
			LH_RNM <= '0;
			GH_RNM <= '0;
			ras_index_RNM <= '0;

			// decoder:
			is_alu_reg_by_way_RNM <= '0;
			is_alu_imm_by_way_RNM <= '0;
			is_bru_by_way_RNM <= '0;
			is_mdu_by_way_RNM <= '0;
			is_ldu_by_way_RNM <= '0;
			is_store_by_way_RNM <= '0;
			is_amo_by_way_RNM <= '0;
			is_fence_by_way_RNM <= '0;
			is_sysu_by_way_RNM <= '0;

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
			// dest_is_zero_by_way_RNM <= '0;
			dest_is_link_ra_by_way_RNM <= '0;

			imm20_by_way_RNM <= '0;

			pred_info_out_by_way_RNM <= '0;

			mem_aq_by_way_RNM <= '0;
			io_aq_by_way_RNM <= '0;
			mem_rl_by_way_RNM <= '0;
			io_rl_by_way_RNM <= '0;
		end
		else if (stall_RNM) begin
			// non-decoder:
			valid_by_way_RNM <= valid_by_way_RNM;
			uncompressed_by_way_RNM <= uncompressed_by_way_RNM;
			PC_by_way_RNM <= PC_by_way_RNM;
			pred_PC_by_way_RNM <= pred_PC_by_way_RNM;
			pred_lru_by_way_RNM <= pred_lru_by_way_RNM;
			mdp_info_by_way_RNM <= mdp_info_by_way_RNM;
			
			is_access_fault_RNM <= is_access_fault_RNM;
			is_page_fault_RNM <= is_page_fault_RNM;
			is_illegal_instr_RNM <= is_illegal_instr_RNM;
			exception_present_RNM <= exception_present_RNM;
			exception_index_RNM <= exception_index_RNM;
			illegal_instr32_RNM <= illegal_instr32_RNM;
			is_exception_by_way_RNM <= is_exception_by_way_RNM;

			checkpoint_marked_RNM <= checkpoint_marked_RNM;
			LH_RNM <= LH_RNM;
			GH_RNM <= GH_RNM;
			ras_index_RNM <= ras_index_RNM;

			// decoder:
			is_alu_reg_by_way_RNM <= is_alu_reg_by_way_RNM;
			is_alu_imm_by_way_RNM <= is_alu_imm_by_way_RNM;
			is_bru_by_way_RNM <= is_bru_by_way_RNM;
			is_mdu_by_way_RNM <= is_mdu_by_way_RNM;
			is_ldu_by_way_RNM <= is_ldu_by_way_RNM;
			is_store_by_way_RNM <= is_store_by_way_RNM;
			is_amo_by_way_RNM <= is_amo_by_way_RNM;
			is_fence_by_way_RNM <= is_fence_by_way_RNM;
			is_sysu_by_way_RNM <= is_sysu_by_way_RNM;

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
			// dest_is_zero_by_way_RNM <= dest_is_zero_by_way_RNM;
			dest_is_link_ra_by_way_RNM <= dest_is_link_ra_by_way_RNM;

			imm20_by_way_RNM <= imm20_by_way_RNM;

			pred_info_out_by_way_RNM <= pred_info_out_by_way_RNM;

			mem_aq_by_way_RNM <= mem_aq_by_way_RNM;
			io_aq_by_way_RNM <= io_aq_by_way_RNM;
			mem_rl_by_way_RNM <= mem_rl_by_way_RNM;
			io_rl_by_way_RNM <= io_rl_by_way_RNM;
		end
		else begin
			// non-decoder:
			valid_by_way_RNM <= next_valid_by_way_RNM;
			uncompressed_by_way_RNM <= next_uncompressed_by_way_RNM;
			PC_by_way_RNM <= next_PC_by_way_RNM;
			pred_PC_by_way_RNM <= next_pred_PC_by_way_RNM;
			pred_lru_by_way_RNM <= next_pred_lru_by_way_RNM;
			mdp_info_by_way_RNM <= next_mdp_info_by_way_RNM;
			
			is_access_fault_RNM <= next_is_access_fault_RNM;
			is_page_fault_RNM <= next_is_page_fault_RNM;
			is_illegal_instr_RNM <= next_is_illegal_instr_RNM;
			exception_present_RNM <= next_exception_present_RNM;
			exception_index_RNM <= next_exception_index_RNM;
			illegal_instr32_RNM <= next_illegal_instr32_RNM;
			is_exception_by_way_RNM <= next_is_exception_by_way_RNM;

			checkpoint_marked_RNM <= next_checkpoint_marked_RNM;
			LH_RNM <= next_LH_RNM;
			GH_RNM <= next_GH_RNM;
			ras_index_RNM <= next_ras_index_RNM;

			// decoder:
			is_alu_reg_by_way_RNM <= next_is_alu_reg_by_way_RNM;
			is_alu_imm_by_way_RNM <= next_is_alu_imm_by_way_RNM;
			is_bru_by_way_RNM <= next_is_bru_by_way_RNM;
			is_mdu_by_way_RNM <= next_is_mdu_by_way_RNM;
			is_ldu_by_way_RNM <= next_is_ldu_by_way_RNM;
			is_store_by_way_RNM <= next_is_store_by_way_RNM;
			is_amo_by_way_RNM <= next_is_amo_by_way_RNM;
			is_fence_by_way_RNM <= next_is_fence_by_way_RNM;
			is_sysu_by_way_RNM <= next_is_sysu_by_way_RNM;

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
			// dest_is_zero_by_way_RNM <= next_dest_is_zero_by_way_RNM;
			dest_is_link_ra_by_way_RNM <= next_dest_is_link_ra_by_way_RNM;

			imm20_by_way_RNM <= next_imm20_by_way_RNM;

			pred_info_out_by_way_RNM <= next_pred_info_out_by_way_RNM;

			mem_aq_by_way_RNM <= next_mem_aq_by_way_RNM;
			io_aq_by_way_RNM <= next_io_aq_by_way_RNM;
			mem_rl_by_way_RNM <= next_mem_rl_by_way_RNM;
			io_rl_by_way_RNM <= next_io_rl_by_way_RNM;
		end
	end

	// simple active state + comb modification to say if making arch state modifications and yielding
	// always_ff @ (posedge CLK, negedge nRST) begin
	always_ff @ (posedge CLK) begin
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
		else if (active_RNM & stall_RNM) begin
			next_active_RNM = 1'b1;
		end
		else if (~stall_RNM & valid_RNM_from_DEC) begin
			next_active_RNM = 1'b1;
		end
		else begin
			next_active_RNM = 1'b0;
		end
	end

	assign valid_DISP_from_RNM = perform_RNM;

	// restart means clear input pipeline reg's and prevent arch state changes

	// rob controlling RNM means prevent arch state changes
		// should be impossible anyway since rob would have restart before
	// and stall RNM since map table not ready for new renames

	// only perform arch state changes on non-restart, non-stall

	// module connections:
	always_comb begin

		// start with only reason to stall being DISP. add reasons as go
		stall_RNM = stall_DISP & active_RNM;

		// free_list:
		free_list_enq_req_valid_by_bank = rob_PR_free_req_valid_by_bank;
		free_list_enq_req_PR_by_bank = rob_PR_free_req_PR_by_bank;
		rob_PR_free_resp_ack_by_bank = free_list_enq_resp_ack_by_bank;

		free_list_deq_req_valid_by_bank = 
			{4{perform_RNM}} 
			& valid_by_way_RNM 
			& is_reg_write_by_way_RNM;

		// stall RNM if not all free list deq's ready
		if (active_RNM &
			~&(free_list_deq_resp_ready_by_bank 
				| ~(valid_by_way_RNM 
					& is_reg_write_by_way_RNM))
		) begin
			stall_RNM = 1'b1;
		end
		
		// map_table:
		map_table_read_AR_by_port[3:0] = A_AR_by_way_RNM;
		map_table_read_AR_by_port[7:4] = B_AR_by_way_RNM;
		map_table_read_AR_by_port[11:8] = dest_AR_by_way_RNM;

		if (rob_controlling_rename) begin
			map_table_write_valid_by_port = rob_map_table_write_valid_by_port;
			map_table_write_AR_by_port = rob_map_table_write_AR_by_port;
			map_table_write_PR_by_port = rob_map_table_write_PR_by_port;
		end
		else begin
			map_table_write_valid_by_port = 
				{4{perform_RNM}}
				& valid_by_way_RNM
				& is_reg_write_by_way_RNM;
			map_table_write_AR_by_port = dest_AR_by_way_RNM;
			map_table_write_PR_by_port = free_list_deq_req_PR_by_bank;
		end

		map_table_restore_valid = rob_checkpoint_map_table_restore_valid;
		map_table_restore_map_table = checkpoint_array_map_table_restore_map_table;

		// checkpoint_array:
		checkpoint_array_save_valid = 
			perform_RNM
			& checkpoint_array_save_ready
			& checkpoint_marked_RNM;
		checkpoint_array_save_map_table = map_table_save_map_table;
		checkpoint_array_save_LH = LH_RNM;
		checkpoint_array_save_GH = GH_RNM;
		checkpoint_array_save_ras_index = ras_index_RNM;

		checkpoint_array_map_table_restore_index = rob_checkpoint_map_table_restore_index;

		checkpoint_array_branch_info_restore_index = rob_branch_update_checkpoint_index;

		checkpoint_array_clear_valid = rob_checkpoint_clear_valid;
		checkpoint_array_clear_index = rob_checkpoint_clear_index;

		// ar_dep_check:
		ar_dep_check_A_AR_by_way = A_AR_by_way_RNM;
		ar_dep_check_B_AR_by_way = B_AR_by_way_RNM;
		ar_dep_check_regwrite_by_way = 
			valid_by_way_RNM 
			& is_reg_write_by_way_RNM;
		ar_dep_check_dest_AR_by_way = dest_AR_by_way_RNM;
	end

	// branch update logic
		// handle rob vs. DEC branch update here
	always_comb begin

		// shared or don't care for DEC branch update
		decode_unit_branch_update_valid = rob_branch_update_valid | DEC_decode_unit_branch_update_valid;
		decode_unit_branch_update_is_mispredict = rob_branch_update_is_mispredict;
		decode_unit_branch_update_is_taken = rob_branch_update_is_taken;
		decode_unit_branch_update_target_PC = rob_branch_update_target_PC;
		decode_unit_branch_update_LH = checkpoint_array_branch_info_restore_LH;
		decode_unit_branch_update_GH = checkpoint_array_branch_info_restore_GH;
		decode_unit_branch_update_ras_index = checkpoint_array_branch_info_restore_ras_index;

		// rob branch update
		if (rob_branch_update_valid) begin
			decode_unit_branch_update_has_checkpoint = rob_branch_update_has_checkpoint;
			decode_unit_branch_update_is_complex = rob_branch_update_intermediate_pred_info[7:6] == 2'b11;
			decode_unit_branch_update_use_upct = rob_branch_update_use_upct;
			decode_unit_branch_update_intermediate_pred_info = rob_branch_update_intermediate_pred_info;
			decode_unit_branch_update_pred_lru = rob_branch_update_pred_lru;
			decode_unit_branch_update_start_PC = rob_branch_update_start_PC;
		end
		
		// DEC branch update
		else begin
			decode_unit_branch_update_has_checkpoint = DEC_decode_unit_branch_update_has_checkpoint;
			decode_unit_branch_update_is_complex = DEC_decode_unit_branch_update_is_complex;
			decode_unit_branch_update_use_upct = DEC_decode_unit_branch_update_use_upct;
			decode_unit_branch_update_intermediate_pred_info = DEC_decode_unit_branch_update_intermediate_pred_info;
			decode_unit_branch_update_pred_lru = DEC_decode_unit_branch_update_pred_lru;
			decode_unit_branch_update_start_PC = DEC_decode_unit_branch_update_start_PC;
		end
	end

	// modules:

	free_list #(
		.FREE_LIST_BANK_COUNT(FREE_LIST_BANK_COUNT),
		.LOG_FREE_LIST_BANK_COUNT(LOG_FREE_LIST_BANK_COUNT),
		.FREE_LIST_LENGTH_PER_BANK(FREE_LIST_LENGTH_PER_BANK),
		.LOG_FREE_LIST_LENGTH_PER_BANK(LOG_FREE_LIST_LENGTH_PER_BANK),
		.FREE_LIST_SHIFT_REG_ENTRIES(FREE_LIST_SHIFT_REG_ENTRIES),
		.FREE_LIST_LOWER_THRESHOLD(FREE_LIST_LOWER_THRESHOLD),
		.FREE_LIST_UPPER_THRESHOLD(FREE_LIST_UPPER_THRESHOLD)
	) FREE_LIST (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // enqueue request
		.enq_req_valid_by_bank(free_list_enq_req_valid_by_bank),
		.enq_req_PR_by_bank(free_list_enq_req_PR_by_bank),

	    // enqueue feedback
		.enq_resp_ack_by_bank(free_list_enq_resp_ack_by_bank),

	    // dequeue request
		.deq_req_valid_by_bank(free_list_deq_req_valid_by_bank),
		.deq_req_PR_by_bank(free_list_deq_req_PR_by_bank),

	    // dequeue feedback
		.deq_resp_ready_by_bank(free_list_deq_resp_ready_by_bank)
	);

	map_table #(
		.MAP_TABLE_READ_PORT_COUNT(MAP_TABLE_READ_PORT_COUNT),
		.MAP_TABLE_WRITE_PORT_COUNT(MAP_TABLE_WRITE_PORT_COUNT)
	) MAP_TABLE (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // read ports
		.read_AR_by_port(map_table_read_AR_by_port),
		.read_PR_by_port(map_table_read_PR_by_port),

	    // write ports
		.write_valid_by_port(map_table_write_valid_by_port),
		.write_AR_by_port(map_table_write_AR_by_port),
		.write_PR_by_port(map_table_write_PR_by_port),

	    // checkpoint save
		.save_map_table(map_table_save_map_table),

	    // checkpoint restore
		.restore_valid(map_table_restore_valid),
		.restore_map_table(map_table_restore_map_table)
	);

	checkpoint_array #(
		.CHECKPOINT_COUNT(CHECKPOINT_COUNT),
		.CHECKPOINT_INDEX_WIDTH(CHECKPOINT_INDEX_WIDTH),
		.CHECKPOINT_THRESHOLD(CHECKPOINT_THRESHOLD)
	) CHECKPOINT_ARRAY (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // checkpoint save
		.save_valid(checkpoint_array_save_valid),
		.save_map_table(checkpoint_array_save_map_table),
		.save_LH(checkpoint_array_save_LH),
		.save_GH(checkpoint_array_save_GH),
		.save_ras_index(checkpoint_array_save_ras_index),

		.save_ready(checkpoint_array_save_ready),
		.save_index(checkpoint_array_save_index),

	    // map table restore
		.map_table_restore_index(checkpoint_array_map_table_restore_index),
		.map_table_restore_map_table(checkpoint_array_map_table_restore_map_table),

		// branch info restore
		.branch_info_restore_index(checkpoint_array_branch_info_restore_index),
		.branch_info_restore_LH(checkpoint_array_branch_info_restore_LH),
		.branch_info_restore_GH(checkpoint_array_branch_info_restore_GH),
		.branch_info_restore_ras_index(checkpoint_array_branch_info_restore_ras_index),

		// checkpoint clear
		.clear_valid(checkpoint_array_clear_valid),
		.clear_index(checkpoint_array_clear_index),

	    // advertized threshold
		.above_threshold(checkpoint_array_above_threshold)
	);

	ar_dep_check AR_DEP_CHECK (

	    // inputs by way
		.regwrite_by_way(ar_dep_check_regwrite_by_way),
		.A_AR_by_way(ar_dep_check_A_AR_by_way),
		.B_AR_by_way(ar_dep_check_B_AR_by_way),
		.dest_AR_by_way(ar_dep_check_dest_AR_by_way),

	    // outputs by way
		.A_PR_dep_by_way(ar_dep_check_A_PR_dep_by_way),
		.A_PR_sel_by_way(ar_dep_check_A_PR_sel_by_way),
		.B_PR_dep_by_way(ar_dep_check_B_PR_dep_by_way),
		.B_PR_sel_by_way(ar_dep_check_B_PR_sel_by_way),
		.dest_PR_dep_by_way(ar_dep_check_dest_PR_dep_by_way),
		.dest_PR_sel_by_way(ar_dep_check_dest_PR_sel_by_way)
	);

	// RNM/DISP pipeline reg inputs:
	always_comb begin

		next_valid_by_way_DISP = valid_by_way_RNM;
		next_uncompressed_by_way_DISP = uncompressed_by_way_RNM;
		next_PC_by_way_DISP = PC_by_way_RNM;
		next_pred_PC_by_way_DISP = pred_PC_by_way_RNM;
		next_pred_info_by_way_DISP = pred_info_out_by_way_RNM;
		next_pred_lru_by_way_DISP = pred_lru_by_way_RNM;
		next_mdp_info_by_way_DISP = mdp_info_by_way_RNM;

		next_is_access_fault_DISP = is_access_fault_RNM;
		next_is_page_fault_DISP = is_page_fault_RNM;
		next_is_illegal_instr_DISP = is_illegal_instr_RNM;
		next_exception_present_DISP = exception_present_RNM;
		next_exception_index_DISP = exception_index_RNM;
		next_illegal_instr32_DISP = illegal_instr32_RNM;
		next_is_exception_by_way_DISP = is_exception_by_way_RNM;
		
		next_checkpoint_saved_DISP = checkpoint_array_save_valid;
		next_checkpoint_saved_index_DISP = checkpoint_array_save_index;

		next_is_alu_reg_by_way_DISP = is_alu_reg_by_way_RNM;
		next_is_alu_imm_by_way_DISP = is_alu_imm_by_way_RNM;
		next_is_bru_by_way_DISP = is_bru_by_way_RNM;
		next_is_mdu_by_way_DISP = is_mdu_by_way_RNM;
		next_is_ldu_by_way_DISP = is_ldu_by_way_RNM;
		next_is_store_by_way_DISP = is_store_by_way_RNM;
		next_is_amo_by_way_DISP = is_amo_by_way_RNM;
		next_is_fence_by_way_DISP = is_fence_by_way_RNM;
		next_is_sysu_by_way_DISP = is_sysu_by_way_RNM;

		next_op_by_way_DISP = op_by_way_RNM;
		next_is_reg_write_by_way_DISP = is_reg_write_by_way_RNM;
		
		// A RAW check
		for (int way = 0; way < 4; way++) begin
			if (ar_dep_check_A_PR_dep_by_way[way]) begin
				next_A_PR_by_way_DISP[way] = free_list_deq_req_PR_by_bank[ar_dep_check_A_PR_sel_by_way[way]];
			end
			else begin
				next_A_PR_by_way_DISP[way] = map_table_read_PR_by_port[way];
			end
		end
		next_A_unneeded_by_way_DISP = A_unneeded_by_way_RNM;
		next_A_is_zero_by_way_DISP = A_is_zero_by_way_RNM;
		next_A_is_ret_ra_by_way_DISP = A_is_ret_ra_by_way_RNM;
		
		// B RAW check
		for (int way = 0; way < 4; way++) begin
			if (ar_dep_check_B_PR_dep_by_way[way]) begin
				next_B_PR_by_way_DISP[way] = free_list_deq_req_PR_by_bank[ar_dep_check_B_PR_sel_by_way[way]];
			end
			else begin
				next_B_PR_by_way_DISP[way] = map_table_read_PR_by_port[way+4];
			end
		end
		next_B_unneeded_by_way_DISP = B_unneeded_by_way_RNM;
		next_B_is_zero_by_way_DISP = B_is_zero_by_way_RNM;
		
		next_dest_AR_by_way_DISP = dest_AR_by_way_RNM;
		// dest WAW check
		for (int way = 0; way < 4; way++) begin
			if (ar_dep_check_dest_PR_dep_by_way[way]) begin
				next_dest_old_PR_by_way_DISP[way] = free_list_deq_req_PR_by_bank[ar_dep_check_dest_PR_sel_by_way[way]];
			end
			else begin
				next_dest_old_PR_by_way_DISP[way] = map_table_read_PR_by_port[way+8];
			end
		end
		next_dest_new_PR_by_way_DISP = free_list_deq_req_PR_by_bank;
		next_dest_is_link_ra_by_way_DISP = dest_is_link_ra_by_way_RNM;

		next_imm20_by_way_DISP = imm20_by_way_RNM;

		next_mem_aq_by_way_DISP = mem_aq_by_way_RNM;
		next_io_aq_by_way_DISP = io_aq_by_way_RNM;
		next_mem_rl_by_way_DISP = mem_rl_by_way_RNM;
		next_io_rl_by_way_DISP = io_rl_by_way_RNM;
	end

	/////////////////
	// DISP Stage: //
	/////////////////

	// RNM/DISP pipeline reg outputs:
	// always_ff @ (posedge CLK, negedge nRST) begin
	always_ff @ (posedge CLK) begin
		if (~nRST) begin
			valid_by_way_DISP <= '0;
			uncompressed_by_way_DISP <= '0;
			PC_by_way_DISP <= '0;
			pred_PC_by_way_DISP <= '0;
			pred_info_by_way_DISP <= '0;
			pred_lru_by_way_DISP <= '0;
			mdp_info_by_way_DISP <= '0;
			
			is_access_fault_DISP <= '0;
			is_page_fault_DISP <= '0;
			is_illegal_instr_DISP <= '0;
			exception_present_DISP <= '0;
			exception_index_DISP <= '0;
			illegal_instr32_DISP <= '0;
			is_exception_by_way_DISP <= '0;

			checkpoint_saved_DISP <= '0;
			checkpoint_saved_index_DISP <= '0;
			
			is_alu_reg_by_way_DISP <= '0;
			is_alu_imm_by_way_DISP <= '0;
			is_bru_by_way_DISP <= '0;
			is_mdu_by_way_DISP <= '0;
			is_ldu_by_way_DISP <= '0;
			is_store_by_way_DISP <= '0;
			is_amo_by_way_DISP <= '0;
			is_fence_by_way_DISP <= '0;
			is_sysu_by_way_DISP <= '0;
			
			op_by_way_DISP <= '0;
			is_reg_write_by_way_DISP <= '0;
			
			A_PR_by_way_DISP <= '0;
			A_unneeded_by_way_DISP <= '0;
			A_is_zero_by_way_DISP <= '0;
			A_is_ret_ra_by_way_DISP <= '0;

			B_PR_by_way_DISP <= '0;
			B_unneeded_by_way_DISP <= '0;
			B_is_zero_by_way_DISP <= '0;
			
			dest_AR_by_way_DISP <= '0;
			dest_old_PR_by_way_DISP <= '0;
			dest_new_PR_by_way_DISP <= '0;
			dest_is_link_ra_by_way_DISP <= '0;

			imm20_by_way_DISP <= '0;

			mem_aq_by_way_DISP <= '0;
			io_aq_by_way_DISP <= '0;
			mem_rl_by_way_DISP <= '0;
			io_rl_by_way_DISP <= '0;
		end
		else if (stall_DISP) begin
			valid_by_way_DISP <= valid_by_way_DISP;
			uncompressed_by_way_DISP <= uncompressed_by_way_DISP;
			PC_by_way_DISP <= PC_by_way_DISP;
			pred_PC_by_way_DISP <= pred_PC_by_way_DISP;
			pred_info_by_way_DISP <= pred_info_by_way_DISP;
			pred_lru_by_way_DISP <= pred_lru_by_way_DISP;
			mdp_info_by_way_DISP <= mdp_info_by_way_DISP;
			
			is_access_fault_DISP <= is_access_fault_DISP;
			is_page_fault_DISP <= is_page_fault_DISP;
			is_illegal_instr_DISP <= is_illegal_instr_DISP;
			exception_present_DISP <= exception_present_DISP;
			exception_index_DISP <= exception_index_DISP;
			illegal_instr32_DISP <= illegal_instr32_DISP;
			is_exception_by_way_DISP <= is_exception_by_way_DISP;

			checkpoint_saved_DISP <= checkpoint_saved_DISP;
			checkpoint_saved_index_DISP <= checkpoint_saved_index_DISP;
			
			is_alu_reg_by_way_DISP <= is_alu_reg_by_way_DISP;
			is_alu_imm_by_way_DISP <= is_alu_imm_by_way_DISP;
			is_bru_by_way_DISP <= is_bru_by_way_DISP;
			is_mdu_by_way_DISP <= is_mdu_by_way_DISP;
			is_ldu_by_way_DISP <= is_ldu_by_way_DISP;
			is_store_by_way_DISP <= is_store_by_way_DISP;
			is_amo_by_way_DISP <= is_amo_by_way_DISP;
			is_fence_by_way_DISP <= is_fence_by_way_DISP;
			is_sysu_by_way_DISP <= is_sysu_by_way_DISP;
			
			op_by_way_DISP <= op_by_way_DISP;
			is_reg_write_by_way_DISP <= is_reg_write_by_way_DISP;
			
			A_PR_by_way_DISP <= A_PR_by_way_DISP;
			A_unneeded_by_way_DISP <= A_unneeded_by_way_DISP;
			A_is_zero_by_way_DISP <= A_is_zero_by_way_DISP;
			A_is_ret_ra_by_way_DISP <= A_is_ret_ra_by_way_DISP;

			B_PR_by_way_DISP <= B_PR_by_way_DISP;
			B_unneeded_by_way_DISP <= B_unneeded_by_way_DISP;
			B_is_zero_by_way_DISP <= B_is_zero_by_way_DISP;
			
			dest_AR_by_way_DISP <= dest_AR_by_way_DISP;
			dest_old_PR_by_way_DISP <= dest_old_PR_by_way_DISP;
			dest_new_PR_by_way_DISP <= dest_new_PR_by_way_DISP;
			dest_is_link_ra_by_way_DISP <= dest_is_link_ra_by_way_DISP;

			imm20_by_way_DISP <= imm20_by_way_DISP;

			mem_aq_by_way_DISP <= mem_aq_by_way_DISP;
			io_aq_by_way_DISP <= io_aq_by_way_DISP;
			mem_rl_by_way_DISP <= mem_rl_by_way_DISP;
			io_rl_by_way_DISP <= io_rl_by_way_DISP;
		end
		else begin
			valid_by_way_DISP <= next_valid_by_way_DISP;
			uncompressed_by_way_DISP <= next_uncompressed_by_way_DISP;
			PC_by_way_DISP <= next_PC_by_way_DISP;
			pred_PC_by_way_DISP <= next_pred_PC_by_way_DISP;
			pred_info_by_way_DISP <= next_pred_info_by_way_DISP;
			pred_lru_by_way_DISP <= next_pred_lru_by_way_DISP;
			mdp_info_by_way_DISP <= next_mdp_info_by_way_DISP;
			
			is_access_fault_DISP <= next_is_access_fault_DISP;
			is_page_fault_DISP <= next_is_page_fault_DISP;
			is_illegal_instr_DISP <= next_is_illegal_instr_DISP;
			exception_present_DISP <= next_exception_present_DISP;
			exception_index_DISP <= next_exception_index_DISP;
			illegal_instr32_DISP <= next_illegal_instr32_DISP;
			is_exception_by_way_DISP <= next_is_exception_by_way_DISP;

			checkpoint_saved_DISP <= next_checkpoint_saved_DISP;
			checkpoint_saved_index_DISP <= next_checkpoint_saved_index_DISP;
			
			is_alu_reg_by_way_DISP <= next_is_alu_reg_by_way_DISP;
			is_alu_imm_by_way_DISP <= next_is_alu_imm_by_way_DISP;
			is_bru_by_way_DISP <= next_is_bru_by_way_DISP;
			is_mdu_by_way_DISP <= next_is_mdu_by_way_DISP;
			is_ldu_by_way_DISP <= next_is_ldu_by_way_DISP;
			is_store_by_way_DISP <= next_is_store_by_way_DISP;
			is_amo_by_way_DISP <= next_is_amo_by_way_DISP;
			is_fence_by_way_DISP <= next_is_fence_by_way_DISP;
			is_sysu_by_way_DISP <= next_is_sysu_by_way_DISP;
			
			op_by_way_DISP <= next_op_by_way_DISP;
			is_reg_write_by_way_DISP <= next_is_reg_write_by_way_DISP;
			
			A_PR_by_way_DISP <= next_A_PR_by_way_DISP;
			A_unneeded_by_way_DISP <= next_A_unneeded_by_way_DISP;
			A_is_zero_by_way_DISP <= next_A_is_zero_by_way_DISP;
			A_is_ret_ra_by_way_DISP <= next_A_is_ret_ra_by_way_DISP;

			B_PR_by_way_DISP <= next_B_PR_by_way_DISP;
			B_unneeded_by_way_DISP <= next_B_unneeded_by_way_DISP;
			B_is_zero_by_way_DISP <= next_B_is_zero_by_way_DISP;
			
			dest_AR_by_way_DISP <= next_dest_AR_by_way_DISP;
			dest_old_PR_by_way_DISP <= next_dest_old_PR_by_way_DISP;
			dest_new_PR_by_way_DISP <= next_dest_new_PR_by_way_DISP;
			dest_is_link_ra_by_way_DISP <= next_dest_is_link_ra_by_way_DISP;

			imm20_by_way_DISP <= next_imm20_by_way_DISP;

			mem_aq_by_way_DISP <= next_mem_aq_by_way_DISP;
			io_aq_by_way_DISP <= next_io_aq_by_way_DISP;
			mem_rl_by_way_DISP <= next_mem_rl_by_way_DISP;
			io_rl_by_way_DISP <= next_io_rl_by_way_DISP;
		end
	end

	// simple active state + comb modification to say if making arch state modifications and yielding
	// always_ff @ (posedge CLK, negedge nRST) begin
	always_ff @ (posedge CLK) begin
		if (~nRST) begin
			active_DISP <= 1'b0;
			killed_DISP <= 1'b0;
		end
		else begin
			active_DISP <= next_active_DISP;
			killed_DISP <= next_killed_DISP;
		end
	end

	always_comb begin

		// check for stall and generate stalls in this block

		// check active state
		if (active_DISP) begin

			// check valid dispatch
				// rob ready
				// way not valid or way excepting or way got ack
			if (
				dispatch_rob_enq_ready
				& &(
					~valid_by_way_DISP
					| is_exception_by_way_DISP
					| dispatch_ack_alu_reg_mdu_dq_by_way
					| dispatch_ack_alu_imm_dq_by_way
					| dispatch_ack_bru_dq_by_way
					| dispatch_ack_ldu_dq_by_way
					| dispatch_ack_stamofu_dq_by_way
					| dispatch_ack_sysu_dq_by_way)
			) begin
				perform_DISP = 1'b1;
				stall_DISP = 1'b0;
			end

			// otherwise, stall
			else begin
				perform_DISP = 1'b0;
				stall_DISP = 1'b1;
			end
		end
		else begin
			perform_DISP = 1'b0;
			stall_DISP = 1'b0;
		end

		// check active next cycle
		if (active_DISP & stall_DISP) begin
			next_active_DISP = 1'b1;
			next_killed_DISP = killed_DISP | rob_kill_valid;
		end
		else if (~stall_DISP & valid_DISP_from_RNM) begin
			next_active_DISP = 1'b1;
			next_killed_DISP = 1'b0;
		end
		else begin
			next_active_DISP = 1'b0;
			next_killed_DISP = 1'b0;
		end
	end

	// dispatch attempt = type & valid
	// dispatch valid = type & valid & ack_mask 

	// check for stall (and maybe no rob enQ) depending on if dispatch's are ack'd

	// ignore restarts since arch state changes have been made and ROB must undo them

	// module connections:
	always_comb begin

		// ready_table:
		ready_table_read_PR_by_port = {B_PR_by_way_DISP, A_PR_by_way_DISP};

		ready_table_set_valid_by_port = WB_bus_valid_by_bank;
		ready_table_set_PR_by_port = {
			WB_bus_upper_PR_by_bank[3], 2'h3,
			WB_bus_upper_PR_by_bank[2], 2'h2,
			WB_bus_upper_PR_by_bank[1], 2'h1,
			WB_bus_upper_PR_by_bank[0], 2'h0
		};
		
		ready_table_clear_valid_by_port = is_reg_write_by_way_DISP;
		ready_table_clear_PR_by_port = dest_new_PR_by_way_DISP;
	end

	// modules:

	ready_table READY_TABLE (
		// seq
		.CLK(CLK),
		.nRST(nRST),
		// 8x read ports
		.read_PR_by_port(ready_table_read_PR_by_port),
		.read_ready_by_port(ready_table_read_ready_by_port),
		// 4x set ports
		.set_valid_by_port(ready_table_set_valid_by_port),
		.set_PR_by_port(ready_table_set_PR_by_port),
		// 4x clear ports
		.clear_valid_by_port(ready_table_clear_valid_by_port),
		.clear_PR_by_port(ready_table_clear_PR_by_port)
	);

	// dispatch outputs
	always_comb begin

		// 4-way ROB entry
		dispatch_rob_enq_valid = perform_DISP;
		dispatch_rob_enq_killed = killed_DISP | rob_kill_valid;

		// general instr info
		dispatch_valid_by_way = valid_by_way_DISP;
		dispatch_uncompressed_by_way = uncompressed_by_way_DISP;
		dispatch_PC_by_way = PC_by_way_DISP;
		dispatch_pred_PC_by_way = pred_PC_by_way_DISP;
		dispatch_is_rename_by_way = is_reg_write_by_way_DISP;
		dispatch_pred_info_by_way = pred_info_by_way_DISP;
		dispatch_pred_lru_by_way = pred_lru_by_way_DISP;
		dispatch_mdp_info_by_way = mdp_info_by_way_DISP;
		dispatch_op_by_way = op_by_way_DISP;
		dispatch_imm20_by_way = imm20_by_way_DISP;

		// ordering
		dispatch_mem_aq_by_way = mem_aq_by_way_DISP;
		dispatch_io_aq_by_way = io_aq_by_way_DISP;
		dispatch_mem_rl_by_way = mem_rl_by_way_DISP;
		dispatch_io_rl_by_way = io_rl_by_way_DISP;

		// exception info
		dispatch_is_page_fault = is_page_fault_DISP;
		dispatch_is_access_fault = is_access_fault_DISP;
		dispatch_is_illegal_instr = is_illegal_instr_DISP;
		dispatch_exception_present = exception_present_DISP;
		dispatch_exception_index = exception_index_DISP;
		dispatch_illegal_instr32 = illegal_instr32_DISP;

		// checkpoint info
		dispatch_has_checkpoint = checkpoint_saved_DISP;
		dispatch_checkpoint_index = checkpoint_saved_index_DISP;

		// instr IQ attempts
		dispatch_attempt_alu_reg_mdu_dq_by_way = is_alu_reg_by_way_DISP | is_mdu_by_way_DISP;
		dispatch_attempt_alu_imm_dq_by_way = is_alu_imm_by_way_DISP;
		dispatch_attempt_bru_dq_by_way = is_bru_by_way_DISP;
		dispatch_attempt_ldu_dq_by_way = is_ldu_by_way_DISP;
		dispatch_attempt_stamofu_dq_by_way = is_store_by_way_DISP | is_amo_by_way_DISP | is_fence_by_way_DISP;
		dispatch_attempt_sysu_dq_by_way = is_sysu_by_way_DISP;

		// instr FU valids
		dispatch_valid_alu_reg_by_way = is_alu_reg_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_mdu_by_way = is_mdu_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_alu_imm_by_way = is_alu_imm_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_bru_by_way = is_bru_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_ldu_by_way = is_ldu_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_store_by_way = is_store_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_amo_by_way = is_amo_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_fence_by_way = is_fence_by_way_DISP & {4{perform_DISP}};
		dispatch_valid_sysu_by_way = is_sysu_by_way_DISP & {4{perform_DISP}};

		// operand A
		dispatch_A_PR_by_way = A_PR_by_way_DISP;
		dispatch_A_ready_by_way = ready_table_read_ready_by_port[3:0];
		dispatch_A_is_zero_by_way = A_is_zero_by_way_DISP;
		dispatch_A_unneeded_or_is_zero_by_way = A_unneeded_by_way_DISP | A_is_zero_by_way_DISP;
		dispatch_A_is_ret_ra_by_way = A_is_ret_ra_by_way_DISP;

		// operand B
		dispatch_B_PR_by_way = B_PR_by_way_DISP;
		dispatch_B_ready_by_way = ready_table_read_ready_by_port[7:4];
		dispatch_B_is_zero_by_way = B_is_zero_by_way_DISP;
		dispatch_B_unneeded_or_is_zero_by_way = B_unneeded_by_way_DISP | B_is_zero_by_way_DISP;

		// dest operand
		dispatch_dest_AR_by_way = dest_AR_by_way_DISP;
		dispatch_dest_old_PR_by_way = dest_old_PR_by_way_DISP;
		dispatch_dest_new_PR_by_way = dest_new_PR_by_way_DISP;
		dispatch_dest_is_link_ra_by_way = dest_is_link_ra_by_way_DISP;
	end

endmodule