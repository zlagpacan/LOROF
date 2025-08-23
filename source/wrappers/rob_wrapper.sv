/*
    Filename: rob_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around rob module. 
    Spec: LOROF/spec/design/rob.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter ROB_ENTRIES = core_types_pkg::ROB_ENTRIES;
parameter LOG_ROB_ENTRIES = $clog2(ROB_ENTRIES);
parameter ROB_MISPRED_Q_ENTRIES = core_types_pkg::ROB_MISPRED_Q_ENTRIES;
parameter ROB_PR_FREE_Q_ENTRIES = core_types_pkg::ROB_MISPRED_Q_ENTRIES;
parameter ROB_RESTART_ON_RESET = 1'b1;
parameter INIT_PC = 32'h00000000;
parameter INIT_ASID = 9'h0;
parameter INIT_EXEC_MODE = M_MODE;
parameter INIT_VIRTUAL_MODE = 1'b0;
parameter INIT_MXR = 1'b0;
parameter INIT_SUM = 1'b0;
parameter INIT_TRAP_SFENCE = 1'b0;
parameter INIT_TRAP_WFI = 1'b0;
parameter INIT_TRAP_SRET = 1'b0;
parameter INIT_TVEC_BASE_PC = 32'h0000F000;

module rob_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // 4-way ROB dispatch:
	input logic next_dispatch_enq_valid,
	input logic next_dispatch_enq_killed,
    // general instr info
	input logic [3:0] next_dispatch_valid_by_way,
	input logic [3:0] next_dispatch_uncompressed_by_way,
	input logic [3:0][31:0] next_dispatch_PC_by_way,
	input logic [3:0] next_dispatch_is_rename_by_way,
    // exception info
	input logic next_dispatch_is_page_fault,
	input logic next_dispatch_is_access_fault,
	input logic next_dispatch_is_illegal_instr,
	input logic next_dispatch_exception_present,
	input logic [1:0] next_dispatch_exception_index,
	input logic [31:0] next_dispatch_illegal_instr32,
	// checkpoint info
	input logic next_dispatch_has_checkpoint,
	input logic [CHECKPOINT_INDEX_WIDTH-1:0] next_dispatch_checkpoint_index,
    // instr FU valids
	input logic [3:0] next_dispatch_attempt_ldu_dq_by_way,
    // dest operand
	input logic [3:0][4:0] next_dispatch_dest_AR_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_old_PR_by_way,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_new_PR_by_way,

    // ROB dispatch feedback
	output logic last_dispatch_enq_ready,
	output logic [3:0][LOG_ROB_ENTRIES-1:0] last_dispatch_ROB_index_by_way,

    // writeback bus complete notif by bank
	input logic [PRF_BANK_COUNT-1:0] next_complete_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] next_complete_bus_ROB_index_by_bank,

    // LDU complete notif
	input logic next_ldu_complete_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_complete_ROB_index,

    // STAMOFU complete notif
	input logic next_stamofu_complete_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_complete_ROB_index,

    // branch notification to ROB
	input logic next_branch_notif_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_branch_notif_ROB_index,
	input logic next_branch_notif_is_mispredict,
	input logic next_branch_notif_is_taken,
	input logic next_branch_notif_use_upct,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_branch_notif_updated_pred_info,
	input logic next_branch_notif_pred_lru,
	input logic [31:0] next_branch_notif_start_PC,
	input logic [31:0] next_branch_notif_target_PC,

    // branch notification backpressure from ROB
	output logic last_branch_notif_ready,

    // LDU misprediction notification to ROB
	input logic next_ldu_mispred_notif_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_mispred_notif_ROB_index,

    // LDU misprediction notification backpressure from ROB
	output logic last_ldu_mispred_notif_ready,

    // fence restart notification to ROB
	input logic next_fence_restart_notif_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_fence_restart_notif_ROB_index,

    // fence restart notification backpressure from ROB
	output logic last_fence_restart_notif_ready,

    // LDU exception to ROB
	input logic next_ldu_exception_valid,
	input logic [VA_WIDTH-1:0] next_ldu_exception_VA,
	input logic next_ldu_exception_page_fault,
	input logic next_ldu_exception_access_fault,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_exception_ROB_index,

    // LDU exception backpressure from ROB
	output logic last_ldu_exception_ready,

    // STAMOFU exception to ROB
	input logic next_stamofu_exception_valid,
	input logic [VA_WIDTH-1:0] next_stamofu_exception_VA,
	input logic next_stamofu_exception_is_lr,
	input logic next_stamofu_exception_page_fault,
	input logic next_stamofu_exception_access_fault,
	input logic next_stamofu_exception_misaligned_exception,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_exception_ROB_index,

    // STAMOFU exception backpressure from ROB
	output logic last_stamofu_exception_ready,

    // mdp update to ROB
	input logic next_ssu_mdp_update_valid,
	input logic [MDPT_INFO_WIDTH-1:0] next_ssu_mdp_update_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_ssu_mdp_update_ROB_index,

    // mdp update feedback from ROB
	output logic last_ssu_mdp_update_ready,

    // mdpt update to fetch unit
	output logic last_fetch_unit_mdpt_update_valid,
	output logic [31:0] last_fetch_unit_mdpt_update_start_full_PC,
	output logic [ASID_WIDTH-1:0] last_fetch_unit_mdpt_update_ASID,
	output logic [MDPT_INFO_WIDTH-1:0] last_fetch_unit_mdpt_update_mdp_info,

    // ROB commit
	output logic [LOG_ROB_ENTRIES-3:0] last_rob_commit_upper_index,
	output logic [3:0] last_rob_commit_lower_index_valid_mask,

    // restart from ROB
	output logic last_rob_restart_valid,
	output logic [31:0] last_rob_restart_PC,
	output logic [ASID_WIDTH-1:0] last_rob_restart_ASID,
	output logic [1:0] last_rob_restart_exec_mode,
	output logic last_rob_restart_virtual_mode,
	output logic last_rob_restart_MXR,
	output logic last_rob_restart_SUM,
	output logic last_rob_restart_trap_sfence,
	output logic last_rob_restart_trap_wfi,
	output logic last_rob_restart_trap_sret,

    // ROB kill
	output logic last_rob_kill_valid,
	output logic [LOG_ROB_ENTRIES-1:0] last_rob_kill_abs_head_index,
	output logic [LOG_ROB_ENTRIES-1:0] last_rob_kill_rel_kill_younger_index,

    // branch update from ROB
	output logic last_rob_branch_update_valid,
	output logic last_rob_branch_update_has_checkpoint,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0] last_rob_branch_update_checkpoint_index,
	output logic last_rob_branch_update_is_mispredict,
	output logic last_rob_branch_update_is_taken,
	output logic last_rob_branch_update_use_upct,
	output logic [BTB_PRED_INFO_WIDTH-1:0] last_rob_branch_update_intermediate_pred_info,
	output logic last_rob_branch_update_pred_lru,
	output logic [31:0] last_rob_branch_update_start_PC,
	output logic [31:0] last_rob_branch_update_target_PC,

    // ROB control of rename
	output logic last_rob_controlling_rename,

	output logic last_rob_checkpoint_map_table_restore_valid,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0] last_rob_checkpoint_map_table_restore_index,

	output logic last_rob_checkpoint_clear_valid,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0] last_rob_checkpoint_clear_index,

	output logic [3:0] last_rob_map_table_write_valid_by_port,
	output logic [3:0][LOG_AR_COUNT-1:0] last_rob_map_table_write_AR_by_port,
	output logic [3:0][LOG_PR_COUNT-1:0] last_rob_map_table_write_PR_by_port,

	// ROB physical register freeing
	output logic [3:0] last_rob_PR_free_req_valid_by_bank,
	output logic [3:0][LOG_PR_COUNT-1:0] last_rob_PR_free_req_PR_by_bank,
	input logic [3:0] next_rob_PR_free_resp_ack_by_bank
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // 4-way ROB dispatch:
	logic dispatch_enq_valid;
	logic dispatch_enq_killed;
    // general instr info
	logic [3:0] dispatch_valid_by_way;
	logic [3:0] dispatch_uncompressed_by_way;
	logic [3:0][31:0] dispatch_PC_by_way;
	logic [3:0] dispatch_is_rename_by_way;
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
    // instr FU valids
	logic [3:0] dispatch_attempt_ldu_dq_by_way;
    // dest operand
	logic [3:0][4:0] dispatch_dest_AR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_old_PR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_new_PR_by_way;

    // ROB dispatch feedback
	logic dispatch_enq_ready;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_way;

    // writeback bus complete notif by bank
	logic [PRF_BANK_COUNT-1:0] complete_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] complete_bus_ROB_index_by_bank;

    // LDU complete notif
	logic ldu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] ldu_complete_ROB_index;

    // STAMOFU complete notif
	logic stamofu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_complete_ROB_index;

    // branch notification to ROB
	logic branch_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] branch_notif_ROB_index;
	logic branch_notif_is_mispredict;
	logic branch_notif_is_taken;
	logic branch_notif_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] branch_notif_updated_pred_info;
	logic branch_notif_pred_lru;
	logic [31:0] branch_notif_start_PC;
	logic [31:0] branch_notif_target_PC;

    // branch notification backpressure from ROB
	logic branch_notif_ready;

    // LDU misprediction notification to ROB
	logic ldu_mispred_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] ldu_mispred_notif_ROB_index;

    // LDU misprediction notification backpressure from ROB
	logic ldu_mispred_notif_ready;

    // fence restart notification to ROB
	logic fence_restart_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] fence_restart_notif_ROB_index;

    // fence restart notification backpressure from ROB
	logic fence_restart_notif_ready;

    // LDU exception to ROB
	logic ldu_exception_valid;
	logic [VA_WIDTH-1:0] ldu_exception_VA;
	logic ldu_exception_page_fault;
	logic ldu_exception_access_fault;
	logic [LOG_ROB_ENTRIES-1:0] ldu_exception_ROB_index;

    // LDU exception backpressure from ROB
	logic ldu_exception_ready;

    // STAMOFU exception to ROB
	logic stamofu_exception_valid;
	logic [VA_WIDTH-1:0] stamofu_exception_VA;
	logic stamofu_exception_is_lr;
	logic stamofu_exception_page_fault;
	logic stamofu_exception_access_fault;
	logic stamofu_exception_misaligned_exception;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_exception_ROB_index;

    // STAMOFU exception backpressure from ROB
	logic stamofu_exception_ready;

    // mdp update to ROB
	logic ssu_mdp_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] ssu_mdp_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ssu_mdp_update_ROB_index;

    // mdp update feedback from ROB
	logic ssu_mdp_update_ready;

    // mdpt update to fetch unit
	logic fetch_unit_mdpt_update_valid;
	logic [31:0] fetch_unit_mdpt_update_start_full_PC;
	logic [ASID_WIDTH-1:0] fetch_unit_mdpt_update_ASID;
	logic [MDPT_INFO_WIDTH-1:0] fetch_unit_mdpt_update_mdp_info;

    // ROB commit
	logic [LOG_ROB_ENTRIES-3:0] rob_commit_upper_index;
	logic [3:0] rob_commit_lower_index_valid_mask;

    // restart from ROB
	logic rob_restart_valid;
	logic [31:0] rob_restart_PC;
	logic [ASID_WIDTH-1:0] rob_restart_ASID;
	logic [1:0] rob_restart_exec_mode;
	logic rob_restart_virtual_mode;
	logic rob_restart_MXR;
	logic rob_restart_SUM;
	logic rob_restart_trap_sfence;
	logic rob_restart_trap_wfi;
	logic rob_restart_trap_sret;

    // ROB kill
	logic rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_rel_kill_younger_index;

    // branch update from ROB
	logic rob_branch_update_valid;
	logic rob_branch_update_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] rob_branch_update_checkpoint_index;
	logic rob_branch_update_is_mispredict;
	logic rob_branch_update_is_taken;
	logic rob_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] rob_branch_update_intermediate_pred_info;
	logic rob_branch_update_pred_lru;
	logic [31:0] rob_branch_update_start_PC;
	logic [31:0] rob_branch_update_target_PC;

    // ROB control of rename
	logic rob_controlling_rename;

	logic rob_checkpoint_map_table_restore_valid;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] rob_checkpoint_map_table_restore_index;

	logic rob_checkpoint_clear_valid;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] rob_checkpoint_clear_index;

	logic [3:0] rob_map_table_write_valid_by_port;
	logic [3:0][LOG_AR_COUNT-1:0] rob_map_table_write_AR_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] rob_map_table_write_PR_by_port;

	// ROB physical register freeing
	logic [3:0] rob_PR_free_req_valid_by_bank;
	logic [3:0][LOG_PR_COUNT-1:0] rob_PR_free_req_PR_by_bank;
	logic [3:0] rob_PR_free_resp_ack_by_bank;

    // ----------------------------------------------------------------
    // Module Instantiation:

	rob #(
		.ROB_ENTRIES(ROB_ENTRIES),
		.LOG_ROB_ENTRIES(LOG_ROB_ENTRIES),
		.ROB_MISPRED_Q_ENTRIES(ROB_MISPRED_Q_ENTRIES),
		.ROB_PR_FREE_Q_ENTRIES(ROB_PR_FREE_Q_ENTRIES),
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

		    // 4-way ROB dispatch:
			dispatch_enq_valid <= '0;
			dispatch_enq_killed <= '0;
		    // general instr info
			dispatch_valid_by_way <= '0;
			dispatch_uncompressed_by_way <= '0;
			dispatch_PC_by_way <= '0;
			dispatch_is_rename_by_way <= '0;
		    // exception info
			dispatch_is_page_fault <= '0;
			dispatch_is_access_fault <= '0;
			dispatch_is_illegal_instr <= '0;
			dispatch_exception_present <= '0;
			dispatch_exception_index <= '0;
			dispatch_illegal_instr32 <= '0;
			// checkpoint info
			dispatch_has_checkpoint <= '0;
			dispatch_checkpoint_index <= '0;
		    // instr FU valids
			dispatch_attempt_ldu_dq_by_way <= '0;
		    // dest operand
			dispatch_dest_AR_by_way <= '0;
			dispatch_dest_old_PR_by_way <= '0;
			dispatch_dest_new_PR_by_way <= '0;

		    // ROB dispatch feedback
			last_dispatch_enq_ready <= '0;
			last_dispatch_ROB_index_by_way <= '0;

		    // writeback bus complete notif by bank
			complete_bus_valid_by_bank <= '0;
			complete_bus_ROB_index_by_bank <= '0;

		    // LDU complete notif
			ldu_complete_valid <= '0;
			ldu_complete_ROB_index <= '0;

		    // STAMOFU complete notif
			stamofu_complete_valid <= '0;
			stamofu_complete_ROB_index <= '0;

		    // branch notification to ROB
			branch_notif_valid <= '0;
			branch_notif_ROB_index <= '0;
			branch_notif_is_mispredict <= '0;
			branch_notif_is_taken <= '0;
			branch_notif_use_upct <= '0;
			branch_notif_updated_pred_info <= '0;
			branch_notif_pred_lru <= '0;
			branch_notif_start_PC <= '0;
			branch_notif_target_PC <= '0;

		    // branch notification backpressure from ROB
			last_branch_notif_ready <= '0;

		    // LDU misprediction notification to ROB
			ldu_mispred_notif_valid <= '0;
			ldu_mispred_notif_ROB_index <= '0;

		    // LDU misprediction notification backpressure from ROB
			last_ldu_mispred_notif_ready <= '0;

		    // fence restart notification to ROB
			fence_restart_notif_valid <= '0;
			fence_restart_notif_ROB_index <= '0;

		    // fence restart notification backpressure from ROB
			last_fence_restart_notif_ready <= '0;

		    // LDU exception to ROB
			ldu_exception_valid <= '0;
			ldu_exception_VA <= '0;
			ldu_exception_page_fault <= '0;
			ldu_exception_access_fault <= '0;
			ldu_exception_ROB_index <= '0;

		    // LDU exception backpressure from ROB
			last_ldu_exception_ready <= '0;

		    // STAMOFU exception to ROB
			stamofu_exception_valid <= '0;
			stamofu_exception_VA <= '0;
			stamofu_exception_is_lr <= '0;
			stamofu_exception_page_fault <= '0;
			stamofu_exception_access_fault <= '0;
			stamofu_exception_misaligned_exception <= '0;
			stamofu_exception_ROB_index <= '0;

		    // STAMOFU exception backpressure from ROB
			last_stamofu_exception_ready <= '0;

		    // mdp update to ROB
			ssu_mdp_update_valid <= '0;
			ssu_mdp_update_mdp_info <= '0;
			ssu_mdp_update_ROB_index <= '0;

		    // mdp update feedback from ROB
			last_ssu_mdp_update_ready <= '0;

		    // mdpt update to fetch unit
			last_fetch_unit_mdpt_update_valid <= '0;
			last_fetch_unit_mdpt_update_start_full_PC <= '0;
			last_fetch_unit_mdpt_update_ASID <= '0;
			last_fetch_unit_mdpt_update_mdp_info <= '0;

		    // ROB commit
			last_rob_commit_upper_index <= '0;
			last_rob_commit_lower_index_valid_mask <= '0;

		    // restart from ROB
			last_rob_restart_valid <= '0;
			last_rob_restart_PC <= '0;
			last_rob_restart_ASID <= '0;
			last_rob_restart_exec_mode <= '0;
			last_rob_restart_virtual_mode <= '0;
			last_rob_restart_MXR <= '0;
			last_rob_restart_SUM <= '0;
			last_rob_restart_trap_sfence <= '0;
			last_rob_restart_trap_wfi <= '0;
			last_rob_restart_trap_sret <= '0;

		    // ROB kill
			last_rob_kill_valid <= '0;
			last_rob_kill_abs_head_index <= '0;
			last_rob_kill_rel_kill_younger_index <= '0;

		    // branch update from ROB
			last_rob_branch_update_valid <= '0;
			last_rob_branch_update_has_checkpoint <= '0;
			last_rob_branch_update_checkpoint_index <= '0;
			last_rob_branch_update_is_mispredict <= '0;
			last_rob_branch_update_is_taken <= '0;
			last_rob_branch_update_use_upct <= '0;
			last_rob_branch_update_intermediate_pred_info <= '0;
			last_rob_branch_update_pred_lru <= '0;
			last_rob_branch_update_start_PC <= '0;
			last_rob_branch_update_target_PC <= '0;

		    // ROB control of rename
			last_rob_controlling_rename <= '0;

			last_rob_checkpoint_map_table_restore_valid <= '0;
			last_rob_checkpoint_map_table_restore_index <= '0;

			last_rob_checkpoint_clear_valid <= '0;
			last_rob_checkpoint_clear_index <= '0;

			last_rob_map_table_write_valid_by_port <= '0;
			last_rob_map_table_write_AR_by_port <= '0;
			last_rob_map_table_write_PR_by_port <= '0;

			// ROB physical register freeing
			last_rob_PR_free_req_valid_by_bank <= '0;
			last_rob_PR_free_req_PR_by_bank <= '0;
			rob_PR_free_resp_ack_by_bank <= '0;
        end
        else begin

		    // 4-way ROB dispatch:
			dispatch_enq_valid <= next_dispatch_enq_valid;
			dispatch_enq_killed <= next_dispatch_enq_killed;
		    // general instr info
			dispatch_valid_by_way <= next_dispatch_valid_by_way;
			dispatch_uncompressed_by_way <= next_dispatch_uncompressed_by_way;
			dispatch_PC_by_way <= next_dispatch_PC_by_way;
			dispatch_is_rename_by_way <= next_dispatch_is_rename_by_way;
		    // exception info
			dispatch_is_page_fault <= next_dispatch_is_page_fault;
			dispatch_is_access_fault <= next_dispatch_is_access_fault;
			dispatch_is_illegal_instr <= next_dispatch_is_illegal_instr;
			dispatch_exception_present <= next_dispatch_exception_present;
			dispatch_exception_index <= next_dispatch_exception_index;
			dispatch_illegal_instr32 <= next_dispatch_illegal_instr32;
			// checkpoint info
			dispatch_has_checkpoint <= next_dispatch_has_checkpoint;
			dispatch_checkpoint_index <= next_dispatch_checkpoint_index;
		    // instr FU valids
			dispatch_attempt_ldu_dq_by_way <= next_dispatch_attempt_ldu_dq_by_way;
		    // dest operand
			dispatch_dest_AR_by_way <= next_dispatch_dest_AR_by_way;
			dispatch_dest_old_PR_by_way <= next_dispatch_dest_old_PR_by_way;
			dispatch_dest_new_PR_by_way <= next_dispatch_dest_new_PR_by_way;

		    // ROB dispatch feedback
			last_dispatch_enq_ready <= dispatch_enq_ready;
			last_dispatch_ROB_index_by_way <= dispatch_ROB_index_by_way;

		    // writeback bus complete notif by bank
			complete_bus_valid_by_bank <= next_complete_bus_valid_by_bank;
			complete_bus_ROB_index_by_bank <= next_complete_bus_ROB_index_by_bank;

		    // LDU complete notif
			ldu_complete_valid <= next_ldu_complete_valid;
			ldu_complete_ROB_index <= next_ldu_complete_ROB_index;

		    // STAMOFU complete notif
			stamofu_complete_valid <= next_stamofu_complete_valid;
			stamofu_complete_ROB_index <= next_stamofu_complete_ROB_index;

		    // branch notification to ROB
			branch_notif_valid <= next_branch_notif_valid;
			branch_notif_ROB_index <= next_branch_notif_ROB_index;
			branch_notif_is_mispredict <= next_branch_notif_is_mispredict;
			branch_notif_is_taken <= next_branch_notif_is_taken;
			branch_notif_use_upct <= next_branch_notif_use_upct;
			branch_notif_updated_pred_info <= next_branch_notif_updated_pred_info;
			branch_notif_pred_lru <= next_branch_notif_pred_lru;
			branch_notif_start_PC <= next_branch_notif_start_PC;
			branch_notif_target_PC <= next_branch_notif_target_PC;

		    // branch notification backpressure from ROB
			last_branch_notif_ready <= branch_notif_ready;

		    // LDU misprediction notification to ROB
			ldu_mispred_notif_valid <= next_ldu_mispred_notif_valid;
			ldu_mispred_notif_ROB_index <= next_ldu_mispred_notif_ROB_index;

		    // LDU misprediction notification backpressure from ROB
			last_ldu_mispred_notif_ready <= ldu_mispred_notif_ready;

		    // fence restart notification to ROB
			fence_restart_notif_valid <= next_fence_restart_notif_valid;
			fence_restart_notif_ROB_index <= next_fence_restart_notif_ROB_index;

		    // fence restart notification backpressure from ROB
			last_fence_restart_notif_ready <= fence_restart_notif_ready;

		    // LDU exception to ROB
			ldu_exception_valid <= next_ldu_exception_valid;
			ldu_exception_VA <= next_ldu_exception_VA;
			ldu_exception_page_fault <= next_ldu_exception_page_fault;
			ldu_exception_access_fault <= next_ldu_exception_access_fault;
			ldu_exception_ROB_index <= next_ldu_exception_ROB_index;

		    // LDU exception backpressure from ROB
			last_ldu_exception_ready <= ldu_exception_ready;

		    // STAMOFU exception to ROB
			stamofu_exception_valid <= next_stamofu_exception_valid;
			stamofu_exception_VA <= next_stamofu_exception_VA;
			stamofu_exception_is_lr <= next_stamofu_exception_is_lr;
			stamofu_exception_page_fault <= next_stamofu_exception_page_fault;
			stamofu_exception_access_fault <= next_stamofu_exception_access_fault;
			stamofu_exception_misaligned_exception <= next_stamofu_exception_misaligned_exception;
			stamofu_exception_ROB_index <= next_stamofu_exception_ROB_index;

		    // STAMOFU exception backpressure from ROB
			last_stamofu_exception_ready <= stamofu_exception_ready;

		    // mdp update to ROB
			ssu_mdp_update_valid <= next_ssu_mdp_update_valid;
			ssu_mdp_update_mdp_info <= next_ssu_mdp_update_mdp_info;
			ssu_mdp_update_ROB_index <= next_ssu_mdp_update_ROB_index;

		    // mdp update feedback from ROB
			last_ssu_mdp_update_ready <= ssu_mdp_update_ready;

		    // mdpt update to fetch unit
			last_fetch_unit_mdpt_update_valid <= fetch_unit_mdpt_update_valid;
			last_fetch_unit_mdpt_update_start_full_PC <= fetch_unit_mdpt_update_start_full_PC;
			last_fetch_unit_mdpt_update_ASID <= fetch_unit_mdpt_update_ASID;
			last_fetch_unit_mdpt_update_mdp_info <= fetch_unit_mdpt_update_mdp_info;

		    // ROB commit
			last_rob_commit_upper_index <= rob_commit_upper_index;
			last_rob_commit_lower_index_valid_mask <= rob_commit_lower_index_valid_mask;

		    // restart from ROB
			last_rob_restart_valid <= rob_restart_valid;
			last_rob_restart_PC <= rob_restart_PC;
			last_rob_restart_ASID <= rob_restart_ASID;
			last_rob_restart_exec_mode <= rob_restart_exec_mode;
			last_rob_restart_virtual_mode <= rob_restart_virtual_mode;
			last_rob_restart_MXR <= rob_restart_MXR;
			last_rob_restart_SUM <= rob_restart_SUM;
			last_rob_restart_trap_sfence <= rob_restart_trap_sfence;
			last_rob_restart_trap_wfi <= rob_restart_trap_wfi;
			last_rob_restart_trap_sret <= rob_restart_trap_sret;

		    // ROB kill
			last_rob_kill_valid <= rob_kill_valid;
			last_rob_kill_abs_head_index <= rob_kill_abs_head_index;
			last_rob_kill_rel_kill_younger_index <= rob_kill_rel_kill_younger_index;

		    // branch update from ROB
			last_rob_branch_update_valid <= rob_branch_update_valid;
			last_rob_branch_update_has_checkpoint <= rob_branch_update_has_checkpoint;
			last_rob_branch_update_checkpoint_index <= rob_branch_update_checkpoint_index;
			last_rob_branch_update_is_mispredict <= rob_branch_update_is_mispredict;
			last_rob_branch_update_is_taken <= rob_branch_update_is_taken;
			last_rob_branch_update_use_upct <= rob_branch_update_use_upct;
			last_rob_branch_update_intermediate_pred_info <= rob_branch_update_intermediate_pred_info;
			last_rob_branch_update_pred_lru <= rob_branch_update_pred_lru;
			last_rob_branch_update_start_PC <= rob_branch_update_start_PC;
			last_rob_branch_update_target_PC <= rob_branch_update_target_PC;

		    // ROB control of rename
			last_rob_controlling_rename <= rob_controlling_rename;

			last_rob_checkpoint_map_table_restore_valid <= rob_checkpoint_map_table_restore_valid;
			last_rob_checkpoint_map_table_restore_index <= rob_checkpoint_map_table_restore_index;

			last_rob_checkpoint_clear_valid <= rob_checkpoint_clear_valid;
			last_rob_checkpoint_clear_index <= rob_checkpoint_clear_index;

			last_rob_map_table_write_valid_by_port <= rob_map_table_write_valid_by_port;
			last_rob_map_table_write_AR_by_port <= rob_map_table_write_AR_by_port;
			last_rob_map_table_write_PR_by_port <= rob_map_table_write_PR_by_port;

			// ROB physical register freeing
			last_rob_PR_free_req_valid_by_bank <= rob_PR_free_req_valid_by_bank;
			last_rob_PR_free_req_PR_by_bank <= rob_PR_free_req_PR_by_bank;
			rob_PR_free_resp_ack_by_bank <= next_rob_PR_free_resp_ack_by_bank;
        end
    end

endmodule