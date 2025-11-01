/*
    Filename: rob_tb.sv
    Author: zlagpacan
    Description: Testbench for rob module. 
    Spec: LOROF/spec/design/rob.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module rob_tb #(
	parameter ROB_ENTRIES = 128,
	parameter LOG_ROB_ENTRIES = $clog2(ROB_ENTRIES),
	parameter ROB_MISPRED_Q_ENTRIES = 2,
	parameter ROB_PR_FREE_Q_ENTRIES = 2,
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
) ();

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

    // 4-way ROB dispatch:
	logic tb_dispatch_enq_valid;
	logic tb_dispatch_enq_killed;
    // general instr info
	logic [3:0] tb_dispatch_valid_by_way;
	logic [3:0] tb_dispatch_uncompressed_by_way;
	logic [3:0][31:0] tb_dispatch_PC_by_way;
	logic [3:0] tb_dispatch_is_rename_by_way;
    // exception info
	logic tb_dispatch_is_page_fault;
	logic tb_dispatch_is_access_fault;
	logic tb_dispatch_is_illegal_instr;
	logic tb_dispatch_exception_present;
	logic [1:0] tb_dispatch_exception_index;
	logic [31:0] tb_dispatch_illegal_instr32;
	// checkpoint info
	logic tb_dispatch_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] tb_dispatch_checkpoint_index;
    // dest operand
	logic [3:0][4:0] tb_dispatch_dest_AR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_old_PR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_new_PR_by_way;

    // ROB dispatch feedback
	logic DUT_dispatch_enq_ready, expected_dispatch_enq_ready;
	logic [3:0][LOG_ROB_ENTRIES-1:0] DUT_dispatch_enq_ROB_index_by_way, expected_dispatch_enq_ROB_index_by_way;

    // writeback bus complete notif by bank
	logic [PRF_BANK_COUNT-1:0] tb_complete_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] tb_complete_bus_ROB_index_by_bank;

    // LDU complete notif
	logic tb_ldu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_complete_ROB_index;

    // STAMOFU complete notif
	logic tb_stamofu_complete_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_complete_ROB_index;

    // branch notification to ROB
	logic tb_branch_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_branch_notif_ROB_index;
	logic tb_branch_notif_is_mispredict;
	logic tb_branch_notif_is_taken;
	logic tb_branch_notif_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_branch_notif_updated_pred_info;
	logic tb_branch_notif_pred_lru;
	logic [31:0] tb_branch_notif_start_PC;
	logic [31:0] tb_branch_notif_target_PC;

    // branch notification backpressure from ROB
	logic DUT_branch_notif_ready, expected_branch_notif_ready;

    // LDU misprediction notification to ROB
	logic tb_ldu_mispred_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_mispred_notif_ROB_index;

    // LDU misprediction notification backpressure from ROB
	logic DUT_ldu_mispred_notif_ready, expected_ldu_mispred_notif_ready;

    // fence restart notification to ROB
	logic tb_fence_restart_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_fence_restart_notif_ROB_index;

    // fence restart notification backpressure from ROB
	logic DUT_fence_restart_notif_ready, expected_fence_restart_notif_ready;

    // LDU exception to ROB
	logic tb_ldu_exception_valid;
	logic [VA_WIDTH-1:0] tb_ldu_exception_VA;
	logic tb_ldu_exception_page_fault;
	logic tb_ldu_exception_access_fault;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_exception_ROB_index;

    // LDU exception backpressure from ROB
	logic DUT_ldu_exception_ready, expected_ldu_exception_ready;

    // STAMOFU exception to ROB
	logic tb_stamofu_exception_valid;
	logic [VA_WIDTH-1:0] tb_stamofu_exception_VA;
	logic tb_stamofu_exception_is_lr;
	logic tb_stamofu_exception_page_fault;
	logic tb_stamofu_exception_access_fault;
	logic tb_stamofu_exception_misaligned_exception;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_exception_ROB_index;

    // STAMOFU exception backpressure from ROB
	logic DUT_stamofu_exception_ready, expected_stamofu_exception_ready;

    // mdp update to ROB
	logic tb_ssu_mdp_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_ssu_mdp_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_ssu_mdp_update_ROB_index;

    // mdp update feedback from ROB
	logic DUT_ssu_mdp_update_ready, expected_ssu_mdp_update_ready;

    // mdpt update to fetch unit
	logic DUT_fetch_unit_mdpt_update_valid, expected_fetch_unit_mdpt_update_valid;
	logic [31:0] DUT_fetch_unit_mdpt_update_start_full_PC, expected_fetch_unit_mdpt_update_start_full_PC;
	logic [ASID_WIDTH-1:0] DUT_fetch_unit_mdpt_update_ASID, expected_fetch_unit_mdpt_update_ASID;
	logic [MDPT_INFO_WIDTH-1:0] DUT_fetch_unit_mdpt_update_mdp_info, expected_fetch_unit_mdpt_update_mdp_info;

    // ROB commit
	logic [LOG_ROB_ENTRIES-3:0] DUT_rob_commit_upper_index, expected_rob_commit_upper_index;
	logic [3:0] DUT_rob_commit_lower_index_valid_mask, expected_rob_commit_lower_index_valid_mask;

    // restart from ROB
	logic DUT_rob_restart_valid, expected_rob_restart_valid;
	logic [31:0] DUT_rob_restart_PC, expected_rob_restart_PC;
	logic [ASID_WIDTH-1:0] DUT_rob_restart_ASID, expected_rob_restart_ASID;
	logic [1:0] DUT_rob_restart_exec_mode, expected_rob_restart_exec_mode;
	logic DUT_rob_restart_virtual_mode, expected_rob_restart_virtual_mode;
	logic DUT_rob_restart_MXR, expected_rob_restart_MXR;
	logic DUT_rob_restart_SUM, expected_rob_restart_SUM;
	logic DUT_rob_restart_trap_sfence, expected_rob_restart_trap_sfence;
	logic DUT_rob_restart_trap_wfi, expected_rob_restart_trap_wfi;
	logic DUT_rob_restart_trap_sret, expected_rob_restart_trap_sret;

    // ROB kill
	logic DUT_rob_kill_valid, expected_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] DUT_rob_kill_abs_head_index, expected_rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] DUT_rob_kill_rel_kill_younger_index, expected_rob_kill_rel_kill_younger_index;

    // branch update from ROB
	logic DUT_rob_branch_update_valid, expected_rob_branch_update_valid;
	logic DUT_rob_branch_update_has_checkpoint, expected_rob_branch_update_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] DUT_rob_branch_update_checkpoint_index, expected_rob_branch_update_checkpoint_index;
	logic DUT_rob_branch_update_is_mispredict, expected_rob_branch_update_is_mispredict;
	logic DUT_rob_branch_update_is_taken, expected_rob_branch_update_is_taken;
	logic DUT_rob_branch_update_use_upct, expected_rob_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_rob_branch_update_intermediate_pred_info, expected_rob_branch_update_intermediate_pred_info;
	logic DUT_rob_branch_update_pred_lru, expected_rob_branch_update_pred_lru;
	logic [31:0] DUT_rob_branch_update_start_PC, expected_rob_branch_update_start_PC;
	logic [31:0] DUT_rob_branch_update_target_PC, expected_rob_branch_update_target_PC;

    // ROB control of rename
	logic DUT_rob_controlling_rename, expected_rob_controlling_rename;

	logic DUT_rob_checkpoint_map_table_restore_valid, expected_rob_checkpoint_map_table_restore_valid;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] DUT_rob_checkpoint_map_table_restore_index, expected_rob_checkpoint_map_table_restore_index;

	logic DUT_rob_checkpoint_clear_valid, expected_rob_checkpoint_clear_valid;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] DUT_rob_checkpoint_clear_index, expected_rob_checkpoint_clear_index;

	logic [3:0] DUT_rob_map_table_write_valid_by_port, expected_rob_map_table_write_valid_by_port;
	logic [3:0][LOG_AR_COUNT-1:0] DUT_rob_map_table_write_AR_by_port, expected_rob_map_table_write_AR_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] DUT_rob_map_table_write_PR_by_port, expected_rob_map_table_write_PR_by_port;

	// ROB physical register freeing
	logic [3:0] DUT_rob_PR_free_req_valid_by_bank, expected_rob_PR_free_req_valid_by_bank;
	logic [3:0][LOG_PR_COUNT-1:0] DUT_rob_PR_free_req_PR_by_bank, expected_rob_PR_free_req_PR_by_bank;
	logic [3:0] tb_rob_PR_free_resp_ack_by_bank;

	// ROB instret advertisement
	logic [31:0] DUT_rob_instret, expected_rob_instret;

	// ROB instret write
	logic tb_rob_instret_write_valid;
	logic [31:0] tb_rob_instret_write_data;

    // ----------------------------------------------------------------
    // DUT instantiation:

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
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // 4-way ROB dispatch:
		.dispatch_enq_valid(tb_dispatch_enq_valid),
		.dispatch_enq_killed(tb_dispatch_enq_killed),
	    // general instr info
		.dispatch_valid_by_way(tb_dispatch_valid_by_way),
		.dispatch_uncompressed_by_way(tb_dispatch_uncompressed_by_way),
		.dispatch_PC_by_way(tb_dispatch_PC_by_way),
		.dispatch_is_rename_by_way(tb_dispatch_is_rename_by_way),
	    // exception info
		.dispatch_is_page_fault(tb_dispatch_is_page_fault),
		.dispatch_is_access_fault(tb_dispatch_is_access_fault),
		.dispatch_is_illegal_instr(tb_dispatch_is_illegal_instr),
		.dispatch_exception_present(tb_dispatch_exception_present),
		.dispatch_exception_index(tb_dispatch_exception_index),
		.dispatch_illegal_instr32(tb_dispatch_illegal_instr32),
		// checkpoint info
		.dispatch_has_checkpoint(tb_dispatch_has_checkpoint),
		.dispatch_checkpoint_index(tb_dispatch_checkpoint_index),
	    // dest operand
		.dispatch_dest_AR_by_way(tb_dispatch_dest_AR_by_way),
		.dispatch_dest_old_PR_by_way(tb_dispatch_dest_old_PR_by_way),
		.dispatch_dest_new_PR_by_way(tb_dispatch_dest_new_PR_by_way),

	    // ROB dispatch feedback
		.dispatch_enq_ready(DUT_dispatch_enq_ready),
		.dispatch_enq_ROB_index_by_way(DUT_dispatch_enq_ROB_index_by_way),

	    // writeback bus complete notif by bank
		.complete_bus_valid_by_bank(tb_complete_bus_valid_by_bank),
		.complete_bus_ROB_index_by_bank(tb_complete_bus_ROB_index_by_bank),

	    // LDU complete notif
		.ldu_complete_valid(tb_ldu_complete_valid),
		.ldu_complete_ROB_index(tb_ldu_complete_ROB_index),

	    // STAMOFU complete notif
		.stamofu_complete_valid(tb_stamofu_complete_valid),
		.stamofu_complete_ROB_index(tb_stamofu_complete_ROB_index),

	    // branch notification to ROB
		.branch_notif_valid(tb_branch_notif_valid),
		.branch_notif_ROB_index(tb_branch_notif_ROB_index),
		.branch_notif_is_mispredict(tb_branch_notif_is_mispredict),
		.branch_notif_is_taken(tb_branch_notif_is_taken),
		.branch_notif_use_upct(tb_branch_notif_use_upct),
		.branch_notif_updated_pred_info(tb_branch_notif_updated_pred_info),
		.branch_notif_pred_lru(tb_branch_notif_pred_lru),
		.branch_notif_start_PC(tb_branch_notif_start_PC),
		.branch_notif_target_PC(tb_branch_notif_target_PC),

	    // branch notification backpressure from ROB
		.branch_notif_ready(DUT_branch_notif_ready),

	    // LDU misprediction notification to ROB
		.ldu_mispred_notif_valid(tb_ldu_mispred_notif_valid),
		.ldu_mispred_notif_ROB_index(tb_ldu_mispred_notif_ROB_index),

	    // LDU misprediction notification backpressure from ROB
		.ldu_mispred_notif_ready(DUT_ldu_mispred_notif_ready),

	    // fence restart notification to ROB
		.fence_restart_notif_valid(tb_fence_restart_notif_valid),
		.fence_restart_notif_ROB_index(tb_fence_restart_notif_ROB_index),

	    // fence restart notification backpressure from ROB
		.fence_restart_notif_ready(DUT_fence_restart_notif_ready),

	    // LDU exception to ROB
		.ldu_exception_valid(tb_ldu_exception_valid),
		.ldu_exception_VA(tb_ldu_exception_VA),
		.ldu_exception_page_fault(tb_ldu_exception_page_fault),
		.ldu_exception_access_fault(tb_ldu_exception_access_fault),
		.ldu_exception_ROB_index(tb_ldu_exception_ROB_index),

	    // LDU exception backpressure from ROB
		.ldu_exception_ready(DUT_ldu_exception_ready),

	    // STAMOFU exception to ROB
		.stamofu_exception_valid(tb_stamofu_exception_valid),
		.stamofu_exception_VA(tb_stamofu_exception_VA),
		.stamofu_exception_is_lr(tb_stamofu_exception_is_lr),
		.stamofu_exception_page_fault(tb_stamofu_exception_page_fault),
		.stamofu_exception_access_fault(tb_stamofu_exception_access_fault),
		.stamofu_exception_misaligned_exception(tb_stamofu_exception_misaligned_exception),
		.stamofu_exception_ROB_index(tb_stamofu_exception_ROB_index),

	    // STAMOFU exception backpressure from ROB
		.stamofu_exception_ready(DUT_stamofu_exception_ready),

	    // mdp update to ROB
		.ssu_mdp_update_valid(tb_ssu_mdp_update_valid),
		.ssu_mdp_update_mdp_info(tb_ssu_mdp_update_mdp_info),
		.ssu_mdp_update_ROB_index(tb_ssu_mdp_update_ROB_index),

	    // mdp update feedback from ROB
		.ssu_mdp_update_ready(DUT_ssu_mdp_update_ready),

	    // mdpt update to fetch unit
		.fetch_unit_mdpt_update_valid(DUT_fetch_unit_mdpt_update_valid),
		.fetch_unit_mdpt_update_start_full_PC(DUT_fetch_unit_mdpt_update_start_full_PC),
		.fetch_unit_mdpt_update_ASID(DUT_fetch_unit_mdpt_update_ASID),
		.fetch_unit_mdpt_update_mdp_info(DUT_fetch_unit_mdpt_update_mdp_info),

	    // ROB commit
		.rob_commit_upper_index(DUT_rob_commit_upper_index),
		.rob_commit_lower_index_valid_mask(DUT_rob_commit_lower_index_valid_mask),

	    // restart from ROB
		.rob_restart_valid(DUT_rob_restart_valid),
		.rob_restart_PC(DUT_rob_restart_PC),
		.rob_restart_ASID(DUT_rob_restart_ASID),
		.rob_restart_exec_mode(DUT_rob_restart_exec_mode),
		.rob_restart_virtual_mode(DUT_rob_restart_virtual_mode),
		.rob_restart_MXR(DUT_rob_restart_MXR),
		.rob_restart_SUM(DUT_rob_restart_SUM),
		.rob_restart_trap_sfence(DUT_rob_restart_trap_sfence),
		.rob_restart_trap_wfi(DUT_rob_restart_trap_wfi),
		.rob_restart_trap_sret(DUT_rob_restart_trap_sret),

	    // ROB kill
		.rob_kill_valid(DUT_rob_kill_valid),
		.rob_kill_abs_head_index(DUT_rob_kill_abs_head_index),
		.rob_kill_rel_kill_younger_index(DUT_rob_kill_rel_kill_younger_index),

	    // branch update from ROB
		.rob_branch_update_valid(DUT_rob_branch_update_valid),
		.rob_branch_update_has_checkpoint(DUT_rob_branch_update_has_checkpoint),
		.rob_branch_update_checkpoint_index(DUT_rob_branch_update_checkpoint_index),
		.rob_branch_update_is_mispredict(DUT_rob_branch_update_is_mispredict),
		.rob_branch_update_is_taken(DUT_rob_branch_update_is_taken),
		.rob_branch_update_use_upct(DUT_rob_branch_update_use_upct),
		.rob_branch_update_intermediate_pred_info(DUT_rob_branch_update_intermediate_pred_info),
		.rob_branch_update_pred_lru(DUT_rob_branch_update_pred_lru),
		.rob_branch_update_start_PC(DUT_rob_branch_update_start_PC),
		.rob_branch_update_target_PC(DUT_rob_branch_update_target_PC),

	    // ROB control of rename
		.rob_controlling_rename(DUT_rob_controlling_rename),

		.rob_checkpoint_map_table_restore_valid(DUT_rob_checkpoint_map_table_restore_valid),
		.rob_checkpoint_map_table_restore_index(DUT_rob_checkpoint_map_table_restore_index),

		.rob_checkpoint_clear_valid(DUT_rob_checkpoint_clear_valid),
		.rob_checkpoint_clear_index(DUT_rob_checkpoint_clear_index),

		.rob_map_table_write_valid_by_port(DUT_rob_map_table_write_valid_by_port),
		.rob_map_table_write_AR_by_port(DUT_rob_map_table_write_AR_by_port),
		.rob_map_table_write_PR_by_port(DUT_rob_map_table_write_PR_by_port),

		// ROB physical register freeing
		.rob_PR_free_req_valid_by_bank(DUT_rob_PR_free_req_valid_by_bank),
		.rob_PR_free_req_PR_by_bank(DUT_rob_PR_free_req_PR_by_bank),
		.rob_PR_free_resp_ack_by_bank(tb_rob_PR_free_resp_ack_by_bank),

		// ROB instret advertisement
		.rob_instret(DUT_rob_instret),

		// ROB instret write
		.rob_instret_write_valid(tb_rob_instret_write_valid),
		.rob_instret_write_data(tb_rob_instret_write_data)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_dispatch_enq_ready !== DUT_dispatch_enq_ready) begin
			$display("TB ERROR: expected_dispatch_enq_ready (%h) != DUT_dispatch_enq_ready (%h)",
				expected_dispatch_enq_ready, DUT_dispatch_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_enq_ROB_index_by_way !== DUT_dispatch_enq_ROB_index_by_way) begin
			$display("TB ERROR: expected_dispatch_enq_ROB_index_by_way (%h) != DUT_dispatch_enq_ROB_index_by_way (%h)",
				expected_dispatch_enq_ROB_index_by_way, DUT_dispatch_enq_ROB_index_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_ready !== DUT_branch_notif_ready) begin
			$display("TB ERROR: expected_branch_notif_ready (%h) != DUT_branch_notif_ready (%h)",
				expected_branch_notif_ready, DUT_branch_notif_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_mispred_notif_ready !== DUT_ldu_mispred_notif_ready) begin
			$display("TB ERROR: expected_ldu_mispred_notif_ready (%h) != DUT_ldu_mispred_notif_ready (%h)",
				expected_ldu_mispred_notif_ready, DUT_ldu_mispred_notif_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_fence_restart_notif_ready !== DUT_fence_restart_notif_ready) begin
			$display("TB ERROR: expected_fence_restart_notif_ready (%h) != DUT_fence_restart_notif_ready (%h)",
				expected_fence_restart_notif_ready, DUT_fence_restart_notif_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_exception_ready !== DUT_ldu_exception_ready) begin
			$display("TB ERROR: expected_ldu_exception_ready (%h) != DUT_ldu_exception_ready (%h)",
				expected_ldu_exception_ready, DUT_ldu_exception_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_exception_ready !== DUT_stamofu_exception_ready) begin
			$display("TB ERROR: expected_stamofu_exception_ready (%h) != DUT_stamofu_exception_ready (%h)",
				expected_stamofu_exception_ready, DUT_stamofu_exception_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ssu_mdp_update_ready !== DUT_ssu_mdp_update_ready) begin
			$display("TB ERROR: expected_ssu_mdp_update_ready (%h) != DUT_ssu_mdp_update_ready (%h)",
				expected_ssu_mdp_update_ready, DUT_ssu_mdp_update_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_fetch_unit_mdpt_update_valid !== DUT_fetch_unit_mdpt_update_valid) begin
			$display("TB ERROR: expected_fetch_unit_mdpt_update_valid (%h) != DUT_fetch_unit_mdpt_update_valid (%h)",
				expected_fetch_unit_mdpt_update_valid, DUT_fetch_unit_mdpt_update_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_fetch_unit_mdpt_update_start_full_PC !== DUT_fetch_unit_mdpt_update_start_full_PC) begin
			$display("TB ERROR: expected_fetch_unit_mdpt_update_start_full_PC (%h) != DUT_fetch_unit_mdpt_update_start_full_PC (%h)",
				expected_fetch_unit_mdpt_update_start_full_PC, DUT_fetch_unit_mdpt_update_start_full_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_fetch_unit_mdpt_update_ASID !== DUT_fetch_unit_mdpt_update_ASID) begin
			$display("TB ERROR: expected_fetch_unit_mdpt_update_ASID (%h) != DUT_fetch_unit_mdpt_update_ASID (%h)",
				expected_fetch_unit_mdpt_update_ASID, DUT_fetch_unit_mdpt_update_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_fetch_unit_mdpt_update_mdp_info !== DUT_fetch_unit_mdpt_update_mdp_info) begin
			$display("TB ERROR: expected_fetch_unit_mdpt_update_mdp_info (%h) != DUT_fetch_unit_mdpt_update_mdp_info (%h)",
				expected_fetch_unit_mdpt_update_mdp_info, DUT_fetch_unit_mdpt_update_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_commit_upper_index !== DUT_rob_commit_upper_index) begin
			$display("TB ERROR: expected_rob_commit_upper_index (%h) != DUT_rob_commit_upper_index (%h)",
				expected_rob_commit_upper_index, DUT_rob_commit_upper_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_commit_lower_index_valid_mask !== DUT_rob_commit_lower_index_valid_mask) begin
			$display("TB ERROR: expected_rob_commit_lower_index_valid_mask (%h) != DUT_rob_commit_lower_index_valid_mask (%h)",
				expected_rob_commit_lower_index_valid_mask, DUT_rob_commit_lower_index_valid_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_valid !== DUT_rob_restart_valid) begin
			$display("TB ERROR: expected_rob_restart_valid (%h) != DUT_rob_restart_valid (%h)",
				expected_rob_restart_valid, DUT_rob_restart_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_PC !== DUT_rob_restart_PC) begin
			$display("TB ERROR: expected_rob_restart_PC (%h) != DUT_rob_restart_PC (%h)",
				expected_rob_restart_PC, DUT_rob_restart_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_ASID !== DUT_rob_restart_ASID) begin
			$display("TB ERROR: expected_rob_restart_ASID (%h) != DUT_rob_restart_ASID (%h)",
				expected_rob_restart_ASID, DUT_rob_restart_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_exec_mode !== DUT_rob_restart_exec_mode) begin
			$display("TB ERROR: expected_rob_restart_exec_mode (%h) != DUT_rob_restart_exec_mode (%h)",
				expected_rob_restart_exec_mode, DUT_rob_restart_exec_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_virtual_mode !== DUT_rob_restart_virtual_mode) begin
			$display("TB ERROR: expected_rob_restart_virtual_mode (%h) != DUT_rob_restart_virtual_mode (%h)",
				expected_rob_restart_virtual_mode, DUT_rob_restart_virtual_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_MXR !== DUT_rob_restart_MXR) begin
			$display("TB ERROR: expected_rob_restart_MXR (%h) != DUT_rob_restart_MXR (%h)",
				expected_rob_restart_MXR, DUT_rob_restart_MXR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_SUM !== DUT_rob_restart_SUM) begin
			$display("TB ERROR: expected_rob_restart_SUM (%h) != DUT_rob_restart_SUM (%h)",
				expected_rob_restart_SUM, DUT_rob_restart_SUM);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_trap_sfence !== DUT_rob_restart_trap_sfence) begin
			$display("TB ERROR: expected_rob_restart_trap_sfence (%h) != DUT_rob_restart_trap_sfence (%h)",
				expected_rob_restart_trap_sfence, DUT_rob_restart_trap_sfence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_trap_wfi !== DUT_rob_restart_trap_wfi) begin
			$display("TB ERROR: expected_rob_restart_trap_wfi (%h) != DUT_rob_restart_trap_wfi (%h)",
				expected_rob_restart_trap_wfi, DUT_rob_restart_trap_wfi);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_restart_trap_sret !== DUT_rob_restart_trap_sret) begin
			$display("TB ERROR: expected_rob_restart_trap_sret (%h) != DUT_rob_restart_trap_sret (%h)",
				expected_rob_restart_trap_sret, DUT_rob_restart_trap_sret);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_kill_valid !== DUT_rob_kill_valid) begin
			$display("TB ERROR: expected_rob_kill_valid (%h) != DUT_rob_kill_valid (%h)",
				expected_rob_kill_valid, DUT_rob_kill_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_kill_abs_head_index !== DUT_rob_kill_abs_head_index) begin
			$display("TB ERROR: expected_rob_kill_abs_head_index (%h) != DUT_rob_kill_abs_head_index (%h)",
				expected_rob_kill_abs_head_index, DUT_rob_kill_abs_head_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_kill_rel_kill_younger_index !== DUT_rob_kill_rel_kill_younger_index) begin
			$display("TB ERROR: expected_rob_kill_rel_kill_younger_index (%h) != DUT_rob_kill_rel_kill_younger_index (%h)",
				expected_rob_kill_rel_kill_younger_index, DUT_rob_kill_rel_kill_younger_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_valid !== DUT_rob_branch_update_valid) begin
			$display("TB ERROR: expected_rob_branch_update_valid (%h) != DUT_rob_branch_update_valid (%h)",
				expected_rob_branch_update_valid, DUT_rob_branch_update_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_has_checkpoint !== DUT_rob_branch_update_has_checkpoint) begin
			$display("TB ERROR: expected_rob_branch_update_has_checkpoint (%h) != DUT_rob_branch_update_has_checkpoint (%h)",
				expected_rob_branch_update_has_checkpoint, DUT_rob_branch_update_has_checkpoint);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_checkpoint_index !== DUT_rob_branch_update_checkpoint_index) begin
			$display("TB ERROR: expected_rob_branch_update_checkpoint_index (%h) != DUT_rob_branch_update_checkpoint_index (%h)",
				expected_rob_branch_update_checkpoint_index, DUT_rob_branch_update_checkpoint_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_is_mispredict !== DUT_rob_branch_update_is_mispredict) begin
			$display("TB ERROR: expected_rob_branch_update_is_mispredict (%h) != DUT_rob_branch_update_is_mispredict (%h)",
				expected_rob_branch_update_is_mispredict, DUT_rob_branch_update_is_mispredict);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_is_taken !== DUT_rob_branch_update_is_taken) begin
			$display("TB ERROR: expected_rob_branch_update_is_taken (%h) != DUT_rob_branch_update_is_taken (%h)",
				expected_rob_branch_update_is_taken, DUT_rob_branch_update_is_taken);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_use_upct !== DUT_rob_branch_update_use_upct) begin
			$display("TB ERROR: expected_rob_branch_update_use_upct (%h) != DUT_rob_branch_update_use_upct (%h)",
				expected_rob_branch_update_use_upct, DUT_rob_branch_update_use_upct);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_intermediate_pred_info !== DUT_rob_branch_update_intermediate_pred_info) begin
			$display("TB ERROR: expected_rob_branch_update_intermediate_pred_info (%h) != DUT_rob_branch_update_intermediate_pred_info (%h)",
				expected_rob_branch_update_intermediate_pred_info, DUT_rob_branch_update_intermediate_pred_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_pred_lru !== DUT_rob_branch_update_pred_lru) begin
			$display("TB ERROR: expected_rob_branch_update_pred_lru (%h) != DUT_rob_branch_update_pred_lru (%h)",
				expected_rob_branch_update_pred_lru, DUT_rob_branch_update_pred_lru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_start_PC !== DUT_rob_branch_update_start_PC) begin
			$display("TB ERROR: expected_rob_branch_update_start_PC (%h) != DUT_rob_branch_update_start_PC (%h)",
				expected_rob_branch_update_start_PC, DUT_rob_branch_update_start_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_branch_update_target_PC !== DUT_rob_branch_update_target_PC) begin
			$display("TB ERROR: expected_rob_branch_update_target_PC (%h) != DUT_rob_branch_update_target_PC (%h)",
				expected_rob_branch_update_target_PC, DUT_rob_branch_update_target_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_controlling_rename !== DUT_rob_controlling_rename) begin
			$display("TB ERROR: expected_rob_controlling_rename (%h) != DUT_rob_controlling_rename (%h)",
				expected_rob_controlling_rename, DUT_rob_controlling_rename);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_checkpoint_map_table_restore_valid !== DUT_rob_checkpoint_map_table_restore_valid) begin
			$display("TB ERROR: expected_rob_checkpoint_map_table_restore_valid (%h) != DUT_rob_checkpoint_map_table_restore_valid (%h)",
				expected_rob_checkpoint_map_table_restore_valid, DUT_rob_checkpoint_map_table_restore_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_checkpoint_map_table_restore_index !== DUT_rob_checkpoint_map_table_restore_index) begin
			$display("TB ERROR: expected_rob_checkpoint_map_table_restore_index (%h) != DUT_rob_checkpoint_map_table_restore_index (%h)",
				expected_rob_checkpoint_map_table_restore_index, DUT_rob_checkpoint_map_table_restore_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_checkpoint_clear_valid !== DUT_rob_checkpoint_clear_valid) begin
			$display("TB ERROR: expected_rob_checkpoint_clear_valid (%h) != DUT_rob_checkpoint_clear_valid (%h)",
				expected_rob_checkpoint_clear_valid, DUT_rob_checkpoint_clear_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_checkpoint_clear_index !== DUT_rob_checkpoint_clear_index) begin
			$display("TB ERROR: expected_rob_checkpoint_clear_index (%h) != DUT_rob_checkpoint_clear_index (%h)",
				expected_rob_checkpoint_clear_index, DUT_rob_checkpoint_clear_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_map_table_write_valid_by_port !== DUT_rob_map_table_write_valid_by_port) begin
			$display("TB ERROR: expected_rob_map_table_write_valid_by_port (%h) != DUT_rob_map_table_write_valid_by_port (%h)",
				expected_rob_map_table_write_valid_by_port, DUT_rob_map_table_write_valid_by_port);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_map_table_write_AR_by_port !== DUT_rob_map_table_write_AR_by_port) begin
			$display("TB ERROR: expected_rob_map_table_write_AR_by_port (%h) != DUT_rob_map_table_write_AR_by_port (%h)",
				expected_rob_map_table_write_AR_by_port, DUT_rob_map_table_write_AR_by_port);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_map_table_write_PR_by_port !== DUT_rob_map_table_write_PR_by_port) begin
			$display("TB ERROR: expected_rob_map_table_write_PR_by_port (%h) != DUT_rob_map_table_write_PR_by_port (%h)",
				expected_rob_map_table_write_PR_by_port, DUT_rob_map_table_write_PR_by_port);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_PR_free_req_valid_by_bank !== DUT_rob_PR_free_req_valid_by_bank) begin
			$display("TB ERROR: expected_rob_PR_free_req_valid_by_bank (%h) != DUT_rob_PR_free_req_valid_by_bank (%h)",
				expected_rob_PR_free_req_valid_by_bank, DUT_rob_PR_free_req_valid_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_PR_free_req_PR_by_bank !== DUT_rob_PR_free_req_PR_by_bank) begin
			$display("TB ERROR: expected_rob_PR_free_req_PR_by_bank (%h) != DUT_rob_PR_free_req_PR_by_bank (%h)",
				expected_rob_PR_free_req_PR_by_bank, DUT_rob_PR_free_req_PR_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_instret !== DUT_rob_instret) begin
			$display("TB ERROR: expected_rob_instret (%h) != DUT_rob_instret (%h)",
				expected_rob_instret, DUT_rob_instret);
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
	    // 4-way ROB dispatch:
		tb_dispatch_enq_valid = 1'b0;
		tb_dispatch_enq_killed = 1'b0;
	    // general instr info
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_uncompressed_by_way = 4'b0000;
		tb_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_is_rename_by_way = 4'b0000;
	    // exception info
		tb_dispatch_is_page_fault = 1'b0;
		tb_dispatch_is_access_fault = 1'b0;
		tb_dispatch_is_illegal_instr = 1'b0;
		tb_dispatch_exception_present = 1'b0;
		tb_dispatch_exception_index = 2'h0;
		tb_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		tb_dispatch_has_checkpoint = 1'b0;
		tb_dispatch_checkpoint_index = 3'h0;
	    // dest operand
		tb_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h00, 5'h00};
		tb_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_dest_new_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // ROB dispatch feedback
	    // writeback bus complete notif by bank
		tb_complete_bus_valid_by_bank = 4'b0000;
		tb_complete_bus_ROB_index_by_bank = {7'h00, 7'h00, 7'h00, 7'h00};
	    // LDU complete notif
		tb_ldu_complete_valid = 1'b0;
		tb_ldu_complete_ROB_index = 7'h00;
	    // STAMOFU complete notif
		tb_stamofu_complete_valid = 1'b0;
		tb_stamofu_complete_ROB_index = 7'h00;
	    // branch notification to ROB
		tb_branch_notif_valid = 1'b0;
		tb_branch_notif_ROB_index = 7'h00;
		tb_branch_notif_is_mispredict = 1'b0;
		tb_branch_notif_is_taken = 1'b0;
		tb_branch_notif_use_upct = 1'b0;
		tb_branch_notif_updated_pred_info = 8'h00;
		tb_branch_notif_pred_lru = 1'b0;
		tb_branch_notif_start_PC = 32'h00000000;
		tb_branch_notif_target_PC = 32'h00000000;
	    // branch notification backpressure from ROB
	    // LDU misprediction notification to ROB
		tb_ldu_mispred_notif_valid = 1'b0;
		tb_ldu_mispred_notif_ROB_index = 7'h00;
	    // LDU misprediction notification backpressure from ROB
	    // fence restart notification to ROB
		tb_fence_restart_notif_valid = 1'b0;
		tb_fence_restart_notif_ROB_index = 7'h00;
	    // fence restart notification backpressure from ROB
	    // LDU exception to ROB
		tb_ldu_exception_valid = 1'b0;
		tb_ldu_exception_VA = 32'h00000000;
		tb_ldu_exception_page_fault = 1'b0;
		tb_ldu_exception_access_fault = 1'b0;
		tb_ldu_exception_ROB_index = 7'h00;
	    // LDU exception backpressure from ROB
	    // STAMOFU exception to ROB
		tb_stamofu_exception_valid = 1'b0;
		tb_stamofu_exception_VA = 32'h00000000;
		tb_stamofu_exception_is_lr = 1'b0;
		tb_stamofu_exception_page_fault = 1'b0;
		tb_stamofu_exception_access_fault = 1'b0;
		tb_stamofu_exception_misaligned_exception = 1'b0;
		tb_stamofu_exception_ROB_index = 7'h00;
	    // STAMOFU exception backpressure from ROB
	    // mdp update to ROB
		tb_ssu_mdp_update_valid = 1'b0;
		tb_ssu_mdp_update_mdp_info = 8'h00;
		tb_ssu_mdp_update_ROB_index = 7'h00;
	    // mdp update feedback from ROB
	    // mdpt update to fetch unit
	    // ROB commit
	    // restart from ROB
	    // ROB kill
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		tb_rob_PR_free_resp_ack_by_bank = 4'b1111;
		// ROB instret advertisement
		// ROB instret write
		tb_rob_instret_write_valid = 1'b0;
		tb_rob_instret_write_data = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // 4-way ROB dispatch:
	    // general instr info
	    // exception info
		// checkpoint info
	    // instr FU valids
	    // dest operand
	    // ROB dispatch feedback
		expected_dispatch_enq_ready = 1'b1;
		expected_dispatch_enq_ROB_index_by_way = {7'h03, 7'h02, 7'h01, 7'h00};
	    // writeback bus complete notif by bank
	    // LDU complete notif
	    // STAMOFU complete notif
	    // branch notification to ROB
	    // branch notification backpressure from ROB
		expected_branch_notif_ready = 1'b1;
	    // LDU misprediction notification to ROB
	    // LDU misprediction notification backpressure from ROB
		expected_ldu_mispred_notif_ready = 1'b1;
	    // fence restart notification to ROB
	    // fence restart notification backpressure from ROB
		expected_fence_restart_notif_ready = 1'b1;
	    // LDU exception to ROB
	    // LDU exception backpressure from ROB
		expected_ldu_exception_ready = 1'b1;
	    // STAMOFU exception to ROB
	    // STAMOFU exception backpressure from ROB
		expected_stamofu_exception_ready = 1'b1;
	    // mdp update to ROB
	    // mdp update feedback from ROB
		expected_ssu_mdp_update_ready = 1'b1;
	    // mdpt update to fetch unit
		expected_fetch_unit_mdpt_update_valid = 1'b0;
		expected_fetch_unit_mdpt_update_start_full_PC = 32'h00000000;
		expected_fetch_unit_mdpt_update_ASID = 9'h000;
		expected_fetch_unit_mdpt_update_mdp_info = 8'h00;
	    // ROB commit
		expected_rob_commit_upper_index = 5'h00;
		expected_rob_commit_lower_index_valid_mask = 4'b0000;
	    // restart from ROB
		expected_rob_restart_valid = 1'b1;
		expected_rob_restart_PC = 32'h00000000;
		expected_rob_restart_ASID = 9'h000;
		expected_rob_restart_exec_mode = M_MODE;
		expected_rob_restart_virtual_mode = 1'b0;
		expected_rob_restart_MXR = 1'b0;
		expected_rob_restart_SUM = 1'b0;
		expected_rob_restart_trap_sfence = 1'b0;
		expected_rob_restart_trap_wfi = 1'b0;
		expected_rob_restart_trap_sret = 1'b0;
	    // ROB kill
		expected_rob_kill_valid = 1'b0;
		expected_rob_kill_abs_head_index = 7'h0;
		expected_rob_kill_rel_kill_younger_index = 7'h0;
	    // branch update from ROB
		expected_rob_branch_update_valid = 1'b0;
		expected_rob_branch_update_has_checkpoint = 1'b0;
		expected_rob_branch_update_checkpoint_index = 3'h0;
		expected_rob_branch_update_is_mispredict = 1'b0;
		expected_rob_branch_update_is_taken = 1'b0;
		expected_rob_branch_update_use_upct = 1'b0;
		expected_rob_branch_update_intermediate_pred_info = 8'h00;
		expected_rob_branch_update_pred_lru = 1'b0;
		expected_rob_branch_update_start_PC = 32'h00000000;
		expected_rob_branch_update_target_PC = 32'h00000000;
	    // ROB control of rename
		expected_rob_controlling_rename = 1'b0;
		expected_rob_checkpoint_map_table_restore_valid = 1'b0;
		expected_rob_checkpoint_map_table_restore_index = 3'h0;
		expected_rob_checkpoint_clear_valid = 1'b0;
		expected_rob_checkpoint_clear_index = 3'h0;
		expected_rob_map_table_write_valid_by_port = 4'b0000;
		expected_rob_map_table_write_AR_by_port = {5'h00, 5'h00, 5'h00, 5'h00};
		expected_rob_map_table_write_PR_by_port = {7'h00, 7'h00, 7'h00, 7'h00};
		// ROB physical register freeing
		expected_rob_PR_free_req_valid_by_bank = 4'b0000;
		expected_rob_PR_free_req_PR_by_bank = {7'h00, 7'h00, 7'h00, 7'h00};
		// ROB instret advertisement
		expected_rob_instret = 32'h0;
		// ROB instret write

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // 4-way ROB dispatch:
		tb_dispatch_enq_valid = 1'b0;
		tb_dispatch_enq_killed = 1'b0;
	    // general instr info
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_uncompressed_by_way = 4'b0000;
		tb_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_is_rename_by_way = 4'b0000;
	    // exception info
		tb_dispatch_is_page_fault = 1'b0;
		tb_dispatch_is_access_fault = 1'b0;
		tb_dispatch_is_illegal_instr = 1'b0;
		tb_dispatch_exception_present = 1'b0;
		tb_dispatch_exception_index = 2'h0;
		tb_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		tb_dispatch_has_checkpoint = 1'b0;
		tb_dispatch_checkpoint_index = 3'h0;
	    // dest operand
		tb_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h00, 5'h00};
		tb_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_dest_new_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // ROB dispatch feedback
	    // writeback bus complete notif by bank
		tb_complete_bus_valid_by_bank = 4'b0000;
		tb_complete_bus_ROB_index_by_bank = {7'h00, 7'h00, 7'h00, 7'h00};
	    // LDU complete notif
		tb_ldu_complete_valid = 1'b0;
		tb_ldu_complete_ROB_index = 7'h00;
	    // STAMOFU complete notif
		tb_stamofu_complete_valid = 1'b0;
		tb_stamofu_complete_ROB_index = 7'h00;
	    // branch notification to ROB
		tb_branch_notif_valid = 1'b0;
		tb_branch_notif_ROB_index = 7'h00;
		tb_branch_notif_is_mispredict = 1'b0;
		tb_branch_notif_is_taken = 1'b0;
		tb_branch_notif_use_upct = 1'b0;
		tb_branch_notif_updated_pred_info = 8'h00;
		tb_branch_notif_pred_lru = 1'b0;
		tb_branch_notif_start_PC = 32'h00000000;
		tb_branch_notif_target_PC = 32'h00000000;
	    // branch notification backpressure from ROB
	    // LDU misprediction notification to ROB
		tb_ldu_mispred_notif_valid = 1'b0;
		tb_ldu_mispred_notif_ROB_index = 7'h00;
	    // LDU misprediction notification backpressure from ROB
	    // fence restart notification to ROB
		tb_fence_restart_notif_valid = 1'b0;
		tb_fence_restart_notif_ROB_index = 7'h00;
	    // fence restart notification backpressure from ROB
	    // LDU exception to ROB
		tb_ldu_exception_valid = 1'b0;
		tb_ldu_exception_VA = 32'h00000000;
		tb_ldu_exception_page_fault = 1'b0;
		tb_ldu_exception_access_fault = 1'b0;
		tb_ldu_exception_ROB_index = 7'h00;
	    // LDU exception backpressure from ROB
	    // STAMOFU exception to ROB
		tb_stamofu_exception_valid = 1'b0;
		tb_stamofu_exception_VA = 32'h00000000;
		tb_stamofu_exception_is_lr = 1'b0;
		tb_stamofu_exception_page_fault = 1'b0;
		tb_stamofu_exception_access_fault = 1'b0;
		tb_stamofu_exception_misaligned_exception = 1'b0;
		tb_stamofu_exception_ROB_index = 7'h00;
	    // STAMOFU exception backpressure from ROB
	    // mdp update to ROB
		tb_ssu_mdp_update_valid = 1'b0;
		tb_ssu_mdp_update_mdp_info = 8'h00;
		tb_ssu_mdp_update_ROB_index = 7'h00;
	    // mdp update feedback from ROB
	    // mdpt update to fetch unit
	    // ROB commit
	    // restart from ROB
	    // ROB kill
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		tb_rob_PR_free_resp_ack_by_bank = 4'b1111;
		// ROB instret advertisement
		// ROB instret write
		tb_rob_instret_write_valid = 1'b0;
		tb_rob_instret_write_data = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // 4-way ROB dispatch:
	    // general instr info
	    // exception info
		// checkpoint info
	    // instr FU valids
	    // dest operand
	    // ROB dispatch feedback
		expected_dispatch_enq_ready = 1'b1;
		expected_dispatch_enq_ROB_index_by_way = {7'h03, 7'h02, 7'h01, 7'h00};
	    // writeback bus complete notif by bank
	    // LDU complete notif
	    // STAMOFU complete notif
	    // branch notification to ROB
	    // branch notification backpressure from ROB
		expected_branch_notif_ready = 1'b1;
	    // LDU misprediction notification to ROB
	    // LDU misprediction notification backpressure from ROB
		expected_ldu_mispred_notif_ready = 1'b1;
	    // fence restart notification to ROB
	    // fence restart notification backpressure from ROB
		expected_fence_restart_notif_ready = 1'b1;
	    // LDU exception to ROB
	    // LDU exception backpressure from ROB
		expected_ldu_exception_ready = 1'b1;
	    // STAMOFU exception to ROB
	    // STAMOFU exception backpressure from ROB
		expected_stamofu_exception_ready = 1'b1;
	    // mdp update to ROB
	    // mdp update feedback from ROB
		expected_ssu_mdp_update_ready = 1'b1;
	    // mdpt update to fetch unit
		expected_fetch_unit_mdpt_update_valid = 1'b0;
		expected_fetch_unit_mdpt_update_start_full_PC = 32'h00000000;
		expected_fetch_unit_mdpt_update_ASID = 9'h000;
		expected_fetch_unit_mdpt_update_mdp_info = 8'h00;
	    // ROB commit
		expected_rob_commit_upper_index = 5'h00;
		expected_rob_commit_lower_index_valid_mask = 4'b0000;
	    // restart from ROB
		expected_rob_restart_valid = 1'b0;
		expected_rob_restart_PC = 32'h00000000;
		expected_rob_restart_ASID = 9'h000;
		expected_rob_restart_exec_mode = M_MODE;
		expected_rob_restart_virtual_mode = 1'b0;
		expected_rob_restart_MXR = 1'b0;
		expected_rob_restart_SUM = 1'b0;
		expected_rob_restart_trap_sfence = 1'b0;
		expected_rob_restart_trap_wfi = 1'b0;
		expected_rob_restart_trap_sret = 1'b0;
	    // ROB kill
		expected_rob_kill_valid = 1'b0;
		expected_rob_kill_abs_head_index = 7'h0;
		expected_rob_kill_rel_kill_younger_index = 7'h0;
	    // branch update from ROB
		expected_rob_branch_update_valid = 1'b0;
		expected_rob_branch_update_has_checkpoint = 1'b0;
		expected_rob_branch_update_checkpoint_index = 3'h0;
		expected_rob_branch_update_is_mispredict = 1'b0;
		expected_rob_branch_update_is_taken = 1'b0;
		expected_rob_branch_update_use_upct = 1'b0;
		expected_rob_branch_update_intermediate_pred_info = 8'h00;
		expected_rob_branch_update_pred_lru = 1'b0;
		expected_rob_branch_update_start_PC = 32'h00000000;
		expected_rob_branch_update_target_PC = 32'h00000000;
	    // ROB control of rename
		expected_rob_controlling_rename = 1'b0;
		expected_rob_checkpoint_map_table_restore_valid = 1'b0;
		expected_rob_checkpoint_map_table_restore_index = 3'h0;
		expected_rob_checkpoint_clear_valid = 1'b0;
		expected_rob_checkpoint_clear_index = 3'h0;
		expected_rob_map_table_write_valid_by_port = 4'b0000;
		expected_rob_map_table_write_AR_by_port = {5'h00, 5'h00, 5'h00, 5'h00};
		expected_rob_map_table_write_PR_by_port = {7'h00, 7'h00, 7'h00, 7'h00};
		// ROB physical register freeing
		expected_rob_PR_free_req_valid_by_bank = 4'b0000;
		expected_rob_PR_free_req_PR_by_bank = {7'h00, 7'h00, 7'h00, 7'h00};
		// ROB instret advertisement
		expected_rob_instret = 32'h0;
		// ROB instret write

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "default";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // 4-way ROB dispatch:
		tb_dispatch_enq_valid = 1'b0;
		tb_dispatch_enq_killed = 1'b0;
	    // general instr info
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_uncompressed_by_way = 4'b0000;
		tb_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_is_rename_by_way = 4'b0000;
	    // exception info
		tb_dispatch_is_page_fault = 1'b0;
		tb_dispatch_is_access_fault = 1'b0;
		tb_dispatch_is_illegal_instr = 1'b0;
		tb_dispatch_exception_present = 1'b0;
		tb_dispatch_exception_index = 2'h0;
		tb_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		tb_dispatch_has_checkpoint = 1'b0;
		tb_dispatch_checkpoint_index = 3'h0;
	    // dest operand
		tb_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h00, 5'h00};
		tb_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_dest_new_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // ROB dispatch feedback
	    // writeback bus complete notif by bank
		tb_complete_bus_valid_by_bank = 4'b0000;
		tb_complete_bus_ROB_index_by_bank = {7'h00, 7'h00, 7'h00, 7'h00};
	    // LDU complete notif
		tb_ldu_complete_valid = 1'b0;
		tb_ldu_complete_ROB_index = 7'h00;
	    // STAMOFU complete notif
		tb_stamofu_complete_valid = 1'b0;
		tb_stamofu_complete_ROB_index = 7'h00;
	    // branch notification to ROB
		tb_branch_notif_valid = 1'b0;
		tb_branch_notif_ROB_index = 7'h00;
		tb_branch_notif_is_mispredict = 1'b0;
		tb_branch_notif_is_taken = 1'b0;
		tb_branch_notif_use_upct = 1'b0;
		tb_branch_notif_updated_pred_info = 8'h00;
		tb_branch_notif_pred_lru = 1'b0;
		tb_branch_notif_start_PC = 32'h00000000;
		tb_branch_notif_target_PC = 32'h00000000;
	    // branch notification backpressure from ROB
	    // LDU misprediction notification to ROB
		tb_ldu_mispred_notif_valid = 1'b0;
		tb_ldu_mispred_notif_ROB_index = 7'h00;
	    // LDU misprediction notification backpressure from ROB
	    // fence restart notification to ROB
		tb_fence_restart_notif_valid = 1'b0;
		tb_fence_restart_notif_ROB_index = 7'h00;
	    // fence restart notification backpressure from ROB
	    // LDU exception to ROB
		tb_ldu_exception_valid = 1'b0;
		tb_ldu_exception_VA = 32'h00000000;
		tb_ldu_exception_page_fault = 1'b0;
		tb_ldu_exception_access_fault = 1'b0;
		tb_ldu_exception_ROB_index = 7'h00;
	    // LDU exception backpressure from ROB
	    // STAMOFU exception to ROB
		tb_stamofu_exception_valid = 1'b0;
		tb_stamofu_exception_VA = 32'h00000000;
		tb_stamofu_exception_is_lr = 1'b0;
		tb_stamofu_exception_page_fault = 1'b0;
		tb_stamofu_exception_access_fault = 1'b0;
		tb_stamofu_exception_misaligned_exception = 1'b0;
		tb_stamofu_exception_ROB_index = 7'h00;
	    // STAMOFU exception backpressure from ROB
	    // mdp update to ROB
		tb_ssu_mdp_update_valid = 1'b0;
		tb_ssu_mdp_update_mdp_info = 8'h00;
		tb_ssu_mdp_update_ROB_index = 7'h00;
	    // mdp update feedback from ROB
	    // mdpt update to fetch unit
	    // ROB commit
	    // restart from ROB
	    // ROB kill
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		tb_rob_PR_free_resp_ack_by_bank = 4'b1111;
		// ROB instret advertisement
		// ROB instret write
		tb_rob_instret_write_valid = 1'b0;
		tb_rob_instret_write_data = 32'h0;

		@(negedge CLK);

		// outputs:

	    // 4-way ROB dispatch:
	    // general instr info
	    // exception info
		// checkpoint info
	    // instr FU valids
	    // dest operand
	    // ROB dispatch feedback
		expected_dispatch_enq_ready = 1'b1;
		expected_dispatch_enq_ROB_index_by_way = {7'h03, 7'h02, 7'h01, 7'h00};
	    // writeback bus complete notif by bank
	    // LDU complete notif
	    // STAMOFU complete notif
	    // branch notification to ROB
	    // branch notification backpressure from ROB
		expected_branch_notif_ready = 1'b1;
	    // LDU misprediction notification to ROB
	    // LDU misprediction notification backpressure from ROB
		expected_ldu_mispred_notif_ready = 1'b1;
	    // fence restart notification to ROB
	    // fence restart notification backpressure from ROB
		expected_fence_restart_notif_ready = 1'b1;
	    // LDU exception to ROB
	    // LDU exception backpressure from ROB
		expected_ldu_exception_ready = 1'b1;
	    // STAMOFU exception to ROB
	    // STAMOFU exception backpressure from ROB
		expected_stamofu_exception_ready = 1'b1;
	    // mdp update to ROB
	    // mdp update feedback from ROB
		expected_ssu_mdp_update_ready = 1'b1;
	    // mdpt update to fetch unit
		expected_fetch_unit_mdpt_update_valid = 1'b0;
		expected_fetch_unit_mdpt_update_start_full_PC = 32'h00000000;
		expected_fetch_unit_mdpt_update_ASID = 9'h000;
		expected_fetch_unit_mdpt_update_mdp_info = 8'h00;
	    // ROB commit
		expected_rob_commit_upper_index = 5'h00;
		expected_rob_commit_lower_index_valid_mask = 4'b0000;
	    // restart from ROB
		expected_rob_restart_valid = 1'b0;
		expected_rob_restart_PC = 32'h00000000;
		expected_rob_restart_ASID = 9'h000;
		expected_rob_restart_exec_mode = M_MODE;
		expected_rob_restart_virtual_mode = 1'b0;
		expected_rob_restart_MXR = 1'b0;
		expected_rob_restart_SUM = 1'b0;
		expected_rob_restart_trap_sfence = 1'b0;
		expected_rob_restart_trap_wfi = 1'b0;
		expected_rob_restart_trap_sret = 1'b0;
	    // ROB kill
		expected_rob_kill_valid = 1'b0;
		expected_rob_kill_abs_head_index = 7'h0;
		expected_rob_kill_rel_kill_younger_index = 7'h0;
	    // branch update from ROB
		expected_rob_branch_update_valid = 1'b0;
		expected_rob_branch_update_has_checkpoint = 1'b0;
		expected_rob_branch_update_checkpoint_index = 3'h0;
		expected_rob_branch_update_is_mispredict = 1'b0;
		expected_rob_branch_update_is_taken = 1'b0;
		expected_rob_branch_update_use_upct = 1'b0;
		expected_rob_branch_update_intermediate_pred_info = 8'h00;
		expected_rob_branch_update_pred_lru = 1'b0;
		expected_rob_branch_update_start_PC = 32'h00000000;
		expected_rob_branch_update_target_PC = 32'h00000000;
	    // ROB control of rename
		expected_rob_controlling_rename = 1'b0;
		expected_rob_checkpoint_map_table_restore_valid = 1'b0;
		expected_rob_checkpoint_map_table_restore_index = 3'h0;
		expected_rob_checkpoint_clear_valid = 1'b0;
		expected_rob_checkpoint_clear_index = 3'h0;
		expected_rob_map_table_write_valid_by_port = 4'b0000;
		expected_rob_map_table_write_AR_by_port = {5'h00, 5'h00, 5'h00, 5'h00};
		expected_rob_map_table_write_PR_by_port = {7'h00, 7'h00, 7'h00, 7'h00};
		// ROB physical register freeing
		expected_rob_PR_free_req_valid_by_bank = 4'b0000;
		expected_rob_PR_free_req_PR_by_bank = {7'h00, 7'h00, 7'h00, 7'h00};
		// ROB instret advertisement
		expected_rob_instret = 32'h0;
		// ROB instret write

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
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule