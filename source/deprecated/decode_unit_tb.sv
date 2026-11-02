/*
    Filename: decode_unit_tb.sv
    Author: zlagpacan
    Description: Testbench for decode_unit module. 
    Spec: LOROF/spec/design/decode_unit.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module decode_unit_tb #(
	parameter INIT_EXEC_MODE = M_MODE,
	parameter INIT_TRAP_SFENCE = 1'b0,
	parameter INIT_TRAP_WFI = 1'b0,
	parameter INIT_TRAP_SRET = 1'b0
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


    // input from istream
	logic tb_istream_valid_SDEQ;
	logic [3:0] tb_istream_valid_by_way_SDEQ;
	logic [3:0] tb_istream_uncompressed_by_way_SDEQ;
	logic [3:0][1:0][15:0] tb_istream_instr_2B_by_way_by_chunk_SDEQ;
	logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0] tb_istream_pred_info_by_way_by_chunk_SDEQ;
	logic [3:0][1:0] tb_istream_pred_lru_by_way_by_chunk_SDEQ;
	logic [3:0][1:0][31:0] tb_istream_pred_PC_by_way_by_chunk_SDEQ;
	logic [3:0][1:0] tb_istream_page_fault_by_way_by_chunk_SDEQ;
	logic [3:0][1:0] tb_istream_access_fault_by_way_by_chunk_SDEQ;
	logic [3:0][MDPT_INFO_WIDTH-1:0] tb_istream_mdp_info_by_way_SDEQ;
	logic [3:0][31:0] tb_istream_PC_by_way_SDEQ;
	logic [3:0][LH_LENGTH-1:0] tb_istream_LH_by_way_SDEQ;
	logic [3:0][GH_LENGTH-1:0] tb_istream_GH_by_way_SDEQ;
	logic [3:0][RAS_INDEX_WIDTH-1:0] tb_istream_ras_index_by_way_SDEQ;

    // feedback to istream
	logic DUT_istream_stall_SDEQ, expected_istream_stall_SDEQ;

    // op dispatch by way:

    // 4-way ROB entry
	logic DUT_dispatch_rob_enq_valid, expected_dispatch_rob_enq_valid;
	logic DUT_dispatch_rob_enq_killed, expected_dispatch_rob_enq_killed;
	logic tb_dispatch_rob_enq_ready;

    // general instr info
	logic [3:0] DUT_dispatch_valid_by_way, expected_dispatch_valid_by_way;
	logic [3:0] DUT_dispatch_uncompressed_by_way, expected_dispatch_uncompressed_by_way;
	logic [3:0][31:0] DUT_dispatch_PC_by_way, expected_dispatch_PC_by_way;
	logic [3:0][31:0] DUT_dispatch_pred_PC_by_way, expected_dispatch_pred_PC_by_way;
	logic [3:0] DUT_dispatch_is_rename_by_way, expected_dispatch_is_rename_by_way;
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0] DUT_dispatch_pred_info_by_way, expected_dispatch_pred_info_by_way;
	logic [3:0] DUT_dispatch_pred_lru_by_way, expected_dispatch_pred_lru_by_way;
	logic [3:0][MDPT_INFO_WIDTH-1:0] DUT_dispatch_mdp_info_by_way, expected_dispatch_mdp_info_by_way;
	logic [3:0][3:0] DUT_dispatch_op_by_way, expected_dispatch_op_by_way;
	logic [3:0][19:0] DUT_dispatch_imm20_by_way, expected_dispatch_imm20_by_way;

    // ordering
	logic [3:0] DUT_dispatch_mem_aq_by_way, expected_dispatch_mem_aq_by_way;
	logic [3:0] DUT_dispatch_io_aq_by_way, expected_dispatch_io_aq_by_way;
	logic [3:0] DUT_dispatch_mem_rl_by_way, expected_dispatch_mem_rl_by_way;
	logic [3:0] DUT_dispatch_io_rl_by_way, expected_dispatch_io_rl_by_way;

    // exception info
	logic DUT_dispatch_is_page_fault, expected_dispatch_is_page_fault;
	logic DUT_dispatch_is_access_fault, expected_dispatch_is_access_fault;
	logic DUT_dispatch_is_illegal_instr, expected_dispatch_is_illegal_instr;
	logic DUT_dispatch_exception_present, expected_dispatch_exception_present;
	logic [1:0] DUT_dispatch_exception_index, expected_dispatch_exception_index;
	logic [31:0] DUT_dispatch_illegal_instr32, expected_dispatch_illegal_instr32;

	// checkpoint info
	logic DUT_dispatch_has_checkpoint, expected_dispatch_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] DUT_dispatch_checkpoint_index, expected_dispatch_checkpoint_index;

    // instr IQ attempts
	logic [3:0] DUT_dispatch_attempt_alu_reg_mdu_dq_by_way, expected_dispatch_attempt_alu_reg_mdu_dq_by_way;
	logic [3:0] DUT_dispatch_attempt_alu_imm_dq_by_way, expected_dispatch_attempt_alu_imm_dq_by_way;
	logic [3:0] DUT_dispatch_attempt_bru_dq_by_way, expected_dispatch_attempt_bru_dq_by_way;
	logic [3:0] DUT_dispatch_attempt_ldu_dq_by_way, expected_dispatch_attempt_ldu_dq_by_way;
	logic [3:0] DUT_dispatch_attempt_stamofu_dq_by_way, expected_dispatch_attempt_stamofu_dq_by_way;
	logic [3:0] DUT_dispatch_attempt_sysu_dq_by_way, expected_dispatch_attempt_sysu_dq_by_way;

    // instr FU valids
	logic [3:0] DUT_dispatch_valid_alu_reg_by_way, expected_dispatch_valid_alu_reg_by_way;
	logic [3:0] DUT_dispatch_valid_mdu_by_way, expected_dispatch_valid_mdu_by_way;
	logic [3:0] DUT_dispatch_valid_alu_imm_by_way, expected_dispatch_valid_alu_imm_by_way;
	logic [3:0] DUT_dispatch_valid_bru_by_way, expected_dispatch_valid_bru_by_way;
	logic [3:0] DUT_dispatch_valid_ldu_by_way, expected_dispatch_valid_ldu_by_way;
	logic [3:0] DUT_dispatch_valid_store_by_way, expected_dispatch_valid_store_by_way;
	logic [3:0] DUT_dispatch_valid_amo_by_way, expected_dispatch_valid_amo_by_way;
	logic [3:0] DUT_dispatch_valid_fence_by_way, expected_dispatch_valid_fence_by_way;
	logic [3:0] DUT_dispatch_valid_sysu_by_way, expected_dispatch_valid_sysu_by_way;

    // operand A
	logic [3:0][LOG_PR_COUNT-1:0] DUT_dispatch_A_PR_by_way, expected_dispatch_A_PR_by_way;
	logic [3:0] DUT_dispatch_A_ready_by_way, expected_dispatch_A_ready_by_way;
	logic [3:0] DUT_dispatch_A_is_zero_by_way, expected_dispatch_A_is_zero_by_way;
	logic [3:0] DUT_dispatch_A_unneeded_or_is_zero_by_way, expected_dispatch_A_unneeded_or_is_zero_by_way;
	logic [3:0] DUT_dispatch_A_is_ret_ra_by_way, expected_dispatch_A_is_ret_ra_by_way;

    // operand B
	logic [3:0][LOG_PR_COUNT-1:0] DUT_dispatch_B_PR_by_way, expected_dispatch_B_PR_by_way;
	logic [3:0] DUT_dispatch_B_ready_by_way, expected_dispatch_B_ready_by_way;
	logic [3:0] DUT_dispatch_B_is_zero_by_way, expected_dispatch_B_is_zero_by_way;
	logic [3:0] DUT_dispatch_B_unneeded_or_is_zero_by_way, expected_dispatch_B_unneeded_or_is_zero_by_way;

    // dest operand
	logic [3:0][4:0] DUT_dispatch_dest_AR_by_way, expected_dispatch_dest_AR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] DUT_dispatch_dest_old_PR_by_way, expected_dispatch_dest_old_PR_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] DUT_dispatch_dest_new_PR_by_way, expected_dispatch_dest_new_PR_by_way;
	logic [3:0] DUT_dispatch_dest_is_link_ra_by_way, expected_dispatch_dest_is_link_ra_by_way;

    // instr IQ acks
	logic [3:0] tb_dispatch_ack_alu_reg_mdu_dq_by_way;
	logic [3:0] tb_dispatch_ack_alu_imm_dq_by_way;
	logic [3:0] tb_dispatch_ack_bru_dq_by_way;
	logic [3:0] tb_dispatch_ack_ldu_dq_by_way;
	logic [3:0] tb_dispatch_ack_stamofu_dq_by_way;
	logic [3:0] tb_dispatch_ack_sysu_dq_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // fetch + decode restart from ROB
	logic tb_rob_restart_valid;
	logic [1:0] tb_rob_restart_exec_mode;
	logic tb_rob_restart_trap_sfence;
	logic tb_rob_restart_trap_wfi;
	logic tb_rob_restart_trap_sret;

	// kill from ROB
	logic tb_rob_kill_valid;

    // branch update from ROB
	logic tb_rob_branch_update_valid;
	logic tb_rob_branch_update_has_checkpoint;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] tb_rob_branch_update_checkpoint_index;
	logic tb_rob_branch_update_is_mispredict;
	logic tb_rob_branch_update_is_taken;
	logic tb_rob_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_rob_branch_update_intermediate_pred_info;
	logic tb_rob_branch_update_pred_lru;
	logic [31:0] tb_rob_branch_update_start_PC;
	logic [31:0] tb_rob_branch_update_target_PC;

    // ROB control of rename
	logic tb_rob_controlling_rename;

	logic tb_rob_checkpoint_map_table_restore_valid;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] tb_rob_checkpoint_map_table_restore_index;

	logic tb_rob_checkpoint_clear_valid;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] tb_rob_checkpoint_clear_index;

	logic [3:0] tb_rob_map_table_write_valid_by_port;
	logic [3:0][LOG_AR_COUNT-1:0] tb_rob_map_table_write_AR_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] tb_rob_map_table_write_PR_by_port;

	// ROB physical register freeing
	logic [3:0] tb_rob_PR_free_req_valid_by_bank;
	logic [3:0][LOG_PR_COUNT-1:0] tb_rob_PR_free_req_PR_by_bank;
	logic [3:0] DUT_rob_PR_free_resp_ack_by_bank, expected_rob_PR_free_resp_ack_by_bank;

    // branch update to fetch unit
	logic DUT_decode_unit_branch_update_valid, expected_decode_unit_branch_update_valid;
	logic DUT_decode_unit_branch_update_has_checkpoint, expected_decode_unit_branch_update_has_checkpoint;
	logic DUT_decode_unit_branch_update_is_mispredict, expected_decode_unit_branch_update_is_mispredict;
	logic DUT_decode_unit_branch_update_is_taken, expected_decode_unit_branch_update_is_taken;
	logic DUT_decode_unit_branch_update_is_complex, expected_decode_unit_branch_update_is_complex;
	logic DUT_decode_unit_branch_update_use_upct, expected_decode_unit_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_decode_unit_branch_update_intermediate_pred_info, expected_decode_unit_branch_update_intermediate_pred_info;
	logic DUT_decode_unit_branch_update_pred_lru, expected_decode_unit_branch_update_pred_lru;
	logic [31:0] DUT_decode_unit_branch_update_start_PC, expected_decode_unit_branch_update_start_PC;
	logic [31:0] DUT_decode_unit_branch_update_target_PC, expected_decode_unit_branch_update_target_PC;
	logic [LH_LENGTH-1:0] DUT_decode_unit_branch_update_LH, expected_decode_unit_branch_update_LH;
	logic [GH_LENGTH-1:0] DUT_decode_unit_branch_update_GH, expected_decode_unit_branch_update_GH;
	logic [RAS_INDEX_WIDTH-1:0] DUT_decode_unit_branch_update_ras_index, expected_decode_unit_branch_update_ras_index;

    // decode unit control
	logic DUT_decode_unit_restart_valid, expected_decode_unit_restart_valid;
	logic [31:0] DUT_decode_unit_restart_PC, expected_decode_unit_restart_PC;

	logic DUT_decode_unit_trigger_wait_for_restart, expected_decode_unit_trigger_wait_for_restart;

	// hardware failure
	logic DUT_unrecoverable_fault, expected_unrecoverable_fault;

    // ----------------------------------------------------------------
    // DUT instantiation:

	decode_unit #(
		.INIT_EXEC_MODE(INIT_EXEC_MODE),
		.INIT_TRAP_SFENCE(INIT_TRAP_SFENCE),
		.INIT_TRAP_WFI(INIT_TRAP_WFI),
		.INIT_TRAP_SRET(INIT_TRAP_SRET)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // input from istream
		.istream_valid_SDEQ(tb_istream_valid_SDEQ),
		.istream_valid_by_way_SDEQ(tb_istream_valid_by_way_SDEQ),
		.istream_uncompressed_by_way_SDEQ(tb_istream_uncompressed_by_way_SDEQ),
		.istream_instr_2B_by_way_by_chunk_SDEQ(tb_istream_instr_2B_by_way_by_chunk_SDEQ),
		.istream_pred_info_by_way_by_chunk_SDEQ(tb_istream_pred_info_by_way_by_chunk_SDEQ),
		.istream_pred_lru_by_way_by_chunk_SDEQ(tb_istream_pred_lru_by_way_by_chunk_SDEQ),
		.istream_pred_PC_by_way_by_chunk_SDEQ(tb_istream_pred_PC_by_way_by_chunk_SDEQ),
		.istream_page_fault_by_way_by_chunk_SDEQ(tb_istream_page_fault_by_way_by_chunk_SDEQ),
		.istream_access_fault_by_way_by_chunk_SDEQ(tb_istream_access_fault_by_way_by_chunk_SDEQ),
		.istream_mdp_info_by_way_SDEQ(tb_istream_mdp_info_by_way_SDEQ),
		.istream_PC_by_way_SDEQ(tb_istream_PC_by_way_SDEQ),
		.istream_LH_by_way_SDEQ(tb_istream_LH_by_way_SDEQ),
		.istream_GH_by_way_SDEQ(tb_istream_GH_by_way_SDEQ),
		.istream_ras_index_by_way_SDEQ(tb_istream_ras_index_by_way_SDEQ),

	    // feedback to istream
		.istream_stall_SDEQ(DUT_istream_stall_SDEQ),

	    // op dispatch by way:

	    // 4-way ROB entry
		.dispatch_rob_enq_valid(DUT_dispatch_rob_enq_valid),
		.dispatch_rob_enq_killed(DUT_dispatch_rob_enq_killed),
		.dispatch_rob_enq_ready(tb_dispatch_rob_enq_ready),

	    // general instr info
		.dispatch_valid_by_way(DUT_dispatch_valid_by_way),
		.dispatch_uncompressed_by_way(DUT_dispatch_uncompressed_by_way),
		.dispatch_PC_by_way(DUT_dispatch_PC_by_way),
		.dispatch_pred_PC_by_way(DUT_dispatch_pred_PC_by_way),
		.dispatch_is_rename_by_way(DUT_dispatch_is_rename_by_way),
		.dispatch_pred_info_by_way(DUT_dispatch_pred_info_by_way),
		.dispatch_pred_lru_by_way(DUT_dispatch_pred_lru_by_way),
		.dispatch_mdp_info_by_way(DUT_dispatch_mdp_info_by_way),
		.dispatch_op_by_way(DUT_dispatch_op_by_way),
		.dispatch_imm20_by_way(DUT_dispatch_imm20_by_way),

	    // ordering
		.dispatch_mem_aq_by_way(DUT_dispatch_mem_aq_by_way),
		.dispatch_io_aq_by_way(DUT_dispatch_io_aq_by_way),
		.dispatch_mem_rl_by_way(DUT_dispatch_mem_rl_by_way),
		.dispatch_io_rl_by_way(DUT_dispatch_io_rl_by_way),

	    // exception info
		.dispatch_is_page_fault(DUT_dispatch_is_page_fault),
		.dispatch_is_access_fault(DUT_dispatch_is_access_fault),
		.dispatch_is_illegal_instr(DUT_dispatch_is_illegal_instr),
		.dispatch_exception_present(DUT_dispatch_exception_present),
		.dispatch_exception_index(DUT_dispatch_exception_index),
		.dispatch_illegal_instr32(DUT_dispatch_illegal_instr32),

		// checkpoint info
		.dispatch_has_checkpoint(DUT_dispatch_has_checkpoint),
		.dispatch_checkpoint_index(DUT_dispatch_checkpoint_index),

	    // instr IQ attempts
		.dispatch_attempt_alu_reg_mdu_dq_by_way(DUT_dispatch_attempt_alu_reg_mdu_dq_by_way),
		.dispatch_attempt_alu_imm_dq_by_way(DUT_dispatch_attempt_alu_imm_dq_by_way),
		.dispatch_attempt_bru_dq_by_way(DUT_dispatch_attempt_bru_dq_by_way),
		.dispatch_attempt_ldu_dq_by_way(DUT_dispatch_attempt_ldu_dq_by_way),
		.dispatch_attempt_stamofu_dq_by_way(DUT_dispatch_attempt_stamofu_dq_by_way),
		.dispatch_attempt_sysu_dq_by_way(DUT_dispatch_attempt_sysu_dq_by_way),

	    // instr FU valids
		.dispatch_valid_alu_reg_by_way(DUT_dispatch_valid_alu_reg_by_way),
		.dispatch_valid_mdu_by_way(DUT_dispatch_valid_mdu_by_way),
		.dispatch_valid_alu_imm_by_way(DUT_dispatch_valid_alu_imm_by_way),
		.dispatch_valid_bru_by_way(DUT_dispatch_valid_bru_by_way),
		.dispatch_valid_ldu_by_way(DUT_dispatch_valid_ldu_by_way),
		.dispatch_valid_store_by_way(DUT_dispatch_valid_store_by_way),
		.dispatch_valid_amo_by_way(DUT_dispatch_valid_amo_by_way),
		.dispatch_valid_fence_by_way(DUT_dispatch_valid_fence_by_way),
		.dispatch_valid_sysu_by_way(DUT_dispatch_valid_sysu_by_way),

	    // operand A
		.dispatch_A_PR_by_way(DUT_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(DUT_dispatch_A_ready_by_way),
		.dispatch_A_is_zero_by_way(DUT_dispatch_A_is_zero_by_way),
		.dispatch_A_unneeded_or_is_zero_by_way(DUT_dispatch_A_unneeded_or_is_zero_by_way),
		.dispatch_A_is_ret_ra_by_way(DUT_dispatch_A_is_ret_ra_by_way),

	    // operand B
		.dispatch_B_PR_by_way(DUT_dispatch_B_PR_by_way),
		.dispatch_B_ready_by_way(DUT_dispatch_B_ready_by_way),
		.dispatch_B_is_zero_by_way(DUT_dispatch_B_is_zero_by_way),
		.dispatch_B_unneeded_or_is_zero_by_way(DUT_dispatch_B_unneeded_or_is_zero_by_way),

	    // dest operand
		.dispatch_dest_AR_by_way(DUT_dispatch_dest_AR_by_way),
		.dispatch_dest_old_PR_by_way(DUT_dispatch_dest_old_PR_by_way),
		.dispatch_dest_new_PR_by_way(DUT_dispatch_dest_new_PR_by_way),
		.dispatch_dest_is_link_ra_by_way(DUT_dispatch_dest_is_link_ra_by_way),

	    // instr IQ acks
		.dispatch_ack_alu_reg_mdu_dq_by_way(tb_dispatch_ack_alu_reg_mdu_dq_by_way),
		.dispatch_ack_alu_imm_dq_by_way(tb_dispatch_ack_alu_imm_dq_by_way),
		.dispatch_ack_bru_dq_by_way(tb_dispatch_ack_bru_dq_by_way),
		.dispatch_ack_ldu_dq_by_way(tb_dispatch_ack_ldu_dq_by_way),
		.dispatch_ack_stamofu_dq_by_way(tb_dispatch_ack_stamofu_dq_by_way),
		.dispatch_ack_sysu_dq_by_way(tb_dispatch_ack_sysu_dq_by_way),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // fetch + decode restart from ROB
		.rob_restart_valid(tb_rob_restart_valid),
		.rob_restart_exec_mode(tb_rob_restart_exec_mode),
		.rob_restart_trap_sfence(tb_rob_restart_trap_sfence),
		.rob_restart_trap_wfi(tb_rob_restart_trap_wfi),
		.rob_restart_trap_sret(tb_rob_restart_trap_sret),

		// kill from ROB
		.rob_kill_valid(tb_rob_kill_valid),

	    // branch update from ROB
		.rob_branch_update_valid(tb_rob_branch_update_valid),
		.rob_branch_update_has_checkpoint(tb_rob_branch_update_has_checkpoint),
		.rob_branch_update_checkpoint_index(tb_rob_branch_update_checkpoint_index),
		.rob_branch_update_is_mispredict(tb_rob_branch_update_is_mispredict),
		.rob_branch_update_is_taken(tb_rob_branch_update_is_taken),
		.rob_branch_update_use_upct(tb_rob_branch_update_use_upct),
		.rob_branch_update_intermediate_pred_info(tb_rob_branch_update_intermediate_pred_info),
		.rob_branch_update_pred_lru(tb_rob_branch_update_pred_lru),
		.rob_branch_update_start_PC(tb_rob_branch_update_start_PC),
		.rob_branch_update_target_PC(tb_rob_branch_update_target_PC),

	    // ROB control of rename
		.rob_controlling_rename(tb_rob_controlling_rename),

		.rob_checkpoint_map_table_restore_valid(tb_rob_checkpoint_map_table_restore_valid),
		.rob_checkpoint_map_table_restore_index(tb_rob_checkpoint_map_table_restore_index),

		.rob_checkpoint_clear_valid(tb_rob_checkpoint_clear_valid),
		.rob_checkpoint_clear_index(tb_rob_checkpoint_clear_index),

		.rob_map_table_write_valid_by_port(tb_rob_map_table_write_valid_by_port),
		.rob_map_table_write_AR_by_port(tb_rob_map_table_write_AR_by_port),
		.rob_map_table_write_PR_by_port(tb_rob_map_table_write_PR_by_port),

		// ROB physical register freeing
		.rob_PR_free_req_valid_by_bank(tb_rob_PR_free_req_valid_by_bank),
		.rob_PR_free_req_PR_by_bank(tb_rob_PR_free_req_PR_by_bank),
		.rob_PR_free_resp_ack_by_bank(DUT_rob_PR_free_resp_ack_by_bank),

	    // branch update to fetch unit
		.decode_unit_branch_update_valid(DUT_decode_unit_branch_update_valid),
		.decode_unit_branch_update_has_checkpoint(DUT_decode_unit_branch_update_has_checkpoint),
		.decode_unit_branch_update_is_mispredict(DUT_decode_unit_branch_update_is_mispredict),
		.decode_unit_branch_update_is_taken(DUT_decode_unit_branch_update_is_taken),
		.decode_unit_branch_update_is_complex(DUT_decode_unit_branch_update_is_complex),
		.decode_unit_branch_update_use_upct(DUT_decode_unit_branch_update_use_upct),
		.decode_unit_branch_update_intermediate_pred_info(DUT_decode_unit_branch_update_intermediate_pred_info),
		.decode_unit_branch_update_pred_lru(DUT_decode_unit_branch_update_pred_lru),
		.decode_unit_branch_update_start_PC(DUT_decode_unit_branch_update_start_PC),
		.decode_unit_branch_update_target_PC(DUT_decode_unit_branch_update_target_PC),
		.decode_unit_branch_update_LH(DUT_decode_unit_branch_update_LH),
		.decode_unit_branch_update_GH(DUT_decode_unit_branch_update_GH),
		.decode_unit_branch_update_ras_index(DUT_decode_unit_branch_update_ras_index),

	    // decode unit control
		.decode_unit_restart_valid(DUT_decode_unit_restart_valid),
		.decode_unit_restart_PC(DUT_decode_unit_restart_PC),

		.decode_unit_trigger_wait_for_restart(DUT_decode_unit_trigger_wait_for_restart),

		// hardware failure
		.unrecoverable_fault(DUT_unrecoverable_fault)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_istream_stall_SDEQ !== DUT_istream_stall_SDEQ) begin
			$display("TB ERROR: expected_istream_stall_SDEQ (%h) != DUT_istream_stall_SDEQ (%h)",
				expected_istream_stall_SDEQ, DUT_istream_stall_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_rob_enq_valid !== DUT_dispatch_rob_enq_valid) begin
			$display("TB ERROR: expected_dispatch_rob_enq_valid (%h) != DUT_dispatch_rob_enq_valid (%h)",
				expected_dispatch_rob_enq_valid, DUT_dispatch_rob_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_rob_enq_killed !== DUT_dispatch_rob_enq_killed) begin
			$display("TB ERROR: expected_dispatch_rob_enq_killed (%h) != DUT_dispatch_rob_enq_killed (%h)",
				expected_dispatch_rob_enq_killed, DUT_dispatch_rob_enq_killed);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_by_way !== DUT_dispatch_valid_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_by_way (%h) != DUT_dispatch_valid_by_way (%h)",
				expected_dispatch_valid_by_way, DUT_dispatch_valid_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_uncompressed_by_way !== DUT_dispatch_uncompressed_by_way) begin
			$display("TB ERROR: expected_dispatch_uncompressed_by_way (%h) != DUT_dispatch_uncompressed_by_way (%h)",
				expected_dispatch_uncompressed_by_way, DUT_dispatch_uncompressed_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_PC_by_way !== DUT_dispatch_PC_by_way) begin
			$display("TB ERROR: expected_dispatch_PC_by_way (%h) != DUT_dispatch_PC_by_way (%h)",
				expected_dispatch_PC_by_way, DUT_dispatch_PC_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_pred_PC_by_way !== DUT_dispatch_pred_PC_by_way) begin
			$display("TB ERROR: expected_dispatch_pred_PC_by_way (%h) != DUT_dispatch_pred_PC_by_way (%h)",
				expected_dispatch_pred_PC_by_way, DUT_dispatch_pred_PC_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_is_rename_by_way !== DUT_dispatch_is_rename_by_way) begin
			$display("TB ERROR: expected_dispatch_is_rename_by_way (%h) != DUT_dispatch_is_rename_by_way (%h)",
				expected_dispatch_is_rename_by_way, DUT_dispatch_is_rename_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_pred_info_by_way !== DUT_dispatch_pred_info_by_way) begin
			$display("TB ERROR: expected_dispatch_pred_info_by_way (%h) != DUT_dispatch_pred_info_by_way (%h)",
				expected_dispatch_pred_info_by_way, DUT_dispatch_pred_info_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_pred_lru_by_way !== DUT_dispatch_pred_lru_by_way) begin
			$display("TB ERROR: expected_dispatch_pred_lru_by_way (%h) != DUT_dispatch_pred_lru_by_way (%h)",
				expected_dispatch_pred_lru_by_way, DUT_dispatch_pred_lru_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_mdp_info_by_way !== DUT_dispatch_mdp_info_by_way) begin
			$display("TB ERROR: expected_dispatch_mdp_info_by_way (%h) != DUT_dispatch_mdp_info_by_way (%h)",
				expected_dispatch_mdp_info_by_way, DUT_dispatch_mdp_info_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_op_by_way !== DUT_dispatch_op_by_way) begin
			$display("TB ERROR: expected_dispatch_op_by_way (%h) != DUT_dispatch_op_by_way (%h)",
				expected_dispatch_op_by_way, DUT_dispatch_op_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_imm20_by_way !== DUT_dispatch_imm20_by_way) begin
			$display("TB ERROR: expected_dispatch_imm20_by_way (%h) != DUT_dispatch_imm20_by_way (%h)",
				expected_dispatch_imm20_by_way, DUT_dispatch_imm20_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_mem_aq_by_way !== DUT_dispatch_mem_aq_by_way) begin
			$display("TB ERROR: expected_dispatch_mem_aq_by_way (%h) != DUT_dispatch_mem_aq_by_way (%h)",
				expected_dispatch_mem_aq_by_way, DUT_dispatch_mem_aq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_io_aq_by_way !== DUT_dispatch_io_aq_by_way) begin
			$display("TB ERROR: expected_dispatch_io_aq_by_way (%h) != DUT_dispatch_io_aq_by_way (%h)",
				expected_dispatch_io_aq_by_way, DUT_dispatch_io_aq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_mem_rl_by_way !== DUT_dispatch_mem_rl_by_way) begin
			$display("TB ERROR: expected_dispatch_mem_rl_by_way (%h) != DUT_dispatch_mem_rl_by_way (%h)",
				expected_dispatch_mem_rl_by_way, DUT_dispatch_mem_rl_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_io_rl_by_way !== DUT_dispatch_io_rl_by_way) begin
			$display("TB ERROR: expected_dispatch_io_rl_by_way (%h) != DUT_dispatch_io_rl_by_way (%h)",
				expected_dispatch_io_rl_by_way, DUT_dispatch_io_rl_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_is_page_fault !== DUT_dispatch_is_page_fault) begin
			$display("TB ERROR: expected_dispatch_is_page_fault (%h) != DUT_dispatch_is_page_fault (%h)",
				expected_dispatch_is_page_fault, DUT_dispatch_is_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_is_access_fault !== DUT_dispatch_is_access_fault) begin
			$display("TB ERROR: expected_dispatch_is_access_fault (%h) != DUT_dispatch_is_access_fault (%h)",
				expected_dispatch_is_access_fault, DUT_dispatch_is_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_is_illegal_instr !== DUT_dispatch_is_illegal_instr) begin
			$display("TB ERROR: expected_dispatch_is_illegal_instr (%h) != DUT_dispatch_is_illegal_instr (%h)",
				expected_dispatch_is_illegal_instr, DUT_dispatch_is_illegal_instr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_exception_present !== DUT_dispatch_exception_present) begin
			$display("TB ERROR: expected_dispatch_exception_present (%h) != DUT_dispatch_exception_present (%h)",
				expected_dispatch_exception_present, DUT_dispatch_exception_present);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_exception_index !== DUT_dispatch_exception_index) begin
			$display("TB ERROR: expected_dispatch_exception_index (%h) != DUT_dispatch_exception_index (%h)",
				expected_dispatch_exception_index, DUT_dispatch_exception_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_illegal_instr32 !== DUT_dispatch_illegal_instr32) begin
			$display("TB ERROR: expected_dispatch_illegal_instr32 (%h) != DUT_dispatch_illegal_instr32 (%h)",
				expected_dispatch_illegal_instr32, DUT_dispatch_illegal_instr32);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_has_checkpoint !== DUT_dispatch_has_checkpoint) begin
			$display("TB ERROR: expected_dispatch_has_checkpoint (%h) != DUT_dispatch_has_checkpoint (%h)",
				expected_dispatch_has_checkpoint, DUT_dispatch_has_checkpoint);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_checkpoint_index !== DUT_dispatch_checkpoint_index) begin
			$display("TB ERROR: expected_dispatch_checkpoint_index (%h) != DUT_dispatch_checkpoint_index (%h)",
				expected_dispatch_checkpoint_index, DUT_dispatch_checkpoint_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_attempt_alu_reg_mdu_dq_by_way !== DUT_dispatch_attempt_alu_reg_mdu_dq_by_way) begin
			$display("TB ERROR: expected_dispatch_attempt_alu_reg_mdu_dq_by_way (%h) != DUT_dispatch_attempt_alu_reg_mdu_dq_by_way (%h)",
				expected_dispatch_attempt_alu_reg_mdu_dq_by_way, DUT_dispatch_attempt_alu_reg_mdu_dq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_attempt_alu_imm_dq_by_way !== DUT_dispatch_attempt_alu_imm_dq_by_way) begin
			$display("TB ERROR: expected_dispatch_attempt_alu_imm_dq_by_way (%h) != DUT_dispatch_attempt_alu_imm_dq_by_way (%h)",
				expected_dispatch_attempt_alu_imm_dq_by_way, DUT_dispatch_attempt_alu_imm_dq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_attempt_bru_dq_by_way !== DUT_dispatch_attempt_bru_dq_by_way) begin
			$display("TB ERROR: expected_dispatch_attempt_bru_dq_by_way (%h) != DUT_dispatch_attempt_bru_dq_by_way (%h)",
				expected_dispatch_attempt_bru_dq_by_way, DUT_dispatch_attempt_bru_dq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_attempt_ldu_dq_by_way !== DUT_dispatch_attempt_ldu_dq_by_way) begin
			$display("TB ERROR: expected_dispatch_attempt_ldu_dq_by_way (%h) != DUT_dispatch_attempt_ldu_dq_by_way (%h)",
				expected_dispatch_attempt_ldu_dq_by_way, DUT_dispatch_attempt_ldu_dq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_attempt_stamofu_dq_by_way !== DUT_dispatch_attempt_stamofu_dq_by_way) begin
			$display("TB ERROR: expected_dispatch_attempt_stamofu_dq_by_way (%h) != DUT_dispatch_attempt_stamofu_dq_by_way (%h)",
				expected_dispatch_attempt_stamofu_dq_by_way, DUT_dispatch_attempt_stamofu_dq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_attempt_sysu_dq_by_way !== DUT_dispatch_attempt_sysu_dq_by_way) begin
			$display("TB ERROR: expected_dispatch_attempt_sysu_dq_by_way (%h) != DUT_dispatch_attempt_sysu_dq_by_way (%h)",
				expected_dispatch_attempt_sysu_dq_by_way, DUT_dispatch_attempt_sysu_dq_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_alu_reg_by_way !== DUT_dispatch_valid_alu_reg_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_alu_reg_by_way (%h) != DUT_dispatch_valid_alu_reg_by_way (%h)",
				expected_dispatch_valid_alu_reg_by_way, DUT_dispatch_valid_alu_reg_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_mdu_by_way !== DUT_dispatch_valid_mdu_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_mdu_by_way (%h) != DUT_dispatch_valid_mdu_by_way (%h)",
				expected_dispatch_valid_mdu_by_way, DUT_dispatch_valid_mdu_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_alu_imm_by_way !== DUT_dispatch_valid_alu_imm_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_alu_imm_by_way (%h) != DUT_dispatch_valid_alu_imm_by_way (%h)",
				expected_dispatch_valid_alu_imm_by_way, DUT_dispatch_valid_alu_imm_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_bru_by_way !== DUT_dispatch_valid_bru_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_bru_by_way (%h) != DUT_dispatch_valid_bru_by_way (%h)",
				expected_dispatch_valid_bru_by_way, DUT_dispatch_valid_bru_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_ldu_by_way !== DUT_dispatch_valid_ldu_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_ldu_by_way (%h) != DUT_dispatch_valid_ldu_by_way (%h)",
				expected_dispatch_valid_ldu_by_way, DUT_dispatch_valid_ldu_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_store_by_way !== DUT_dispatch_valid_store_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_store_by_way (%h) != DUT_dispatch_valid_store_by_way (%h)",
				expected_dispatch_valid_store_by_way, DUT_dispatch_valid_store_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_amo_by_way !== DUT_dispatch_valid_amo_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_amo_by_way (%h) != DUT_dispatch_valid_amo_by_way (%h)",
				expected_dispatch_valid_amo_by_way, DUT_dispatch_valid_amo_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_fence_by_way !== DUT_dispatch_valid_fence_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_fence_by_way (%h) != DUT_dispatch_valid_fence_by_way (%h)",
				expected_dispatch_valid_fence_by_way, DUT_dispatch_valid_fence_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_valid_sysu_by_way !== DUT_dispatch_valid_sysu_by_way) begin
			$display("TB ERROR: expected_dispatch_valid_sysu_by_way (%h) != DUT_dispatch_valid_sysu_by_way (%h)",
				expected_dispatch_valid_sysu_by_way, DUT_dispatch_valid_sysu_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_A_PR_by_way !== DUT_dispatch_A_PR_by_way) begin
			$display("TB ERROR: expected_dispatch_A_PR_by_way (%h) != DUT_dispatch_A_PR_by_way (%h)",
				expected_dispatch_A_PR_by_way, DUT_dispatch_A_PR_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_A_ready_by_way !== DUT_dispatch_A_ready_by_way) begin
			$display("TB ERROR: expected_dispatch_A_ready_by_way (%h) != DUT_dispatch_A_ready_by_way (%h)",
				expected_dispatch_A_ready_by_way, DUT_dispatch_A_ready_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_A_is_zero_by_way !== DUT_dispatch_A_is_zero_by_way) begin
			$display("TB ERROR: expected_dispatch_A_is_zero_by_way (%h) != DUT_dispatch_A_is_zero_by_way (%h)",
				expected_dispatch_A_is_zero_by_way, DUT_dispatch_A_is_zero_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_A_unneeded_or_is_zero_by_way !== DUT_dispatch_A_unneeded_or_is_zero_by_way) begin
			$display("TB ERROR: expected_dispatch_A_unneeded_or_is_zero_by_way (%h) != DUT_dispatch_A_unneeded_or_is_zero_by_way (%h)",
				expected_dispatch_A_unneeded_or_is_zero_by_way, DUT_dispatch_A_unneeded_or_is_zero_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_A_is_ret_ra_by_way !== DUT_dispatch_A_is_ret_ra_by_way) begin
			$display("TB ERROR: expected_dispatch_A_is_ret_ra_by_way (%h) != DUT_dispatch_A_is_ret_ra_by_way (%h)",
				expected_dispatch_A_is_ret_ra_by_way, DUT_dispatch_A_is_ret_ra_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_B_PR_by_way !== DUT_dispatch_B_PR_by_way) begin
			$display("TB ERROR: expected_dispatch_B_PR_by_way (%h) != DUT_dispatch_B_PR_by_way (%h)",
				expected_dispatch_B_PR_by_way, DUT_dispatch_B_PR_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_B_ready_by_way !== DUT_dispatch_B_ready_by_way) begin
			$display("TB ERROR: expected_dispatch_B_ready_by_way (%h) != DUT_dispatch_B_ready_by_way (%h)",
				expected_dispatch_B_ready_by_way, DUT_dispatch_B_ready_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_B_is_zero_by_way !== DUT_dispatch_B_is_zero_by_way) begin
			$display("TB ERROR: expected_dispatch_B_is_zero_by_way (%h) != DUT_dispatch_B_is_zero_by_way (%h)",
				expected_dispatch_B_is_zero_by_way, DUT_dispatch_B_is_zero_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_B_unneeded_or_is_zero_by_way !== DUT_dispatch_B_unneeded_or_is_zero_by_way) begin
			$display("TB ERROR: expected_dispatch_B_unneeded_or_is_zero_by_way (%h) != DUT_dispatch_B_unneeded_or_is_zero_by_way (%h)",
				expected_dispatch_B_unneeded_or_is_zero_by_way, DUT_dispatch_B_unneeded_or_is_zero_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_dest_AR_by_way !== DUT_dispatch_dest_AR_by_way) begin
			$display("TB ERROR: expected_dispatch_dest_AR_by_way (%h) != DUT_dispatch_dest_AR_by_way (%h)",
				expected_dispatch_dest_AR_by_way, DUT_dispatch_dest_AR_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_dest_old_PR_by_way !== DUT_dispatch_dest_old_PR_by_way) begin
			$display("TB ERROR: expected_dispatch_dest_old_PR_by_way (%h) != DUT_dispatch_dest_old_PR_by_way (%h)",
				expected_dispatch_dest_old_PR_by_way, DUT_dispatch_dest_old_PR_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_dest_new_PR_by_way !== DUT_dispatch_dest_new_PR_by_way) begin
			$display("TB ERROR: expected_dispatch_dest_new_PR_by_way (%h) != DUT_dispatch_dest_new_PR_by_way (%h)",
				expected_dispatch_dest_new_PR_by_way, DUT_dispatch_dest_new_PR_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dispatch_dest_is_link_ra_by_way !== DUT_dispatch_dest_is_link_ra_by_way) begin
			$display("TB ERROR: expected_dispatch_dest_is_link_ra_by_way (%h) != DUT_dispatch_dest_is_link_ra_by_way (%h)",
				expected_dispatch_dest_is_link_ra_by_way, DUT_dispatch_dest_is_link_ra_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_PR_free_resp_ack_by_bank !== DUT_rob_PR_free_resp_ack_by_bank) begin
			$display("TB ERROR: expected_rob_PR_free_resp_ack_by_bank (%h) != DUT_rob_PR_free_resp_ack_by_bank (%h)",
				expected_rob_PR_free_resp_ack_by_bank, DUT_rob_PR_free_resp_ack_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_valid !== DUT_decode_unit_branch_update_valid) begin
			$display("TB ERROR: expected_decode_unit_branch_update_valid (%h) != DUT_decode_unit_branch_update_valid (%h)",
				expected_decode_unit_branch_update_valid, DUT_decode_unit_branch_update_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_has_checkpoint !== DUT_decode_unit_branch_update_has_checkpoint) begin
			$display("TB ERROR: expected_decode_unit_branch_update_has_checkpoint (%h) != DUT_decode_unit_branch_update_has_checkpoint (%h)",
				expected_decode_unit_branch_update_has_checkpoint, DUT_decode_unit_branch_update_has_checkpoint);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_is_mispredict !== DUT_decode_unit_branch_update_is_mispredict) begin
			$display("TB ERROR: expected_decode_unit_branch_update_is_mispredict (%h) != DUT_decode_unit_branch_update_is_mispredict (%h)",
				expected_decode_unit_branch_update_is_mispredict, DUT_decode_unit_branch_update_is_mispredict);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_is_taken !== DUT_decode_unit_branch_update_is_taken) begin
			$display("TB ERROR: expected_decode_unit_branch_update_is_taken (%h) != DUT_decode_unit_branch_update_is_taken (%h)",
				expected_decode_unit_branch_update_is_taken, DUT_decode_unit_branch_update_is_taken);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_is_complex !== DUT_decode_unit_branch_update_is_complex) begin
			$display("TB ERROR: expected_decode_unit_branch_update_is_complex (%h) != DUT_decode_unit_branch_update_is_complex (%h)",
				expected_decode_unit_branch_update_is_complex, DUT_decode_unit_branch_update_is_complex);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_use_upct !== DUT_decode_unit_branch_update_use_upct) begin
			$display("TB ERROR: expected_decode_unit_branch_update_use_upct (%h) != DUT_decode_unit_branch_update_use_upct (%h)",
				expected_decode_unit_branch_update_use_upct, DUT_decode_unit_branch_update_use_upct);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_intermediate_pred_info !== DUT_decode_unit_branch_update_intermediate_pred_info) begin
			$display("TB ERROR: expected_decode_unit_branch_update_intermediate_pred_info (%h) != DUT_decode_unit_branch_update_intermediate_pred_info (%h)",
				expected_decode_unit_branch_update_intermediate_pred_info, DUT_decode_unit_branch_update_intermediate_pred_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_pred_lru !== DUT_decode_unit_branch_update_pred_lru) begin
			$display("TB ERROR: expected_decode_unit_branch_update_pred_lru (%h) != DUT_decode_unit_branch_update_pred_lru (%h)",
				expected_decode_unit_branch_update_pred_lru, DUT_decode_unit_branch_update_pred_lru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_start_PC !== DUT_decode_unit_branch_update_start_PC) begin
			$display("TB ERROR: expected_decode_unit_branch_update_start_PC (%h) != DUT_decode_unit_branch_update_start_PC (%h)",
				expected_decode_unit_branch_update_start_PC, DUT_decode_unit_branch_update_start_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_target_PC !== DUT_decode_unit_branch_update_target_PC) begin
			$display("TB ERROR: expected_decode_unit_branch_update_target_PC (%h) != DUT_decode_unit_branch_update_target_PC (%h)",
				expected_decode_unit_branch_update_target_PC, DUT_decode_unit_branch_update_target_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_LH !== DUT_decode_unit_branch_update_LH) begin
			$display("TB ERROR: expected_decode_unit_branch_update_LH (%h) != DUT_decode_unit_branch_update_LH (%h)",
				expected_decode_unit_branch_update_LH, DUT_decode_unit_branch_update_LH);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_GH !== DUT_decode_unit_branch_update_GH) begin
			$display("TB ERROR: expected_decode_unit_branch_update_GH (%h) != DUT_decode_unit_branch_update_GH (%h)",
				expected_decode_unit_branch_update_GH, DUT_decode_unit_branch_update_GH);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_branch_update_ras_index !== DUT_decode_unit_branch_update_ras_index) begin
			$display("TB ERROR: expected_decode_unit_branch_update_ras_index (%h) != DUT_decode_unit_branch_update_ras_index (%h)",
				expected_decode_unit_branch_update_ras_index, DUT_decode_unit_branch_update_ras_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_restart_valid !== DUT_decode_unit_restart_valid) begin
			$display("TB ERROR: expected_decode_unit_restart_valid (%h) != DUT_decode_unit_restart_valid (%h)",
				expected_decode_unit_restart_valid, DUT_decode_unit_restart_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_restart_PC !== DUT_decode_unit_restart_PC) begin
			$display("TB ERROR: expected_decode_unit_restart_PC (%h) != DUT_decode_unit_restart_PC (%h)",
				expected_decode_unit_restart_PC, DUT_decode_unit_restart_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_decode_unit_trigger_wait_for_restart !== DUT_decode_unit_trigger_wait_for_restart) begin
			$display("TB ERROR: expected_decode_unit_trigger_wait_for_restart (%h) != DUT_decode_unit_trigger_wait_for_restart (%h)",
				expected_decode_unit_trigger_wait_for_restart, DUT_decode_unit_trigger_wait_for_restart);
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
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0000;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0000;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_PC_by_way_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_LH_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_GH_by_way_SDEQ = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_istream_ras_index_by_way_SDEQ = {3'h0, 3'h0, 3'h0, 3'h0};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0000;
		expected_dispatch_uncompressed_by_way = 4'b0000;
		expected_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_pred_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = {20'h0, 20'h0, 20'h0, 20'h0};
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b0000;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b0000;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h0, 5'h0, 5'h0, 5'h0};
		expected_dispatch_dest_old_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		expected_dispatch_dest_new_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h0;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h0;
		expected_decode_unit_branch_update_GH = 12'h0;
		expected_decode_unit_branch_update_ras_index = 3'h0;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h0;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0000;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0000;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_PC_by_way_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_LH_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_GH_by_way_SDEQ = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_istream_ras_index_by_way_SDEQ = {3'h0, 3'h0, 3'h0, 3'h0};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0000;
		expected_dispatch_uncompressed_by_way = 4'b0000;
		expected_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_pred_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = {20'h0, 20'h0, 20'h0, 20'h0};
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b0000;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b0000;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h0, 5'h0, 5'h0, 5'h0};
		expected_dispatch_dest_old_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		expected_dispatch_dest_new_PR_by_way = {7'h23, 7'h22, 7'h21, 7'h20};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h0;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h0;
		expected_decode_unit_branch_update_GH = 12'h0;
		expected_decode_unit_branch_update_ras_index = 3'h0;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h0;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // idle sequence:
        test_case = "idle sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "idle 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0000;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0000;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_PC_by_way_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_LH_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_GH_by_way_SDEQ = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_istream_ras_index_by_way_SDEQ = {3'h0, 3'h0, 3'h0, 3'h0};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0000;
		expected_dispatch_uncompressed_by_way = 4'b0000;
		expected_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_pred_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = {20'h0, 20'h0, 20'h0, 20'h0};
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2, 7'h2, 7'h2, 7'h2};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h8, 5'h8, 5'h8, 5'h8};
		expected_dispatch_dest_old_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_dest_new_PR_by_way = {7'h23, 7'h22, 7'h21, 7'h20};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h0;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h0;
		expected_decode_unit_branch_update_GH = 12'h0;
		expected_decode_unit_branch_update_ras_index = 3'h0;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h0;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "idle 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0000;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0000;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_PC_by_way_SDEQ = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_istream_LH_by_way_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_GH_by_way_SDEQ = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_istream_ras_index_by_way_SDEQ = {3'h0, 3'h0, 3'h0, 3'h0};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0000;
		expected_dispatch_uncompressed_by_way = 4'b0000;
		expected_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_pred_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = {20'h0, 20'h0, 20'h0, 20'h0};
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2, 7'h2, 7'h2, 7'h2};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h8, 5'h8, 5'h8, 5'h8};
		expected_dispatch_dest_old_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_dest_new_PR_by_way = {7'h23, 7'h22, 7'h21, 7'h20};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h0;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h0;
		expected_decode_unit_branch_update_GH = 12'h0;
		expected_decode_unit_branch_update_ras_index = 3'h0;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h0;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // simple sequence:
        test_case = "simple sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 0\n",
			"\t\tSDEQ:\n",
			"\t\t\t", "8000000C: ", "sb x30, 0xcba(x8)", "\n",
			"\t\t\t", "80000008: ", "lb x31, 0xfed(x1)", "\n",
			"\t\t\t", "80000004: ", "jal x1, 0x23456", "\n",
			"\t\t\t", "80000000: ", "lui x5, 0xa5a5a", "\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'hcbe40d23,
			32'hfed08f83,
			32'h456230ef,
			32'ha5a5a2b7
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h80000010, 32'h8000000E,
			32'h8000000C, 32'h8000000A,
			32'h80000008, 32'h80000006,
			32'h80000004, 32'h80000002
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h10,
			8'h0C,
			8'h08,
			8'h04
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h8000000C,
			32'h80000008,
			32'h80000004,
			32'h80000000
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h0E,
			8'h0A,
			8'h06,
			8'h02
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h010,
			12'h00C,
			12'h008,
			12'h004
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'hE,
			3'hA,
			3'h6,
			3'h2
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0000;
		expected_dispatch_uncompressed_by_way = 4'b0000;
		expected_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_pred_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = {20'h0, 20'h0, 20'h0, 20'h0};
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2, 7'h2, 7'h2, 7'h2};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h8, 5'h8, 5'h8, 5'h8};
		expected_dispatch_dest_old_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_dest_new_PR_by_way = {7'h23, 7'h22, 7'h21, 7'h20};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h0;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h0;
		expected_decode_unit_branch_update_GH = 12'h0;
		expected_decode_unit_branch_update_ras_index = 3'h0;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h0;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 1\n",
			"\t\tSDEQ:\n",
			"\t\t\t", "3456789E: ", "sh x0, 0x21(x14)", "\n",
			"\t\t\t", "3456789A: ", "lh x22, 0x45(x21)", "\n",
			"\t\t\t", "80000014: ", "jalr x0, 0x508(x22) + pred", "\n",
			"\t\t\t", "80000010: ", "auipc x14, 0x69696", "\n",
			"\t\tDEC:\n",
			"\t\t\t", "8000000C: ", "sb x30, 0xcba(x8)", "\n",
			"\t\t\t", "80000008: ", "lb x31, 0xfed(x1)", "\n",
			"\t\t\t", "80000004: ", "jal x1, 0x23456", "\n",
			"\t\t\t", "80000000: ", "lui x5, 0xa5a5a", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h020710a3,
			32'h045a9b03,
			32'h508b0067,
			32'h69696717
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b01000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00001000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678A2, 32'h345678A0,
			32'h3456789E, 32'h3456789C,
			32'h3456789A, 32'h80000016,
			32'h80000014, 32'h80000012
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hA2,
			8'h9E,
			8'h9A,
			8'h14
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h3456789E,
			32'h3456789A,
			32'h80000014,
			32'h80000010
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hA0,
			8'h9C,
			8'h16,
			8'h12
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8A2,
			12'h89E,
			12'h89A,
			12'h014
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h6,
			3'h2
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0000;
		expected_dispatch_uncompressed_by_way = 4'b0000;
		expected_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_pred_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = {20'h0, 20'h0, 20'h0, 20'h0};
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2, 7'h2, 7'h2, 7'h2};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h8, 5'h8, 5'h8, 5'h8};
		expected_dispatch_dest_old_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_dest_new_PR_by_way = {7'h23, 7'h22, 7'h21, 7'h20};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h0;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h0;
		expected_decode_unit_branch_update_GH = 12'h0;
		expected_decode_unit_branch_update_ras_index = 3'h0;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h0;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 2\n",
			"\t\tSDEQ:\n",
			"\t\t\t", "345678AE: ", "csrrw x4, 0x45, x19", "\n",
			"\t\t\t", "345678AA: ", "fence io,rw", "\n",
			"\t\t\t", "345678A6: ", "add x19, x27, x19", "\n",
			"\t\t\t", "345678A2: ", "addi x19, x19, 0x21", "\n",
			"\t\tDEC:\n",
			"\t\t\t", "3456789E: ", "sh x0, 0x21(x14)", "\n",
			"\t\t\t", "3456789A: ", "lh x22, 0x45(x21)", "\n",
			"\t\t\t", "80000014: ", "jalr x0, 0x508(x22) + pred", "\n",
			"\t\t\t", "80000010: ", "auipc x14, 0x69696", "\n",
			"\t\tRNM:\n",
			"\t\t\t", "8000000C: ", "sb x30, 0xcba(x8)", "\n",
			"\t\t\t", "80000008: ", "lb x31, 0xfed(x1)", "\n",
			"\t\t\t", "80000004: ", "jal x1, 0x23456", "\n",
			"\t\t\t", "80000000: ", "lui x5, 0xa5a5a", "\n",
			"\t\tDISP: NOP"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h04599273,
			32'h0c30000f,
			32'h013d89b3,
			32'h02198993
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678B2, 32'h345678B0,
			32'h345678AE, 32'h345678AC,
			32'h345678AA, 32'h345678A8,
			32'h345678A6, 32'h345678A4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hB2,
			8'hAE,
			8'hAA,
			8'hA6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678AE,
			32'h345678AA,
			32'h345678A6,
			32'h345678A2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hB0,
			8'hAC,
			8'hA8,
			8'hA4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8B2,
			12'h8AE,
			12'h8AA,
			12'h8A6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0000;
		expected_dispatch_uncompressed_by_way = 4'b0000;
		expected_dispatch_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_pred_PC_by_way = {32'h0, 32'h0, 32'h0, 32'h0};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = {20'h0, 20'h0, 20'h0, 20'h0};
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2, 7'h2, 7'h2, 7'h2};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h8, 5'h8, 5'h8, 5'h8};
		expected_dispatch_dest_old_PR_by_way = {7'h8, 7'h8, 7'h8, 7'h8};
		expected_dispatch_dest_new_PR_by_way = {7'h23, 7'h22, 7'h21, 7'h20};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h80000000;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h0;
		expected_decode_unit_branch_update_GH = 12'h0;
		expected_decode_unit_branch_update_ras_index = 3'h0;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h80000000;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 3\n",
			"\t\tSDEQ:\n",
			"\t\t\t", "345678AE: ", "ecall", "\n",
			"\t\t\t", "345678AA: ", "sret", "\n",
			"\t\t\t", "345678A6: ", "lr.w x10, (x20)", "\n",
			"\t\t\t", "345678B2: ", "mul x6, x12, x24", "\n",
			"\t\tDEC:\n",
			"\t\t\t", "345678AE: ", "csrrw x4, 0x45, x19", "\n",
			"\t\t\t", "345678AA: ", "fence io,rw", "\n",
			"\t\t\t", "345678A6: ", "add x19, x27, x19", "\n",
			"\t\t\t", "345678A2: ", "addi x19, x19, 0x21", "\n",
			"\t\tRNM:\n",
			"\t\t\t", "3456789E: ", "sh x0, 0x21(x14)", "\n",
			"\t\t\t", "3456789A: ", "lh x22, 0x45(x21)", "\n",
			"\t\t\t", "80000014: ", "jalr x0, 0x508(x22) + pred", "\n",
			"\t\t\t", "80000010: ", "auipc x14, 0x69696", "\n",
			"\t\tDISP:\n",
			"\t\t\t", "8000000C: ", "sb x30, 0xcba(x8)", "\n",
			"\t\t\t", "80000008: ", "lb x31, 0xfed(x1)", "\n",
			"\t\t\t", "80000004: ", "jal x1, 0x23456", "\n",
			"\t\t\t", "80000000: ", "lui x5, 0xa5a5a"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000073,
			32'h10200073,
			32'h100a252f,
			32'h03860333
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678C2, 32'h345678C0,
			32'h345678BE, 32'h345678BC,
			32'h345678BA, 32'h345678B8,
			32'h345678B6, 32'h345678B4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hC2,
			8'hBE,
			8'hBA,
			8'hB6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hC0,
			8'hBC,
			8'hB8,
			8'hB4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8C2,
			12'h8BE,
			12'h8BA,
			12'h8B6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0011;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0100;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b1000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h8000000C,
			32'h80000008,
			32'h80000004,
			32'h80000000
		};
		expected_dispatch_pred_PC_by_way = {
			32'h80000010,
			32'h8000000C,
			32'h80000008,
			32'h80000004
		};
		expected_dispatch_is_rename_by_way = 4'b0111;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h10,
			8'h0C,
			8'h08,
			8'h04
		};
		expected_dispatch_op_by_way = {4'b1000, 4'b1000, 4'b0010, 4'b0110};
		expected_dispatch_imm20_by_way = 80'h40cba08fed234565aa5a;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'ha5a5a2b7;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b1;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0011;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0100;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b1000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0011;
		expected_dispatch_valid_ldu_by_way = 4'b0100;
		expected_dispatch_valid_store_by_way = 4'b1000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h8, 7'h21, 7'h4, 7'hb};
		expected_dispatch_A_ready_by_way = 4'b1011;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0100;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h1e, 7'hd, 7'h16, 7'h1a};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h1a, 5'h1f, 5'h1, 5'h5};
		expected_dispatch_dest_old_PR_by_way = {7'h1a, 7'h1f, 7'h1, 7'h5};
		expected_dispatch_dest_new_PR_by_way = {7'h23, 7'h22, 7'h21, 7'h20};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0011;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h80000010;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h80000010;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 4\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: stall for trigger WFR\n",
			"\t\t\t", "345678AE: ", "ecall", "\n",
			"\t\t\t", "345678AA: ", "sret", "\n",
			"\t\t\t", "345678A6: ", "lr.w x10, (x20)", "\n",
			"\t\t\t", "345678B2: ", "mul x6, x12, x24", "\n",
			"\t\tRNM:\n",
			"\t\t\t", "345678AE: ", "csrrw x4, 0x45, x19", "\n",
			"\t\t\t", "345678AA: ", "fence io,rw", "\n",
			"\t\t\t", "345678A6: ", "add x19, x27, x19", "\n",
			"\t\t\t", "345678A2: ", "addi x19, x19, 0x21", "\n",
			"\t\tDISP:\n",
			"\t\t\t", "3456789E: ", "sh x0, 0x21(x14)", "\n",
			"\t\t\t", "3456789A: ", "lh x22, 0x45(x21)", "\n",
			"\t\t\t", "80000014: ", "jalr x0, 0x508(x22) + pred", "\n",
			"\t\t\t", "80000010: ", "auipc x14, 0x69696"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000073,
			32'h10200073,
			32'h100a252f,
			32'h03860333
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678C2, 32'h345678C0,
			32'h345678BE, 32'h345678BC,
			32'h345678BA, 32'h345678B8,
			32'h345678B6, 32'h345678B4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hC2,
			8'hBE,
			8'hBA,
			8'hB6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hC0,
			8'hBC,
			8'hB8,
			8'hB4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8C2,
			12'h8BE,
			12'h8BA,
			12'h8B6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0011;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0100;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b1000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b1;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b1;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b1;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h3456789E,
			32'h3456789A,
			32'h80000014,
			32'h80000010
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678A2,
			32'h3456789E,
			32'h3456789A,
			32'h80000014
		};
		expected_dispatch_is_rename_by_way = 4'b0101;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b01000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0010;
		expected_dispatch_mdp_info_by_way = {
			8'ha2,
			8'h9e,
			8'h9a,
			8'h14
		};
		expected_dispatch_op_by_way = {4'b0001, 4'b0001, 4'b0000, 4'b0111};
		expected_dispatch_imm20_by_way = 80'h71021a9045b050896696;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h69696717;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0011;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0100;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b1000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0011;
		expected_dispatch_valid_ldu_by_way = 4'b0100;
		expected_dispatch_valid_store_by_way = 4'b1000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h23, 7'h15, 7'h16, 7'h12};
		expected_dispatch_A_ready_by_way = 4'b0111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1101;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h0, 7'h20, 7'h08, 7'h16};
		expected_dispatch_B_ready_by_way = 4'b1011;
		expected_dispatch_B_is_zero_by_way = 4'b1000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h1, 5'h16, 5'h0, 5'he};
		expected_dispatch_dest_old_PR_by_way = {7'h21, 7'h16, 7'h0, 7'he};
		expected_dispatch_dest_new_PR_by_way = {7'h26, 7'h25, 7'h24, 7'h23};
		expected_dispatch_dest_is_link_ra_by_way = 4'b1000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678a2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678a2;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 5\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: trigger WFR",
			"\t\t\t", "345678AE: ", "inv ecall", "\n",
			"\t\t\t", "345678AA: ", "sret", "\n",
			"\t\t\t", "345678A6: ", "lr.w x10, (x20)", "\n",
			"\t\t\t", "345678B2: ", "mul x6, x12, x24", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: stall missing acks\n",
			"\t\t\t", "345678AE: ", "csrrw x4, 0x45, x19", "\n",
			"\t\t\t", "345678AA: ", "fence io,rw", "\n",
			"\t\t\t", "345678A6: ", "add x19, x27, x19", "\n",
			"\t\t\t", "345678A2: ", "addi x19, x19, 0x21"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000073,
			32'h10200073,
			32'h100a252f,
			32'h03860333
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678C2, 32'h345678C0,
			32'h345678BE, 32'h345678BC,
			32'h345678BA, 32'h345678B8,
			32'h345678B6, 32'h345678B4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hC2,
			8'hBE,
			8'hBA,
			8'hB6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hC0,
			8'hBC,
			8'hB8,
			8'hB4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8C2,
			12'h8BE,
			12'h8BA,
			12'h8B6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0001;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0100;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b1;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b1;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678AE,
			32'h345678AA,
			32'h345678A6,
			32'h345678A2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678B2,
			32'h345678AE,
			32'h345678AA,
			32'h345678A6
		};
		expected_dispatch_is_rename_by_way = 4'b1011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hb2,
			8'hae,
			8'haa,
			8'ha6
		};
		expected_dispatch_op_by_way = {4'b0001, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h99045000c3d801398021;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0100;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0100;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h02198993;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0001;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0100;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b1000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h26, 7'h00, 7'h1b, 7'h13};
		expected_dispatch_A_ready_by_way = 4'b0111;
		expected_dispatch_A_is_zero_by_way = 4'b0100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h20, 7'h03, 7'h24, 7'h21};
		expected_dispatch_B_ready_by_way = 4'b0100;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h04, 5'h00, 5'h13, 5'h13};
		expected_dispatch_dest_old_PR_by_way = {7'h04, 7'h00, 7'h24, 7'h13};
		expected_dispatch_dest_new_PR_by_way = {7'h28, 7'h27, 7'h26, 7'h24};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678b2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678b2;
		expected_decode_unit_trigger_wait_for_restart = 1'b1;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 6\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM:\n",
			"\t\t\t", "345678AE: ", "inv ecall", "\n",
			"\t\t\t", "345678AA: ", "sret", "\n",
			"\t\t\t", "345678A6: ", "lr.w x10, (x20)", "\n",
			"\t\t\t", "345678B2: ", "mul x6, x12, x24", "\n",
			"\t\tDISP:\n",
			"\t\t\t", "345678AE: ", "csrrw x4, 0x45, x19", "\n",
			"\t\t\t", "345678AA: ", "fence io,rw", "\n",
			"\t\t\t", "345678A6: ", "add x19, x27, x19", "\n",
			"\t\t\t", "345678A2: ", "addi x19, x19, 0x21"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000073,
			32'h10200073,
			32'h100a252f,
			32'h03860333
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678C2, 32'h345678C0,
			32'h345678BE, 32'h345678BC,
			32'h345678BA, 32'h345678B8,
			32'h345678B6, 32'h345678B4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hC2,
			8'hBE,
			8'hBA,
			8'hB6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hC0,
			8'hBC,
			8'hB8,
			8'hB4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8C2,
			12'h8BE,
			12'h8BA,
			12'h8B6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0010;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0001;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0100;
		tb_dispatch_ack_sysu_dq_by_way = 4'b1000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b1;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678AE,
			32'h345678AA,
			32'h345678A6,
			32'h345678A2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678B2,
			32'h345678AE,
			32'h345678AA,
			32'h345678A6
		};
		expected_dispatch_is_rename_by_way = 4'b1011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hb2,
			8'hae,
			8'haa,
			8'ha6
		};
		expected_dispatch_op_by_way = {4'b0001, 4'b0000, 4'b0000, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h99045000c3d801398021;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0100;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0100;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h02198993;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0001;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0100;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b1000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0010;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0001;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0100;
		expected_dispatch_valid_sysu_by_way = 4'b1000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h26, 7'h00, 7'h1b, 7'h13};
		expected_dispatch_A_ready_by_way = 4'b0111;
		expected_dispatch_A_is_zero_by_way = 4'b0100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h20, 7'h03, 7'h24, 7'h21};
		expected_dispatch_B_ready_by_way = 4'b0100;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h04, 5'h00, 5'h13, 5'h13};
		expected_dispatch_dest_old_PR_by_way = {7'h04, 7'h00, 7'h24, 7'h13};
		expected_dispatch_dest_new_PR_by_way = {7'h28, 7'h27, 7'h26, 7'h24};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678b2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678b2;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 7\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: ROB enQ stall\n",
			"\t\t\t", "345678AE: ", "inv ecall", "\n",
			"\t\t\t", "345678AA: ", "sret", "\n",
			"\t\t\t", "345678A6: ", "lr.w x10, (x20)", "\n",
			"\t\t\t", "345678B2: ", "mul x6, x12, x24", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000073,
			32'h10200073,
			32'h100a252f,
			32'h03860333
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678C2, 32'h345678C0,
			32'h345678BE, 32'h345678BC,
			32'h345678BA, 32'h345678B8,
			32'h345678B6, 32'h345678B4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hC2,
			8'hBE,
			8'hBA,
			8'hB6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hC0,
			8'hBC,
			8'hB8,
			8'hB4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8C2,
			12'h8BE,
			12'h8BA,
			12'h8B6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b0;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0001;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0010;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0100;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678C2,
			32'h345678BE,
			32'h345678BA,
			32'h345678B6
		};
		expected_dispatch_is_rename_by_way = 4'b0011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hc2,
			8'hbe,
			8'hba,
			8'hb6
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0010, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h0000000102a210060038;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h03860333;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0100;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h14, 7'hc};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b1100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h00, 7'h02, 7'h00, 7'h18};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b1010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h0a, 5'h06};
		expected_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h0a, 7'h06};
		expected_dispatch_dest_new_PR_by_way = {7'h2b, 7'h2a, 7'h29, 7'h27};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678b2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678b2;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 8\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP:\n",
			"\t\t\t", "345678AE: ", "inv ecall", "\n",
			"\t\t\t", "345678AA: ", "sret", "\n",
			"\t\t\t", "345678A6: ", "lr.w x10, (x20)", "\n",
			"\t\t\t", "345678B2: ", "mul x6, x12, x24", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000073,
			32'h10200073,
			32'h100a252f,
			32'h03860333
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678C2, 32'h345678C0,
			32'h345678BE, 32'h345678BC,
			32'h345678BA, 32'h345678B8,
			32'h345678B6, 32'h345678B4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hC2,
			8'hBE,
			8'hBA,
			8'hB6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hC0,
			8'hBC,
			8'hB8,
			8'hB4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8C2,
			12'h8BE,
			12'h8BA,
			12'h8B6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0001;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0010;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0100;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678C2,
			32'h345678BE,
			32'h345678BA,
			32'h345678B6
		};
		expected_dispatch_is_rename_by_way = 4'b0011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hc2,
			8'hbe,
			8'hba,
			8'hb6
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0010, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h0000000102a210060038;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h03860333;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0100;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0001;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0010;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0100;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h14, 7'hc};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b1100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h00, 7'h02, 7'h00, 7'h18};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b1010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h0a, 5'h06};
		expected_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h0a, 7'h06};
		expected_dispatch_dest_new_PR_by_way = {7'h2b, 7'h2a, 7'h29, 7'h27};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678b2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678b2;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"simple sequence cycle 9\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1111;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000073,
			32'h10200073,
			32'h100a252f,
			32'h03860333
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h345678C2, 32'h345678C0,
			32'h345678BE, 32'h345678BC,
			32'h345678BA, 32'h345678B8,
			32'h345678B6, 32'h345678B4
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'hC2,
			8'hBE,
			8'hBA,
			8'hB6
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		tb_istream_LH_by_way_SDEQ = {
			8'hC0,
			8'hBC,
			8'hB8,
			8'hB4
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h8C2,
			12'h8BE,
			12'h8BA,
			12'h8B6
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h0,
			3'hC,
			3'h8,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678C2,
			32'h345678BE,
			32'h345678BA,
			32'h345678B6
		};
		expected_dispatch_is_rename_by_way = 4'b0011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hc2,
			8'hbe,
			8'hba,
			8'hb6
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0010, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h0000000102a210060038;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h03860333;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b1100;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h14, 7'hc};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b1100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h00, 7'h02, 7'h00, 7'h18};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b1010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h0a, 5'h06};
		expected_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h29, 7'h27};
		expected_dispatch_dest_new_PR_by_way = {7'h2d, 7'h2c, 7'h2b, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678b2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678b2;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // complex sequence:
        test_case = "complex sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 0\n",
			"\t\tSDEQ: \n",
			"\t\t\t", "12345680: ", "inv illegal instr", "\n",
			"\t\t\t", "1234567E: ", "c.jr x1", "\n",
			"\t\t\t", "1234567A: ", "rem x24, x16, x0", "\n",
			"\t\t\t", "12345678: ", "c.swsp x6, 0x14", "\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b0111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1010;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'hffffffff,
			32'hf0f08082,
			32'h02086c33,
			32'h0f0fca1a
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b01000000, 8'b00000000,
			8'b00000000, 8'b01101001,
			8'b00000000, 8'b00000000,
			8'b10100000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h12345684, 32'h12345682,
			32'h12345682, 32'h40000002,
			32'h1234567E, 32'h1234567C,
			32'h1234567C, 32'h1234567A
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h84,
			8'h82,
			8'h7E,
			8'h7C
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h12345680,
			32'h1234567E,
			32'h1234567A,
			32'h12345678
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h82,
			8'h80,
			8'h7C,
			8'h7A
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h684,
			12'h682,
			12'h67E,
			12'h67C
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h0,
			3'hC,
			3'hA
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678C2,
			32'h345678BE,
			32'h345678BA,
			32'h345678B6
		};
		expected_dispatch_is_rename_by_way = 4'b0011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hc2,
			8'hbe,
			8'hba,
			8'hb6
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0010, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h0000000102a210060038;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h03860333;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b1100;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h14, 7'hc};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b1100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h00, 7'h02, 7'h00, 7'h18};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b1010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h0a, 5'h06};
		expected_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h29, 7'h27};
		expected_dispatch_dest_new_PR_by_way = {7'h2d, 7'h2c, 7'h2b, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678b2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678b2;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 1\n",
			"\t\tSDEQ: \n",
			"\t\t\t", "4000000A: ", "mulhu x8, x8, x8", "\n",
			"\t\t\t", "40000006: ", "amoxor.w.rl x8, x8, (x7) BAD PRED AFTER", "\n",
			"\t\t\t", "40000004: ", "c.lw x8, 20(x13)", "\n",
			"\t\t\t", "40000002: ", "c.slli x7, 23", "\n",
			"\t\tDEC: \n",
			"\t\t\t", "12345680: ", "inv illegal instr", "\n",
			"\t\t\t", "1234567E: ", "c.jr x1", "\n",
			"\t\t\t", "1234567A: ", "rem x24, x16, x0", "\n",
			"\t\t\t", "12345678: ", "c.swsp x6, 0x14", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1100;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h02843433,
			32'h2283a42f,
			32'hf0f04ac0,
			32'h0f0f03de
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b01101001, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h80000004, 32'h80000002,
			32'h80000000, 32'h40000008,
			32'h40000008, 32'h40000006,
			32'h40000006, 32'h40000004
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h80000000,
			32'h40000006,
			32'h40000004,
			32'h40000002
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678C2,
			32'h345678BE,
			32'h345678BA,
			32'h345678B6
		};
		expected_dispatch_is_rename_by_way = 4'b0011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hc2,
			8'hbe,
			8'hba,
			8'hb6
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0010, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h0000000102a210060038;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h03860333;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b1100;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h14, 7'hc};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b1100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h00, 7'h02, 7'h00, 7'h18};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b1010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h0a, 5'h06};
		expected_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h29, 7'h27};
		expected_dispatch_dest_new_PR_by_way = {7'h2d, 7'h2c, 7'h2b, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h345678b2;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h345678b2;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 2\n",
			"\t\tSDEQ: ignored\n",
			"\t\t\t", "90000004: ", "sra x31, x0, x0", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n",
			"\t\tDEC: stall -> restart sequence\n",
			"\t\t\t", "80000000: ", "mulhu x8, x8, x8", "\n",
			"\t\t\t", "40000006: ", "amoxor.w.rl x8, x8, (x7) BAD PRED AFTER", "\n",
			"\t\t\t", "40000004: ", "c.lw x8, 20(x13)", "\n",
			"\t\t\t", "40000002: ", "c.slli x7, 23", "\n",
			"\t\tRNM: \n",
			"\t\t\t", "12345680: ", "inv illegal instr", "\n",
			"\t\t\t", "1234567E: ", "c.jr x1", "\n",
			"\t\t\t", "1234567A: ", "rem x24, x16, x0", "\n",
			"\t\t\t", "12345678: ", "c.swsp x6, 0x14", "\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1100;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h40005fb3,
			32'h01828013,
			32'hf0f0b001,
			32'h00205003
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b10011001,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h80000004, 32'h80000002,
			32'h80000000, 32'h40000008,
			32'h40000008, 32'h40000006,
			32'h40000006, 32'h40000004
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h90000004,
			32'h90000000,
			32'h80000008,
			32'h80000004
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b1;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b1111;
		expected_dispatch_PC_by_way = {
			32'h345678BE,
			32'h345678BA,
			32'h345678B6,
			32'h345678B2
		};
		expected_dispatch_pred_PC_by_way = {
			32'h345678C2,
			32'h345678BE,
			32'h345678BA,
			32'h345678B6
		};
		expected_dispatch_is_rename_by_way = 4'b0011;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'hc2,
			8'hbe,
			8'hba,
			8'hb6
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0010, 4'b0000};
		expected_dispatch_imm20_by_way = 80'h0000000102a210060038;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h03860333;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b1100;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h14, 7'hc};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b1100;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h00, 7'h02, 7'h00, 7'h18};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b1010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h00, 5'h00, 5'h0a, 5'h06};
		expected_dispatch_dest_old_PR_by_way = {7'h00, 7'h00, 7'h29, 7'h27};
		expected_dispatch_dest_new_PR_by_way = {7'h2d, 7'h2c, 7'h2b, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h12345678;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h12345678;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 3\n",
			"\t\tSDEQ: ignored\n",
			"\t\t\t", "90000004: ", "sra x31, x0, x0", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n",
			"\t\tDEC: restart 0\n",
			"\t\t\t", "80000000: ", "mulhu x8, x8, x8", "\n",
			"\t\t\t", "40000006: ", "amoxor.w.rl x8, x8, (x7) BAD PRED AFTER", "\n",
			"\t\t\t", "40000004: ", "c.lw x8, 20(x13)", "\n",
			"\t\t\t", "40000002: ", "c.slli x7, 23", "\n",
			"\t\tRNM: \n",
			"\t\tDISP: stalled IQ ack\n",
			"\t\t\t", "12345680: ", "inv illegal instr", "\n",
			"\t\t\t", "1234567E: ", "c.jr x1", "\n",
			"\t\t\t", "1234567A: ", "rem x24, x16, x0", "\n",
			"\t\t\t", "12345678: ", "c.swsp x6, 0x14", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1100;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h40005fb3,
			32'h01828013,
			32'hf0f0b001,
			32'h00205003
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b10011001,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h80000004, 32'h80000002,
			32'h80000000, 32'h40000008,
			32'h40000008, 32'h40000006,
			32'h40000006, 32'h40000004
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h90000004,
			32'h90000000,
			32'h80000008,
			32'h80000004
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0010;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b1000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0001;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b1;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0111;
		expected_dispatch_uncompressed_by_way = 4'b1010;
		expected_dispatch_PC_by_way = {
			32'h12345680,
			32'h1234567E,
			32'h1234567A,
			32'h12345678
		};
		expected_dispatch_pred_PC_by_way = {
			32'h12345684,
			32'h40000002,
			32'h1234567E,
			32'h1234567A
		};
		expected_dispatch_is_rename_by_way = 4'b0010;
		expected_dispatch_pred_info_by_way = {
			8'b01000000,
			8'b01101001,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h84,
			8'h82,
			8'h7E,
			8'h7C
		};
		expected_dispatch_op_by_way = {4'b1111, 4'b0101, 4'b0110, 4'b0110};
		expected_dispatch_imm20_by_way = 80'hfffff000008602000014;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0f0fca1a;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0100;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h22, 7'h21, 7'h10, 7'h2};
		expected_dispatch_A_ready_by_way = 4'b0011;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1011;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0100;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h22, 7'h00, 7'h00, 7'h27};
		expected_dispatch_B_ready_by_way = 4'b0110;
		expected_dispatch_B_is_zero_by_way = 4'b0110;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h1f, 5'h01, 5'h18, 5'h14};
		expected_dispatch_dest_old_PR_by_way = {7'h22, 7'h21, 7'h18, 7'h14};
		expected_dispatch_dest_new_PR_by_way = {7'h2d, 7'h2c, 7'h2b, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0100;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b1;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h40000008;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h4000000a;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 4\n",
			"\t\tSDEQ: ignored\n",
			"\t\t\t", "90000004: ", "sra x31, x0, x0", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n",
			"\t\tDEC: restart 1\n",
			"\t\t\t", "80000000: ", "mulhu x8, x8, x8", "\n",
			"\t\t\t", "40000006: ", "amoxor.w.rl x8, x8, (x7) BAD PRED AFTER", "\n",
			"\t\t\t", "40000004: ", "c.lw x8, 20(x13)", "\n",
			"\t\t\t", "40000002: ", "c.slli x7, 23", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: \n",
			"\t\t\t", "12345680: ", "inv illegal instr", "\n",
			"\t\t\t", "1234567E: ", "c.jr x1", "\n",
			"\t\t\t", "1234567A: ", "rem x24, x16, x0", "\n",
			"\t\t\t", "12345678: ", "c.swsp x6, 0x14", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1100;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h40005fb3,
			32'h01828013,
			32'hf0f0b001,
			32'h00205003
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b10011001,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h80000004, 32'h80000002,
			32'h80000000, 32'h40000008,
			32'h40000008, 32'h40000006,
			32'h40000006, 32'h40000004
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h90000004,
			32'h90000000,
			32'h80000008,
			32'h80000004
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0010;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0100;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0001;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b1;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0111;
		expected_dispatch_uncompressed_by_way = 4'b1010;
		expected_dispatch_PC_by_way = {
			32'h12345680,
			32'h1234567E,
			32'h1234567A,
			32'h12345678
		};
		expected_dispatch_pred_PC_by_way = {
			32'h12345684,
			32'h40000002,
			32'h1234567E,
			32'h1234567A
		};
		expected_dispatch_is_rename_by_way = 4'b0010;
		expected_dispatch_pred_info_by_way = {
			8'b01000000,
			8'b01101001,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h84,
			8'h82,
			8'h7E,
			8'h7C
		};
		expected_dispatch_op_by_way = {4'b1111, 4'b0101, 4'b0110, 4'b0110};
		expected_dispatch_imm20_by_way = 80'hfffff000008602000014;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0f0fca1a;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0100;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0010;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0100;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0001;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h22, 7'h21, 7'h10, 7'h2};
		expected_dispatch_A_ready_by_way = 4'b0011;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1011;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0100;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h22, 7'h00, 7'h00, 7'h27};
		expected_dispatch_B_ready_by_way = 4'b0110;
		expected_dispatch_B_is_zero_by_way = 4'b0110;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h1f, 5'h01, 5'h18, 5'h14};
		expected_dispatch_dest_old_PR_by_way = {7'h22, 7'h21, 7'h18, 7'h14};
		expected_dispatch_dest_new_PR_by_way = {7'h2d, 7'h2c, 7'h2b, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0100;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h40000008;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h4000000a;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 5\n",
			"\t\tSDEQ: \n",
			"\t\t\t", "90000004: ", "illegal instr", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n",
			"\t\tDEC: restart 2\n",
			"\t\t\t", "80000000: ", "mulhu x8, x8, x8", "\n",
			"\t\t\t", "40000006: ", "amoxor.w.rl x8, x8, (x7) BAD PRED AFTER", "\n",
			"\t\t\t", "40000004: ", "c.lw x8, 20(x13)", "\n",
			"\t\t\t", "40000002: ", "c.slli x7, 23", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0101;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'hffff0000,
			32'h01828013,
			32'hf0f0b001,
			32'h00205003
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b10011001,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h90000008, 32'h90000006,
			32'h90000004, 32'h90000002,
			32'h8000000C, 32'h90000000,
			32'h80000008, 32'h80000006
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h08,
			8'h04,
			8'h0C,
			8'h08
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h90000004,
			32'h90000000,
			32'h80000008,
			32'h80000004
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h06,
			8'h02,
			8'h00,
			8'h06
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h008,
			12'h004,
			12'h00C,
			12'h008
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h6,
			3'h2,
			3'h0,
			3'h6
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0001;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0010;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0100;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0111;
		expected_dispatch_uncompressed_by_way = 4'b1100;
		expected_dispatch_PC_by_way = {
			32'h80000000,
			32'h40000006,
			32'h40000004,
			32'h40000002
		};
		expected_dispatch_pred_PC_by_way = {
			32'h80000004,
			32'h80000000,
			32'h40000006,
			32'h40000004
		};
		expected_dispatch_is_rename_by_way = 4'b1111;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b01101001,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		expected_dispatch_op_by_way = {4'b0011, 4'b0100, 4'b1010, 4'b0001};
		expected_dispatch_imm20_by_way = 80'h430283a2280001400017;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0100;
		expected_dispatch_io_rl_by_way = 4'b0100;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0f0f03de;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0001;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0100;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2d, 7'h2a, 7'h0d, 7'h07};
		expected_dispatch_A_ready_by_way = 4'b0011;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2c, 7'h08, 7'h17};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h08, 5'h07};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h2c, 7'h08, 7'h07};
		expected_dispatch_dest_new_PR_by_way = {7'h2e, 7'h2d, 7'h2c, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h40000008;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b1;
		expected_decode_unit_restart_PC = 32'h4000000a;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 6\n",
			"\t\tSDEQ: ignored\n",
			"\t\t\t", "90000004: ", "illegal instr", "\n",
			"\t\t\t", "90000000: ", "illegal instr", "\n",
			"\t\t\t", "80000008: ", "csrrwi x0, 0x15, 13 PAGE FAULT", "\n",
			"\t\t\t", "80000004: ", "c.lui x16, 29", "\n",
			"\t\tDEC: stall -> illegal instr WFR\n",
			"\t\t\t", "90000004: ", "illegal instr", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n",
			"\t\tRNM: \n",
			"\t\t\t", "80000000: ", "mulhu x8, x8, x8", "\n",
			"\t\t\t", "40000006: ", "amoxor.w.rl x8, x8, (x7) BAD PRED AFTER", "\n",
			"\t\t\t", "40000004: ", "c.lw x8, 20(x13)", "\n",
			"\t\t\t", "40000002: ", "c.slli x7, 23", "\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b1110;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h0156d073,
			32'h0f0f6875
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'h90000008, 32'h90000006,
			32'h90000004, 32'h90000002,
			32'h8000000C, 32'h90000000,
			32'h80000008, 32'h80000006
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'h90000004,
			32'h90000000,
			32'h80000008,
			32'h80000004
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0001;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0010;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0100;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b1;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0111;
		expected_dispatch_uncompressed_by_way = 4'b1100;
		expected_dispatch_PC_by_way = {
			32'h80000000,
			32'h40000006,
			32'h40000004,
			32'h40000002
		};
		expected_dispatch_pred_PC_by_way = {
			32'h80000004,
			32'h80000000,
			32'h40000006,
			32'h40000004
		};
		expected_dispatch_is_rename_by_way = 4'b1111;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b01101001,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		expected_dispatch_op_by_way = {4'b0011, 4'b0100, 4'b1010, 4'b0001};
		expected_dispatch_imm20_by_way = 80'h430283a2280001400017;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0100;
		expected_dispatch_io_rl_by_way = 4'b0100;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0f0f03de;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0001;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0100;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2d, 7'h2a, 7'h0d, 7'h07};
		expected_dispatch_A_ready_by_way = 4'b0011;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2c, 7'h08, 7'h17};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h08, 5'h07};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h2c, 7'h08, 7'h07};
		expected_dispatch_dest_new_PR_by_way = {7'h2e, 7'h2d, 7'h2c, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h40000008;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h4000000a;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 7\n",
			"\t\tSDEQ: \n",
			"\t\t\t", "A0000004: ", "illegal instr", "\n",
			"\t\t\t", "A0000002: ", "illegal instr", "\n",
			"\t\t\t", "9FFFFFFE: ", "csrrwi x0, 0x15, 0xd PAGE FAULT", "\n",
			"\t\t\t", "9FFFFFFC: ", "c.lui x16, 29", "\n",
			"\t\tDEC: illegal instr WFR\n",
			"\t\t\t", "90000004: ", "illegal instr", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: \n",
			"\t\t\t", "80000000: ", "mulhu x8, x8, x8", "\n",
			"\t\t\t", "40000006: ", "amoxor.w.rl x8, x8, (x7) BAD PRED AFTER", "\n",
			"\t\t\t", "40000004: ", "c.lw x8, 20(x13)", "\n",
			"\t\t\t", "40000002: ", "c.slli x7, 23", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0010;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h0156d073,
			32'h0f0f6875
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b11111111,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hA0000008, 32'hA0000006,
			32'hA0000006, 32'hA0000004,
			32'hA0000002, 32'hA0000000,
			32'hA0000000, 32'h9FFFFFFE
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00001010;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h08,
			8'h06,
			8'h02,
			8'h00
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h06,
			8'h04,
			8'h00,
			8'hFE
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h008,
			12'h006,
			12'h002,
			12'h000
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h6,
			3'h4,
			3'h0,
			3'hE
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0001;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0010;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0100;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0111;
		expected_dispatch_uncompressed_by_way = 4'b1100;
		expected_dispatch_PC_by_way = {
			32'h80000000,
			32'h40000006,
			32'h40000004,
			32'h40000002
		};
		expected_dispatch_pred_PC_by_way = {
			32'h80000004,
			32'h80000000,
			32'h40000006,
			32'h40000004
		};
		expected_dispatch_is_rename_by_way = 4'b1111;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b01101001,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		expected_dispatch_op_by_way = {4'b0011, 4'b0100, 4'b1010, 4'b0001};
		expected_dispatch_imm20_by_way = 80'h430283a2280001400017;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0100;
		expected_dispatch_io_rl_by_way = 4'b0100;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0f0f03de;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0001;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0010;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0100;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0001;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0010;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0100;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h2d, 7'h2a, 7'h0d, 7'h07};
		expected_dispatch_A_ready_by_way = 4'b0011;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2c, 7'h08, 7'h17};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h08, 5'h07};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h2c, 7'h08, 7'h07};
		expected_dispatch_dest_new_PR_by_way = {7'h2e, 7'h2d, 7'h2c, 7'h2a};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h80000004;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h80000004;
		expected_decode_unit_trigger_wait_for_restart = 1'b1;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 8\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: stall -> page fault WFR\n",
			"\t\t\t", "A0000004: ", "illegal instr", "\n",
			"\t\t\t", "A0000002: ", "illegal instr", "\n",
			"\t\t\t", "9FFFFFFE: ", "csrrwi x0, 0x15, 0xd PAGE FAULT", "\n",
			"\t\t\t", "9FFFFFFC: ", "c.lui x16, 29", "\n",
			"\t\tRNM: \n",
			"\t\t\t", "90000004: ", "illegal instr", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0010;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h0156d073,
			32'h0f0f6875
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b11111111,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hA0000008, 32'hA0000006,
			32'hA0000006, 32'hA0000004,
			32'hA0000002, 32'hA0000000,
			32'hA0000000, 32'h9FFFFFFE
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0100;
		tb_dispatch_ack_bru_dq_by_way = 4'b0010;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0001;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b1;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b0101;
		expected_dispatch_PC_by_way = {
			32'h90000004,
			32'h90000000,
			32'h80000008,
			32'h80000004
		};
		expected_dispatch_pred_PC_by_way = {
			32'h90000006,
			32'h90000004,
			32'h90000000,
			32'h80000008
		};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b10011001,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h08,
			8'h04,
			8'h0C,
			8'h08
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0100, 4'b0101};
		expected_dispatch_imm20_by_way = 80'h0000028018ff80105002;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b1;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h3;
		expected_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0100;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0010;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h20, 7'h00, 7'h00};
		expected_dispatch_A_ready_by_way = 4'b1011;
		expected_dispatch_A_is_zero_by_way = 4'b0011;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0100;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2b, 7'h00, 7'h02};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h00, 5'h00, 5'h00};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h00, 7'h00, 7'h00};
		expected_dispatch_dest_new_PR_by_way = {7'h31, 7'h30, 7'h2f, 7'h2e};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h80000004;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h80000004;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 9\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: page fault WFR\n",
			"\t\t\t", "A0000004: ", "illegal instr", "\n",
			"\t\t\t", "A0000002: ", "illegal instr", "\n",
			"\t\t\t", "9FFFFFFE: ", "csrrwi x0, 0x15, 0xd PAGE FAULT", "\n",
			"\t\t\t", "9FFFFFFC: ", "c.lui x16, 29", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: \n",
			"\t\t\t", "90000004: ", "illegal instr", "\n",
			"\t\t\t", "90000000: ", "addi x0, x5, 24", "\n",
			"\t\t\t", "80000008: ", "c.j -2048", "\n",
			"\t\t\t", "80000004: ", "lhu, x0, 2(x0)", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0010;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h0156d073,
			32'h0f0f6875
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b11111111,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hA0000008, 32'hA0000006,
			32'hA0000006, 32'hA0000004,
			32'hA0000002, 32'hA0000000,
			32'hA0000000, 32'h9FFFFFFE
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0100;
		tb_dispatch_ack_bru_dq_by_way = 4'b0010;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0001;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b0101;
		expected_dispatch_PC_by_way = {
			32'h90000004,
			32'h90000000,
			32'h80000008,
			32'h80000004
		};
		expected_dispatch_pred_PC_by_way = {
			32'h90000006,
			32'h90000004,
			32'h90000000,
			32'h80000008
		};
		expected_dispatch_is_rename_by_way = 4'b0000;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b10011001,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h08,
			8'h04,
			8'h0C,
			8'h08
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0100, 4'b0101};
		expected_dispatch_imm20_by_way = 80'h0000028018ff80105002;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b1;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h3;
		expected_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0100;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0010;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0100;
		expected_dispatch_valid_bru_by_way = 4'b0010;
		expected_dispatch_valid_ldu_by_way = 4'b0001;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h20, 7'h00, 7'h00};
		expected_dispatch_A_ready_by_way = 4'b1011;
		expected_dispatch_A_is_zero_by_way = 4'b0011;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0100;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2b, 7'h00, 7'h02};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0010;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h00, 5'h00, 5'h00};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h00, 7'h00, 7'h00};
		expected_dispatch_dest_new_PR_by_way = {7'h31, 7'h30, 7'h2f, 7'h2e};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h9ffffffc;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h9ffffffc;
		expected_decode_unit_trigger_wait_for_restart = 1'b1;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle A\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: \n",
			"\t\t\t", "A0000004: ", "illegal instr", "\n",
			"\t\t\t", "A0000002: ", "illegal instr", "\n",
			"\t\t\t", "9FFFFFFE: ", "csrrwi x0, 0x15, 0xd PAGE FAULT", "\n",
			"\t\t\t", "9FFFFFFC: ", "c.lui x16, 29", "\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0010;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h0156d073,
			32'h0f0f6875
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b11111111,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hA0000008, 32'hA0000006,
			32'hA0000006, 32'hA0000004,
			32'hA0000002, 32'hA0000000,
			32'hA0000000, 32'h9FFFFFFE
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0001;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0010;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b0010;
		expected_dispatch_PC_by_way = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		expected_dispatch_pred_PC_by_way = {
			32'hA0000006,
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b11111111,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h08,
			8'h06,
			8'h02,
			8'h00
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0110};
		expected_dispatch_imm20_by_way = 80'h00000000006d0151d000;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b1;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h1;
		expected_dispatch_illegal_instr32 = 32'h0f0f6875;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0001;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0010;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h0d, 7'h10};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2d, 7'h15, 7'h1d};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h00, 5'h10};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h2d, 7'h00, 7'h10};
		expected_dispatch_dest_new_PR_by_way = {7'h31, 7'h30, 7'h2f, 7'h2e};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h9ffffffc;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h9ffffffc;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle B (rob restart + restore checkpoint 0)\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: \n",
			"\t\t\t", "A0000004: ", "illegal instr", "\n",
			"\t\t\t", "A0000002: ", "illegal instr", "\n",
			"\t\t\t", "9FFFFFFE: ", "csrrwi x0, 0x15, 0xd PAGE FAULT", "\n",
			"\t\t\t", "9FFFFFFC: ", "c.lui x16, 29", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0010;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h0156d073,
			32'h0f0f6875
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b11111111,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hA0000008, 32'hA0000006,
			32'hA0000006, 32'hA0000004,
			32'hA0000002, 32'hA0000000,
			32'hA0000000, 32'h9FFFFFFE
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0001;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0010;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b1;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b1;
		tb_rob_branch_update_has_checkpoint = 1'b1;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b1;
		tb_rob_branch_update_is_taken = 1'b1;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'b10100101;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h12345678;
		tb_rob_branch_update_target_PC = 32'h9abcdef0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b1;
		tb_rob_checkpoint_map_table_restore_valid = 1'b1;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b1;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0000;
		tb_rob_map_table_write_AR_by_port = {5'h0, 5'h0, 5'h0, 5'h0};
		tb_rob_map_table_write_PR_by_port = {7'h0, 7'h0, 7'h0, 7'h0};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0011;
		expected_dispatch_uncompressed_by_way = 4'b0010;
		expected_dispatch_PC_by_way = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		expected_dispatch_pred_PC_by_way = {
			32'hA0000006,
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b11111111,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h08,
			8'h06,
			8'h02,
			8'h00
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0110};
		expected_dispatch_imm20_by_way = 80'h00000000006d0151d000;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b1;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h1;
		expected_dispatch_illegal_instr32 = 32'h0f0f6875;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0001;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0010;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0001;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0010;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h0d, 7'h10};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2d, 7'h15, 7'h1d};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h00, 5'h10};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h2d, 7'h00, 7'h10};
		expected_dispatch_dest_new_PR_by_way = {7'h31, 7'h30, 7'h2f, 7'h2e};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b1;
		expected_decode_unit_branch_update_has_checkpoint = 1'b1;
		expected_decode_unit_branch_update_is_mispredict = 1'b1;
		expected_decode_unit_branch_update_is_taken = 1'b1;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'b10100101;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h12345678;
		expected_decode_unit_branch_update_target_PC = 32'h9abcdef0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h9ffffffc;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle C (rob map r4:7->p74:77, free p1)\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b1111;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0010;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h0156d073,
			32'h0f0f6875
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b11111111,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hA0000008, 32'hA0000006,
			32'hA0000006, 32'hA0000004,
			32'hA0000002, 32'hA0000000,
			32'hA0000000, 32'h9FFFFFFE
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h02,
			8'h08,
			8'h06,
			8'h04
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h004,
			12'h000,
			12'h008,
			12'h006
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'h2,
			3'h8,
			3'h6,
			3'h4
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0001;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0010;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b1;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b1111;
		tb_rob_map_table_write_AR_by_port = {5'h7, 5'h6, 5'h5, 5'h4};
		tb_rob_map_table_write_PR_by_port = {7'h77, 7'h76, 7'h75, 7'h74};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0010;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h1, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b0010;
		expected_dispatch_PC_by_way = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		expected_dispatch_pred_PC_by_way = {
			32'hA0000006,
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b11111111,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0110};
		expected_dispatch_imm20_by_way = 80'h00000000006d0151d000;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b1;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h2;
		expected_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0001;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0010;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h0d, 7'h2e};
		expected_dispatch_A_ready_by_way = 4'b1110;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h2d, 7'h2d, 7'h15, 7'h1d};
		expected_dispatch_B_ready_by_way = 4'b0011;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h00, 5'h10};
		expected_dispatch_dest_old_PR_by_way = {7'h2d, 7'h2d, 7'h00, 7'h2e};
		expected_dispatch_dest_new_PR_by_way = {7'h32, 7'h31, 7'h30, 7'h2f};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0010;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h9ffffffc;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h9ffffffc;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle D\n",
			"\t\tSDEQ: \n",
			"\t\t\t", "B0000008: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000006: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000004: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000000: ", "divu x1, x7, x5", "\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b1;
		tb_istream_valid_by_way_SDEQ = 4'b0001;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0001;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h0253d0b3
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hB000000C, 32'hB000000A,
			32'hB000000A, 32'hB0000008,
			32'hB0000008, 32'hB0000006,
			32'hB0000004, 32'hB0000002
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h0C,
			8'h0A,
			8'h08,
			8'h04
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hB0000008,
			32'hB0000006,
			32'hB0000004,
			32'hB0000000
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h0A,
			8'h08,
			8'h06,
			8'h02
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h00C,
			12'h00A,
			12'h008,
			12'h004
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'hA,
			3'h8,
			3'h6,
			3'h2
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0001;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0010;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0100;
		tb_rob_map_table_write_AR_by_port = {5'h7, 5'h6, 5'h5, 5'h4};
		tb_rob_map_table_write_PR_by_port = {7'h77, 7'h76, 7'h75, 7'h74};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b0010;
		expected_dispatch_PC_by_way = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		expected_dispatch_pred_PC_by_way = {
			32'hA0000006,
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b11111111,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0110};
		expected_dispatch_imm20_by_way = 80'h00000000006d0151d000;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b1;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h2;
		expected_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0001;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0010;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h0d, 7'h10};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h08, 7'h08, 7'h15, 7'h1d};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h00, 5'h10};
		expected_dispatch_dest_old_PR_by_way = {7'h08, 7'h08, 7'h00, 7'h10};
		expected_dispatch_dest_new_PR_by_way = {7'h32, 7'h31, 7'h30, 7'h2f};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h9ffffffc;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h9ffffffc;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle E\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: \n",
			"\t\t\t", "B0000008: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000006: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000004: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000000: ", "divu x1, x7, x5", "\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0001;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0001;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h0253d0b3
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hB000000C, 32'hB000000A,
			32'hB000000A, 32'hB0000008,
			32'hB0000008, 32'hB0000006,
			32'hB0000004, 32'hB0000002
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h0C,
			8'h0A,
			8'h08,
			8'h04
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hB0000008,
			32'hB0000006,
			32'hB0000004,
			32'hB0000000
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h0A,
			8'h08,
			8'h06,
			8'h02
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h00C,
			12'h00A,
			12'h008,
			12'h004
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'hA,
			3'h8,
			3'h6,
			3'h2
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0001;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0010;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0100;
		tb_rob_map_table_write_AR_by_port = {5'h7, 5'h6, 5'h5, 5'h4};
		tb_rob_map_table_write_PR_by_port = {7'h77, 7'h76, 7'h75, 7'h74};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b0010;
		expected_dispatch_PC_by_way = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		expected_dispatch_pred_PC_by_way = {
			32'hA0000006,
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b11111111,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0110};
		expected_dispatch_imm20_by_way = 80'h00000000006d0151d000;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b1;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h2;
		expected_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0001;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0010;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h0d, 7'h10};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h08, 7'h08, 7'h15, 7'h1d};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h00, 5'h10};
		expected_dispatch_dest_old_PR_by_way = {7'h08, 7'h08, 7'h00, 7'h10};
		expected_dispatch_dest_new_PR_by_way = {7'h32, 7'h31, 7'h30, 7'h2f};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'h9ffffffc;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'h9ffffffc;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle F\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: \n",
			"\t\t\t", "B0000008: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000006: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000004: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000000: ", "divu x1, x7, x5", "\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0001;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0001;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h0253d0b3
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hB000000C, 32'hB000000A,
			32'hB000000A, 32'hB0000008,
			32'hB0000008, 32'hB0000006,
			32'hB0000004, 32'hB0000002
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h0C,
			8'h0A,
			8'h08,
			8'h04
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hB0000008,
			32'hB0000006,
			32'hB0000004,
			32'hB0000000
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h0A,
			8'h08,
			8'h06,
			8'h02
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h00C,
			12'h00A,
			12'h008,
			12'h004
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'hA,
			3'h8,
			3'h6,
			3'h2
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0000;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0001;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0010;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0100;
		tb_rob_map_table_write_AR_by_port = {5'h7, 5'h6, 5'h5, 5'h4};
		tb_rob_map_table_write_PR_by_port = {7'h77, 7'h76, 7'h75, 7'h74};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b1111;
		expected_dispatch_uncompressed_by_way = 4'b0010;
		expected_dispatch_PC_by_way = {
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE,
			32'h9FFFFFFC
		};
		expected_dispatch_pred_PC_by_way = {
			32'hA0000006,
			32'hA0000004,
			32'hA0000002,
			32'h9FFFFFFE
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b11111111,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h04,
			8'h00,
			8'h08,
			8'h06
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0110};
		expected_dispatch_imm20_by_way = 80'h00000000006d0151d000;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b1;
		expected_dispatch_exception_present = 1'b1;
		expected_dispatch_exception_index = 2'h2;
		expected_dispatch_illegal_instr32 = 32'h00000000;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0001;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0010;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h0d, 7'h10};
		expected_dispatch_A_ready_by_way = 4'b1111;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h08, 7'h08, 7'h15, 7'h1d};
		expected_dispatch_B_ready_by_way = 4'b1111;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h00, 5'h10};
		expected_dispatch_dest_old_PR_by_way = {7'h08, 7'h08, 7'h00, 7'h10};
		expected_dispatch_dest_new_PR_by_way = {7'h32, 7'h31, 7'h30, 7'h2f};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0000;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'hB0000000;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'hB0000000;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 10\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: \n",
			"\t\t\t", "B0000008: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000006: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000004: ", "inv illegal instr", "\n",
			"\t\t\t", "B0000000: ", "divu x1, x7, x5", "\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0001;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0001;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h0253d0b3
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hB000000C, 32'hB000000A,
			32'hB000000A, 32'hB0000008,
			32'hB0000008, 32'hB0000006,
			32'hB0000004, 32'hB0000002
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h0C,
			8'h0A,
			8'h08,
			8'h04
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hB0000008,
			32'hB0000006,
			32'hB0000004,
			32'hB0000000
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h0A,
			8'h08,
			8'h06,
			8'h02
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h00C,
			12'h00A,
			12'h008,
			12'h004
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'hA,
			3'h8,
			3'h6,
			3'h2
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0001;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0100;
		tb_rob_map_table_write_AR_by_port = {5'h7, 5'h6, 5'h5, 5'h4};
		tb_rob_map_table_write_PR_by_port = {7'h77, 7'h76, 7'h75, 7'h74};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b1;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0001;
		expected_dispatch_uncompressed_by_way = 4'b0001;
		expected_dispatch_PC_by_way = {
			32'hB0000008,
			32'hB0000006,
			32'hB0000004,
			32'hB0000000
		};
		expected_dispatch_pred_PC_by_way = {
			32'hB000000A,
			32'hB0000008,
			32'hB0000006,
			32'hB0000004
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h0C,
			8'h0A,
			8'h08,
			8'h04
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0101};
		expected_dispatch_imm20_by_way = 80'h0000000000000003d025;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0253d0b3;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0001;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h02, 7'h77};
		expected_dispatch_A_ready_by_way = 4'b1110;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h08, 7'h08, 7'h08, 7'h75};
		expected_dispatch_B_ready_by_way = 4'b1110;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h08, 5'h01};
		expected_dispatch_dest_old_PR_by_way = {7'h08, 7'h08, 7'h08, 7'h01};
		expected_dispatch_dest_new_PR_by_way = {7'h32, 7'h31, 7'h30, 7'h2f};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0001;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'hB0000000;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'hB0000000;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"complex sequence cycle 11\n",
			"\t\tSDEQ: NOP\n",
			"\t\tDEC: NOP\n",
			"\t\tRNM: NOP\n",
			"\t\tDISP: NOP\n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input from istream
		tb_istream_valid_SDEQ = 1'b0;
		tb_istream_valid_by_way_SDEQ = 4'b0001;
		tb_istream_uncompressed_by_way_SDEQ = 4'b0001;
		tb_istream_instr_2B_by_way_by_chunk_SDEQ = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h0253d0b3
		};
		tb_istream_pred_info_by_way_by_chunk_SDEQ = {
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000,
			8'b00000000, 8'b00000000
		};
		tb_istream_pred_lru_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_pred_PC_by_way_by_chunk_SDEQ = {
			32'hB000000C, 32'hB000000A,
			32'hB000000A, 32'hB0000008,
			32'hB0000008, 32'hB0000006,
			32'hB0000004, 32'hB0000002
		};
		tb_istream_page_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_access_fault_by_way_by_chunk_SDEQ = 8'b00000000;
		tb_istream_mdp_info_by_way_SDEQ = {
			8'h0C,
			8'h0A,
			8'h08,
			8'h04
		};
		tb_istream_PC_by_way_SDEQ = {
			32'hB0000008,
			32'hB0000006,
			32'hB0000004,
			32'hB0000000
		};
		tb_istream_LH_by_way_SDEQ = {
			8'h0A,
			8'h08,
			8'h06,
			8'h02
		};
		tb_istream_GH_by_way_SDEQ = {
			12'h00C,
			12'h00A,
			12'h008,
			12'h004
		};
		tb_istream_ras_index_by_way_SDEQ = {
			3'hA,
			3'h8,
			3'h6,
			3'h2
		};
	    // feedback to istream
	    // op dispatch by way:
	    // 4-way ROB entry
		tb_dispatch_rob_enq_ready = 1'b1;
	    // general instr info
	    // ordering
	    // exception info
		// checkpoint info
	    // instr IQ attempts
	    // instr FU valids
	    // operand A
	    // operand B
	    // dest operand
	    // instr IQ acks
		tb_dispatch_ack_alu_reg_mdu_dq_by_way = 4'b0001;
		tb_dispatch_ack_alu_imm_dq_by_way = 4'b0000;
		tb_dispatch_ack_bru_dq_by_way = 4'b0000;
		tb_dispatch_ack_ldu_dq_by_way = 4'b0000;
		tb_dispatch_ack_stamofu_dq_by_way = 4'b0000;
		tb_dispatch_ack_sysu_dq_by_way = 4'b0000;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_trap_sfence = 1'b0;
		tb_rob_restart_trap_wfi = 1'b0;
		tb_rob_restart_trap_sret = 1'b0;
		// kill from ROB
		tb_rob_kill_valid = 1'b0;
	    // branch update from ROB
		tb_rob_branch_update_valid = 1'b0;
		tb_rob_branch_update_has_checkpoint = 1'b0;
		tb_rob_branch_update_checkpoint_index = 3'h0;
		tb_rob_branch_update_is_mispredict = 1'b0;
		tb_rob_branch_update_is_taken = 1'b0;
		tb_rob_branch_update_use_upct = 1'b0;
		tb_rob_branch_update_intermediate_pred_info = 8'h0;
		tb_rob_branch_update_pred_lru = 1'b0;
		tb_rob_branch_update_start_PC = 32'h0;
		tb_rob_branch_update_target_PC = 32'h0;
	    // ROB control of rename
		tb_rob_controlling_rename = 1'b0;
		tb_rob_checkpoint_map_table_restore_valid = 1'b0;
		tb_rob_checkpoint_map_table_restore_index = 3'h0;
		tb_rob_checkpoint_clear_valid = 1'b0;
		tb_rob_checkpoint_clear_index = 3'h0;
		tb_rob_map_table_write_valid_by_port = 4'b0100;
		tb_rob_map_table_write_AR_by_port = {5'h7, 5'h6, 5'h5, 5'h4};
		tb_rob_map_table_write_PR_by_port = {7'h77, 7'h76, 7'h75, 7'h74};
		// ROB physical register freeing
		tb_rob_PR_free_req_valid_by_bank = 4'b0000;
		tb_rob_PR_free_req_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // branch update to fetch unit
	    // decode unit control
		// hardware failure

		@(negedge CLK);

		// outputs:

	    // input from istream
	    // feedback to istream
		expected_istream_stall_SDEQ = 1'b0;
	    // op dispatch by way:
	    // 4-way ROB entry
		expected_dispatch_rob_enq_valid = 1'b0;
		expected_dispatch_rob_enq_killed = 1'b0;
	    // general instr info
		expected_dispatch_valid_by_way = 4'b0001;
		expected_dispatch_uncompressed_by_way = 4'b0001;
		expected_dispatch_PC_by_way = {
			32'hB0000008,
			32'hB0000006,
			32'hB0000004,
			32'hB0000000
		};
		expected_dispatch_pred_PC_by_way = {
			32'hB000000A,
			32'hB0000008,
			32'hB0000006,
			32'hB0000004
		};
		expected_dispatch_is_rename_by_way = 4'b0001;
		expected_dispatch_pred_info_by_way = {
			8'b00000000,
			8'b00000000,
			8'b00000000,
			8'b00000000
		};
		expected_dispatch_pred_lru_by_way = 4'b0000;
		expected_dispatch_mdp_info_by_way = {
			8'h0C,
			8'h0A,
			8'h08,
			8'h04
		};
		expected_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0101};
		expected_dispatch_imm20_by_way = 80'h0000000000000003d025;
	    // ordering
		expected_dispatch_mem_aq_by_way = 4'b0000;
		expected_dispatch_io_aq_by_way = 4'b0000;
		expected_dispatch_mem_rl_by_way = 4'b0000;
		expected_dispatch_io_rl_by_way = 4'b0000;
	    // exception info
		expected_dispatch_is_page_fault = 1'b0;
		expected_dispatch_is_access_fault = 1'b0;
		expected_dispatch_is_illegal_instr = 1'b0;
		expected_dispatch_exception_present = 1'b0;
		expected_dispatch_exception_index = 2'h0;
		expected_dispatch_illegal_instr32 = 32'h0253d0b3;
		// checkpoint info
		expected_dispatch_has_checkpoint = 1'b0;
		expected_dispatch_checkpoint_index = 3'h0;
	    // instr IQ attempts
		expected_dispatch_attempt_alu_reg_mdu_dq_by_way = 4'b0001;
		expected_dispatch_attempt_alu_imm_dq_by_way = 4'b0000;
		expected_dispatch_attempt_bru_dq_by_way = 4'b0000;
		expected_dispatch_attempt_ldu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_stamofu_dq_by_way = 4'b0000;
		expected_dispatch_attempt_sysu_dq_by_way = 4'b0000;
	    // instr FU valids
		expected_dispatch_valid_alu_reg_by_way = 4'b0000;
		expected_dispatch_valid_mdu_by_way = 4'b0000;
		expected_dispatch_valid_alu_imm_by_way = 4'b0000;
		expected_dispatch_valid_bru_by_way = 4'b0000;
		expected_dispatch_valid_ldu_by_way = 4'b0000;
		expected_dispatch_valid_store_by_way = 4'b0000;
		expected_dispatch_valid_amo_by_way = 4'b0000;
		expected_dispatch_valid_fence_by_way = 4'b0000;
		expected_dispatch_valid_sysu_by_way = 4'b0000;
	    // operand A
		expected_dispatch_A_PR_by_way = {7'h02, 7'h02, 7'h02, 7'h77};
		expected_dispatch_A_ready_by_way = 4'b1110;
		expected_dispatch_A_is_zero_by_way = 4'b0000;
		expected_dispatch_A_unneeded_or_is_zero_by_way = 4'b1111;
		expected_dispatch_A_is_ret_ra_by_way = 4'b0000;
	    // operand B
		expected_dispatch_B_PR_by_way = {7'h08, 7'h08, 7'h08, 7'h75};
		expected_dispatch_B_ready_by_way = 4'b1110;
		expected_dispatch_B_is_zero_by_way = 4'b0000;
		expected_dispatch_B_unneeded_or_is_zero_by_way = 4'b1111;
	    // dest operand
		expected_dispatch_dest_AR_by_way = {5'h08, 5'h08, 5'h08, 5'h01};
		expected_dispatch_dest_old_PR_by_way = {7'h08, 7'h08, 7'h08, 7'h2f};
		expected_dispatch_dest_new_PR_by_way = {7'h33, 7'h32, 7'h31, 7'h30};
		expected_dispatch_dest_is_link_ra_by_way = 4'b0001;
	    // instr IQ acks
	    // writeback bus by bank
	    // fetch + decode restart from ROB
	    // branch update from ROB
	    // ROB control of rename
		// ROB physical register freeing
		expected_rob_PR_free_resp_ack_by_bank = 4'b0000;
	    // branch update to fetch unit
		expected_decode_unit_branch_update_valid = 1'b0;
		expected_decode_unit_branch_update_has_checkpoint = 1'b0;
		expected_decode_unit_branch_update_is_mispredict = 1'b0;
		expected_decode_unit_branch_update_is_taken = 1'b0;
		expected_decode_unit_branch_update_is_complex = 1'b0;
		expected_decode_unit_branch_update_use_upct = 1'b0;
		expected_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		expected_decode_unit_branch_update_pred_lru = 1'b0;
		expected_decode_unit_branch_update_start_PC = 32'hB0000000;
		expected_decode_unit_branch_update_target_PC = 32'h0;
		expected_decode_unit_branch_update_LH = 8'h06;
		expected_decode_unit_branch_update_GH = 12'h008;
		expected_decode_unit_branch_update_ras_index = 3'h6;
	    // decode unit control
		expected_decode_unit_restart_valid = 1'b0;
		expected_decode_unit_restart_PC = 32'hB0000000;
		expected_decode_unit_trigger_wait_for_restart = 1'b0;
		// hardware failure
		expected_unrecoverable_fault = 1'b0;

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