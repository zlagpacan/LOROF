/*
    Filename: rob.sv
    Author: zlagpacan
    Description: RTL for Reorder Buffer
    Spec: LOROF/spec/design/rob.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module rob #(
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
) (
    // seq
    input logic CLK,
    input logic nRST,
    
    // 4-way ROB dispatch:
    input logic                                 dispatch_enq_valid,
    input logic                                 dispatch_enq_killed,
    // general instr info
    input logic [3:0]                           dispatch_valid_by_way,
    input logic [3:0]                           dispatch_uncompressed_by_way,
    input logic [3:0][31:0]                     dispatch_PC_by_way,
    input logic [3:0]                           dispatch_is_rename_by_way,
    // exception info
    input logic                             	dispatch_is_page_fault,
    input logic                             	dispatch_is_access_fault,
    input logic                             	dispatch_is_illegal_instr,
	input logic 								dispatch_exception_present,
	input logic [1:0]					        dispatch_exception_index,
    input logic [31:0]                          dispatch_illegal_instr32,
	// checkpoint info
	input logic									dispatch_has_checkpoint,
	input logic [CHECKPOINT_INDEX_WIDTH-1:0]    dispatch_checkpoint_index,
    // instr FU valids
	input logic [3:0]                           dispatch_attempt_ldu_dq_by_way,
    // dest operand
    input logic [3:0][4:0]                      dispatch_dest_AR_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]         dispatch_dest_old_PR_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]         dispatch_dest_new_PR_by_way,

    // ROB dispatch feedback
    output logic                                dispatch_enq_ready,
    output logic [3:0][LOG_ROB_ENTRIES-1:0]     dispatch_ROB_index_by_way,

    // writeback bus complete notif by bank
    input logic [PRF_BANK_COUNT-1:0]                        complete_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   complete_bus_ROB_index_by_bank,

    // LDU complete notif
    input logic                         ldu_complete_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_complete_ROB_index,

    // STAMOFU complete notif
    input logic                         stamofu_complete_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_complete_ROB_index,

    // branch notification to ROB
    input logic                             branch_notif_valid,
    input logic [LOG_ROB_ENTRIES-1:0]       branch_notif_ROB_index,
    input logic                             branch_notif_is_mispredict,
    input logic                             branch_notif_is_taken,
    input logic                             branch_notif_use_upct,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   branch_notif_updated_pred_info,
    input logic                             branch_notif_pred_lru,
    input logic [31:0]                      branch_notif_start_PC,
    input logic [31:0]                      branch_notif_target_PC,

    // branch notification backpressure from ROB
    output logic                            branch_notif_ready,

    // LDU misprediction notification to ROB
    input logic                         ldu_mispred_notif_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_mispred_notif_ROB_index,

    // LDU misprediction notification backpressure from ROB
    output logic                        ldu_mispred_notif_ready,

    // fence restart notification to ROB
    input logic                         fence_restart_notif_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   fence_restart_notif_ROB_index,

    // fence restart notification backpressure from ROB
    output logic                        fence_restart_notif_ready,

    // LDU exception to ROB
    input logic                         ldu_exception_valid,
    input logic [VA_WIDTH-1:0]          ldu_exception_VA,
    input logic                         ldu_exception_page_fault,
    input logic                         ldu_exception_access_fault,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_exception_ROB_index,

    // LDU exception backpressure from ROB
    output logic                        ldu_exception_ready,

    // STAMOFU exception to ROB
    input logic                         stamofu_exception_valid,
    input logic [VA_WIDTH-1:0]          stamofu_exception_VA,
    input logic                         stamofu_exception_is_lr,
    input logic                         stamofu_exception_page_fault,
    input logic                         stamofu_exception_access_fault,
    input logic                         stamofu_exception_misaligned_exception,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_exception_ROB_index,

    // STAMOFU exception backpressure from ROB
    output logic                        stamofu_exception_ready,

    // mdp update to ROB
    input logic                         ssu_mdp_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   ssu_mdp_update_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   ssu_mdp_update_ROB_index,

    // mdp update feedback from ROB
    output logic                        ssu_mdp_update_ready,

    // mdpt update to fetch unit
    output logic                        fetch_unit_mdpt_update_valid,
    output logic [31:0]                 fetch_unit_mdpt_update_start_full_PC,
    output logic [ASID_WIDTH-1:0]       fetch_unit_mdpt_update_ASID,
    output logic [MDPT_INFO_WIDTH-1:0]  fetch_unit_mdpt_update_mdp_info,

    // ROB commit
    output logic [LOG_ROB_ENTRIES-3:0]  rob_commit_upper_index,
    output logic [3:0]                  rob_commit_lower_index_valid_mask,

    // restart from ROB
    output logic                    rob_restart_valid,
    output logic [31:0]             rob_restart_PC,
    output logic [ASID_WIDTH-1:0]   rob_restart_ASID,
    output logic [1:0]              rob_restart_exec_mode,
    output logic                    rob_restart_virtual_mode,
    output logic                    rob_restart_MXR,
    output logic                    rob_restart_SUM,
    output logic                    rob_restart_trap_sfence,
    output logic                    rob_restart_trap_wfi,
    output logic                    rob_restart_trap_sret,

    // ROB kill
    output logic                        rob_kill_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_kill_abs_head_index, // must also always be true head index
    output logic [LOG_ROB_ENTRIES-1:0]  rob_kill_rel_kill_younger_index,

    // branch update from ROB
    output logic                                rob_branch_update_valid,
    output logic                                rob_branch_update_has_checkpoint,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0]   rob_branch_update_checkpoint_index,
    output logic                                rob_branch_update_is_mispredict,
    output logic                                rob_branch_update_is_taken,
    output logic                                rob_branch_update_use_upct,
    output logic [BTB_PRED_INFO_WIDTH-1:0]      rob_branch_update_intermediate_pred_info,
    output logic                                rob_branch_update_pred_lru,
    output logic [31:0]                         rob_branch_update_start_PC,
    output logic [31:0]                         rob_branch_update_target_PC,

    // ROB control of rename
    output logic                             	rob_controlling_rename,

    output logic                                rob_checkpoint_map_table_restore_valid,
    output logic [CHECKPOINT_INDEX_WIDTH-1:0]   rob_checkpoint_map_table_restore_index,

    output logic                                rob_checkpoint_clear_valid,
    output logic [CHECKPOINT_INDEX_WIDTH-1:0]   rob_checkpoint_clear_index,

    output logic [3:0]                          rob_map_table_write_valid_by_port,
    output logic [3:0][LOG_AR_COUNT-1:0]        rob_map_table_write_AR_by_port,
    output logic [3:0][LOG_PR_COUNT-1:0]        rob_map_table_write_PR_by_port,

	// ROB physical register freeing
	output logic [3:0]						rob_PR_free_req_valid_by_bank,
	output logic [3:0][LOG_PR_COUNT-1:0]	rob_PR_free_req_PR_by_bank,
	input logic [3:0]                       rob_PR_free_resp_ack_by_bank
);

    // on restart
        // can treat early and late restart the same
        // restore oldest checkpoint younger than restart if exists
            // technically can choose closest checkpoint, but this is probably not worth it to determine
                // can select smaller of (restart point - oldest younger) vs. (restart point - youngest older)
        // then take control of map table to finish off rollback
            // serial rollback of 4-way entries get to desired 4-way entry
            // make changes required to get to state within desired 4-way entry 
            // this process should probably use head port since reading
                // save head for later continuing of true commit
                // keep tail where it is so that younger garbage register writes and checkpoints
                // can get cleared out when they reach the head
                // i.e. never trample over anything in the ROB, let everything get to head, including garbage
                // head commit actions are now: 
                    // good instr, commit -> free old PR
                    // bad instr, rollback -> free new PR
                    // NO MAP TABLE CHANGES HERE

    // AMOs
        // dependent instructions can be naturally stalled, restarted as-needed as long as they remain in the ROB
            // they will because they will be marked incomplete
        // essentially just means need to delay freeing of AMO write PR
            // can put in separate queue or other tracking structure which can free from when doing regular frees from ROB head
            // actually no need to delay:
                // any instruction that could want old value is already completed (and consequently committed)

    // separately track load unit completes since rely on certain LSQ conditions before can guarantee complete
        // i.e. can't use WB bus as complete
            // 1 or more of these will come in for load
        // already separately tracking completes for stamofu, bru, sysu, etc.

    // TODO: no sysu functionality for now
        // will need various notif controls to deal with exec env changes
        // will need more exception support
        // will need CSR interfaces
            // need to update CSR's for e.g. exception
            // need to read CSR's or from sysu source for relevant exec env info

    // independent processes
        // deq/rollback
        // restart
        // exception req
        // mdp update

    // ----------------------------------------------------------------
    // Signals:

    // FF arrays
        // need to PE over or multiple referenced simultaneously
    logic [ROB_ENTRIES/4-1:0]                               valid_by_4way;
    logic [ROB_ENTRIES/4-1:0]                               checkpoint_present_by_4way;
    logic [ROB_ENTRIES/4-1:0][CHECKPOINT_INDEX_WIDTH-1:0]   checkpoint_index_by_4way;

    logic [ROB_ENTRIES-1:0] WB_complete_by_entry;
    logic [ROB_ENTRIES-1:0] unit_complete_by_entry;
    logic [ROB_ENTRIES-1:0] killed_by_entry;

    logic [ROB_ENTRIES/4-1:0] wraparound_mask;

    // bulk bram array
        // need for restart, deq/rollback
    typedef struct packed {
        logic [3:0]                         valid_by_way; // need for deq/rollback
        logic [3:0]                         uncompressed_by_way; // need for deq/rollback
        logic [3:0]                         is_rename_by_way; // need for deq/rollback
        logic [3:0]                         is_ldu_by_way; // need for deq/rollback
        logic [3:0][4:0]                    dest_AR_by_way; // need for deq/rollback
        logic [3:0][LOG_PR_COUNT-1:0]       dest_old_PR_by_way; // need for deq/rollback
        logic [3:0][LOG_PR_COUNT-1:0]       dest_new_PR_by_way; // need for deq/rollback
    } bulk_bram_entry_t;

    logic                           bulk_bram_read_next_valid;
    logic [LOG_ROB_ENTRIES-2-1:0]   bulk_bram_read_next_index;
    bulk_bram_entry_t               bulk_bram_read_entry;

    logic                           bulk_bram_write_valid;
    logic [LOG_ROB_ENTRIES-2-1:0]   bulk_bram_write_index;
    bulk_bram_entry_t               bulk_bram_write_entry;

    // PC bram array
        // need for restart, mdp update
        // diff read index than bulk bram array due to mdp udpate
    logic [LOG_ROB_ENTRIES-2-1:0]   PC_bram_read_next_valid;
    logic [LOG_ROB_ENTRIES-2-1:0]   PC_bram_read_next_index;
    logic [3:0][31:0]               PC_bram_read_PC_by_way;

    logic                           PC_bram_write_valid;
    logic [LOG_ROB_ENTRIES-2-1:0]   PC_bram_write_index;
    logic [3:0][31:0]               PC_bram_write_PC_by_way;

    logic PC_bram_read_restart_control;
    
    logic [1:0] ssu_mdp_update_saved_lower_ROB_index;

    // exception reg
        // need for exception req, deq/rollback
    logic                           exception_reg_valid, next_exception_reg_valid;
    logic [LOG_ROB_ENTRIES-1:0]     exception_reg_target_index, next_exception_reg_target_index;
    logic [31:0]                    exception_reg_cause, next_exception_reg_cause;
    logic [31:0]                    exception_reg_tval, next_exception_reg_tval;

    logic [ROB_ENTRIES/4-1:0]       exception_reg_target_mask_by_4way;

    logic exception_sent;

    // FIFO pointers
    logic [LOG_ROB_ENTRIES-2-1:0] tail_ptr;
    logic [LOG_ROB_ENTRIES-2-1:0] head_ptr;

    logic [LOG_ROB_ENTRIES-2-1:0]   map_table_state_ptr, next_map_table_state_ptr;
    logic                           map_table_state_rolling_back;
    logic                           map_table_state_reversing, next_map_table_state_reversing;
    logic                           map_table_state_ptr_incr;
    logic                           map_table_state_ptr_decr;

    logic enq_perform;
    logic deq_perform;
    
    logic checkpoint_perform;

    // deq/rollback
    typedef enum logic [1:0] {
        DEQ,
        RESTART_SEND,
        CHECKPOINT_RESTORE,
        ROLLBACK
    } restart_state_t;
    
    restart_state_t restart_state, next_restart_state;

    logic                           restart_info_valid, next_restart_info_valid;
    logic [LOG_ROB_ENTRIES-1:0]     restart_info_target_index, next_restart_info_target_index;
    logic [ROB_ENTRIES/4-1:0]       restart_info_target_mask_by_4way, next_restart_info_target_mask_by_4way;
    logic                           restart_info_use_rob_PC, next_restart_info_use_rob_PC;
    logic [31:0]                    restart_info_branch_target_PC, next_restart_info_branch_target_PC;
    logic                           restart_info_is_exception, next_restart_info_is_exception;

    logic                           new_restart_valid, next_new_restart_valid;
    logic [LOG_ROB_ENTRIES-1:0]     new_restart_target_index, next_new_restart_target_index;
    logic                           new_restart_use_rob_PC, next_new_restart_use_rob_PC;
    logic [31:0]                    new_restart_branch_target_PC, next_new_restart_branch_target_PC;

    logic [ROB_ENTRIES/4-1:0]       new_restart_target_mask_by_4way;

    logic                           checkpoint_present;

    logic                           younger_checkpoint_present, next_younger_checkpoint_present;
    logic [LOG_ROB_ENTRIES-2-1:0]   oldest_younger_checkpoint_4way_index, next_oldest_younger_checkpoint_4way_index;
    logic                           older_checkpoint_present, next_older_checkpoint_present;
    logic [LOG_ROB_ENTRIES-2-1:0]   youngest_older_checkpoint_4way_index, next_youngest_older_checkpoint_4way_index;

    logic [LOG_ROB_ENTRIES-2-1:0]   selected_checkpoint_nearest_4way_index;
    logic                           selected_checkpoint_younger;

    logic [3:0] deq_launched_by_way, next_deq_launched_by_way;

    logic [3:0] deq_complete_by_way;
    logic [3:0] deq_launching_by_way;

    logic                           branch_mispred_enq_valid;
    logic [LOG_ROB_ENTRIES-1:0]     branch_mispred_enq_ROB_index;
    logic [31:0]                    branch_mispred_enq_target_PC;
    logic                           branch_mispred_enq_ready;

    logic                           branch_mispred_deq_valid;
    logic [LOG_ROB_ENTRIES-1:0]     branch_mispred_deq_ROB_index;
    logic [31:0]                    branch_mispred_deq_target_PC;
    logic                           branch_mispred_deq_ready;

    logic branch_mispred_restarting;

    logic                           ldu_mispred_enq_valid;
    logic [LOG_ROB_ENTRIES-1:0]     ldu_mispred_enq_ROB_index;
    logic                           ldu_mispred_enq_ready;

    logic                           ldu_mispred_deq_valid;
    logic [LOG_ROB_ENTRIES-1:0]     ldu_mispred_deq_ROB_index;
    logic                           ldu_mispred_deq_ready;

    logic ldu_mispred_restarting;

    logic                           fence_mispred_enq_valid;
    logic [LOG_ROB_ENTRIES-1:0]     fence_mispred_enq_ROB_index;
    logic                           fence_mispred_enq_ready;

    logic                           fence_mispred_deq_valid;
    logic [LOG_ROB_ENTRIES-1:0]     fence_mispred_deq_ROB_index;
    logic                           fence_mispred_deq_ready;

    logic fence_mispred_restarting;

    // env vars
    logic [31:0]            env_restart_PC;
    logic [ASID_WIDTH-1:0]  env_ASID;
    logic [1:0]             env_exec_mode;
    logic                   env_virtual_mode;
    logic                   env_MXR;
    logic                   env_SUM;
    logic                   env_trap_sfence;
    logic                   env_trap_wfi;
    logic                   env_trap_sret;
    logic [31:0]            env_tvec_BASE_PC;

    // reset sequence
    logic reset_rob_restart_valid;

    logic           central_rob_restart_valid;
    logic [31:0]    central_rob_restart_PC;

    // PR free queue
    logic                           PR_free_q_enq_valid;
    logic [3:0]                     PR_free_q_enq_valid_by_way;
    logic [3:0][LOG_PR_COUNT-1:0]   PR_free_q_enq_PR_by_way;
    logic                           PR_free_q_enq_ready;
    
    logic                           PR_free_q_deq_valid;
    logic [3:0]                     PR_free_q_deq_valid_by_way;
    logic [3:0][LOG_PR_COUNT-1:0]   PR_free_q_deq_PR_by_way;
    logic                           PR_free_q_deq_ready;

    logic [3:0]                     PR_free_q_deq_invalid_mask, next_PR_free_q_deq_invalid_mask;

    // ----------------------------------------------------------------
    // Logic:

    // branch notif consumer
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            rob_branch_update_valid <= 1'b0;
            rob_branch_update_has_checkpoint <= 1'b0;
            rob_branch_update_checkpoint_index <= 0;
            rob_branch_update_is_mispredict <= 1'b0;
            rob_branch_update_is_taken <= 1'b0;
            rob_branch_update_use_upct <= 1'b0;
            rob_branch_update_intermediate_pred_info <= 8'b00000000;
            rob_branch_update_pred_lru <= 1'b0;
            rob_branch_update_start_PC <= 32'h0;
            rob_branch_update_target_PC <= 32'h0;
        end
        else begin
            // want to delay this 1 cycle so it is closer to real restart if mispred
            rob_branch_update_valid <= 
                branch_notif_valid
                & branch_notif_ready
                & ~killed_by_entry[branch_notif_ROB_index];
            rob_branch_update_has_checkpoint <= checkpoint_present_by_4way[branch_notif_ROB_index[LOG_ROB_ENTRIES-1:2]];
            rob_branch_update_checkpoint_index <= checkpoint_index_by_4way[branch_notif_ROB_index[LOG_ROB_ENTRIES-1:2]];
            rob_branch_update_is_mispredict <= branch_notif_is_mispredict;
            rob_branch_update_is_taken <= branch_notif_is_taken;
            rob_branch_update_use_upct <= branch_notif_use_upct;
            rob_branch_update_intermediate_pred_info <= branch_notif_updated_pred_info;
            rob_branch_update_pred_lru <= branch_notif_pred_lru;
            rob_branch_update_start_PC <= branch_notif_start_PC;
            rob_branch_update_target_PC <= branch_notif_target_PC;
        end
    end
    always_comb begin
        branch_mispred_enq_valid = 
            branch_notif_valid
            & branch_notif_ready
            & branch_notif_is_mispredict
            & ~killed_by_entry[branch_notif_ROB_index];
        branch_mispred_enq_ROB_index = branch_notif_ROB_index;
        branch_mispred_enq_target_PC = branch_notif_target_PC;

        branch_notif_ready = branch_mispred_enq_ready;
    end
    q_fast_ready #(
        .DATA_WIDTH(LOG_ROB_ENTRIES + 32),
        .NUM_ENTRIES(ROB_MISPRED_Q_ENTRIES)
    ) BRANCH_MISPRED_Q (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(branch_mispred_enq_valid),
        .enq_data({branch_mispred_enq_ROB_index, branch_mispred_enq_target_PC}),
        .enq_ready(branch_mispred_enq_ready),
        .deq_valid(branch_mispred_deq_valid),
        .deq_data({branch_mispred_deq_ROB_index, branch_mispred_deq_target_PC}),
        .deq_ready(branch_mispred_deq_ready)
    );

    // ldu mispred notif consumer
    always_comb begin
        ldu_mispred_enq_valid = ldu_mispred_notif_valid & killed_by_entry[branch_notif_ROB_index];
        ldu_mispred_enq_ROB_index = ldu_mispred_notif_ROB_index;

        ldu_mispred_notif_ready = ldu_mispred_enq_ready;
    end
    q_fast_ready #(
        .DATA_WIDTH(LOG_ROB_ENTRIES),
        .NUM_ENTRIES(ROB_MISPRED_Q_ENTRIES)
    ) LDU_MISPRED_Q (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(ldu_mispred_enq_valid),
        .enq_data(ldu_mispred_enq_ROB_index),
        .enq_ready(ldu_mispred_enq_ready),
        .deq_valid(ldu_mispred_deq_valid),
        .deq_data(ldu_mispred_deq_ROB_index),
        .deq_ready(ldu_mispred_deq_ready)
    );

    // fence mispred notif consumer
    always_comb begin
        fence_mispred_enq_valid = fence_restart_notif_valid & killed_by_entry[branch_notif_ROB_index];
        fence_mispred_enq_ROB_index = fence_restart_notif_ROB_index;

        fence_restart_notif_ready = fence_mispred_enq_ready;
    end
    q_fast_ready #(
        .DATA_WIDTH(LOG_ROB_ENTRIES),
        .NUM_ENTRIES(ROB_MISPRED_Q_ENTRIES)
    ) FENCE_MISPRED_Q (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(fence_mispred_enq_valid),
        .enq_data(fence_mispred_enq_ROB_index),
        .enq_ready(fence_mispred_enq_ready),
        .deq_valid(fence_mispred_deq_valid),
        .deq_data(fence_mispred_deq_ROB_index),
        .deq_ready(fence_mispred_deq_ready)
    );

    // restart controller
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            new_restart_valid <= 1'b0;
            new_restart_target_index <= 0;
            new_restart_use_rob_PC <= 1'b0;
            new_restart_branch_target_PC <= 32'h00000000;
        end
        else begin
            new_restart_valid <= next_new_restart_valid;
            new_restart_target_index <= next_new_restart_target_index;
            new_restart_use_rob_PC <= next_new_restart_use_rob_PC;
            new_restart_branch_target_PC <= next_new_restart_branch_target_PC;
        end
    end
    always_comb begin

        // static priority: fence > ldu > branch

        // fence check
        if (fence_mispred_deq_valid) begin
            if (killed_by_entry[branch_mispred_deq_ROB_index]) begin
                // ack and ignore fence
                fence_mispred_deq_ready = 1'b1;
                fence_mispred_restarting = 1'b0;
            end else begin
                // use fence for restart
                fence_mispred_deq_ready = 1'b0;
                fence_mispred_restarting = 1'b1;
            end
        end else begin
            fence_mispred_deq_ready = 1'b0;
            fence_mispred_restarting = 1'b0;
        end

        // ldu check
        if (ldu_mispred_deq_valid) begin
            if (killed_by_entry[branch_mispred_deq_ROB_index]) begin
                // ack and ignore ldu
                ldu_mispred_deq_ready = 1'b1;
                ldu_mispred_restarting = 1'b0;
            end else if (~fence_mispred_restarting) begin
                // use ldu for restart
                ldu_mispred_deq_ready = 1'b1;
                ldu_mispred_restarting = 1'b1;
            end else begin
                // stall ldu
                ldu_mispred_deq_ready = 1'b0;
                ldu_mispred_restarting = 1'b0;
            end
        end else begin
            ldu_mispred_deq_ready = 1'b0;
            ldu_mispred_restarting = 1'b0;
        end

        // branch check
        if (branch_mispred_deq_valid) begin
            if (killed_by_entry[branch_mispred_deq_ROB_index]) begin
                // ack and ignore branch
                branch_mispred_deq_ready = 1'b1;
                branch_mispred_restarting = 1'b0;
            end else if (~fence_mispred_restarting & ~ldu_mispred_restarting) begin
                // use branch for restart
                branch_mispred_deq_ready = 1'b1;
                branch_mispred_restarting = 1'b1;
            end else begin
                // stall branch
                branch_mispred_deq_ready = 1'b0;
                branch_mispred_restarting = 1'b0;
            end
        end else begin
            branch_mispred_deq_ready = 1'b0;
            branch_mispred_restarting = 1'b0;
        end

        next_new_restart_valid = fence_mispred_restarting | ldu_mispred_restarting | branch_mispred_restarting;
        if (fence_mispred_restarting) begin
            next_new_restart_target_index = fence_mispred_deq_ROB_index;
            next_new_restart_use_rob_PC = 1'b1;
        end else if (ldu_mispred_restarting) begin
            next_new_restart_target_index = ldu_mispred_deq_ROB_index;
            next_new_restart_use_rob_PC = 1'b1;
        end else begin
            next_new_restart_target_index = branch_mispred_deq_ROB_index;
            next_new_restart_use_rob_PC = 1'b0;
        end
        next_new_restart_branch_target_PC = branch_mispred_deq_target_PC;
    end
    always_comb begin
        new_restart_target_mask_by_4way = {(ROB_ENTRIES/4){1'b1}} << new_restart_target_index[LOG_ROB_ENTRIES-1:2];
    end

    // exception controller
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            exception_reg_valid <= 1'b0;
            exception_reg_target_index <= 2'h0;
            exception_reg_cause <= 32'h0;
            exception_reg_tval <= 32'h0;
        end
        else begin
            exception_reg_valid <= next_exception_reg_valid;
            exception_reg_target_index <= next_exception_reg_target_index;
            exception_reg_cause <= next_exception_reg_cause;
            exception_reg_tval <= next_exception_reg_tval;
        end
    end
    always_comb begin
        next_exception_reg_valid = exception_reg_valid;
        next_exception_reg_target_index = exception_reg_target_index;
        next_exception_reg_cause = exception_reg_cause;
        next_exception_reg_tval = exception_reg_tval;
        
        // static priority of stamofu > ldu > dispatch
            // doesn't really matter, uncommon cases
        stamofu_exception_ready = 1'b1;
        ldu_exception_ready = ~stamofu_exception_valid;

        if (exception_sent) begin
            // clear exception
            next_exception_reg_valid = 1'b0;
        end
        else if (stamofu_exception_valid) begin
            // take new exception if this one older than curr
            if (
                ~exception_reg_valid
                | (
                    (stamofu_exception_ROB_index - rob_kill_abs_head_index)
                    < (exception_reg_target_index - rob_kill_abs_head_index))
            ) begin
                next_exception_reg_valid = 1'b1;
                next_exception_reg_target_index = stamofu_exception_ROB_index;
                if (stamofu_exception_is_lr) begin
                    // LR.W
                    if (stamofu_exception_page_fault) begin
                        // load page fault -> [13]
                        next_exception_reg_cause = 32'h00002000;
                    end
                    else if (stamofu_exception_access_fault) begin
                        // load access fault -> [5]
                        next_exception_reg_cause = 32'h00000020;
                    end
                    else begin
                        // load addr misaligned -> [4]
                        next_exception_reg_cause = 32'h00000010;
                    end
                end
                else begin
                    // S*, AMO*, SC.W
                    if (stamofu_exception_page_fault) begin
                        // store/amo page fault -> [15]
                        next_exception_reg_cause = 32'h00008000;
                    end
                    else if (stamofu_exception_access_fault) begin
                        // store/amo access fault -> [7]
                        next_exception_reg_cause = 32'h00000080;
                    end
                    else begin
                        // store/amo addr misaligned -> [6]
                        next_exception_reg_cause = 32'h00000040;
                    end
                end
                next_exception_reg_tval = stamofu_exception_VA;
            end
            // clear current exception if killed
            else if (exception_reg_valid & killed_by_entry[exception_reg_target_index]) begin
                next_exception_reg_valid = 1'b0;
            end
        end
        else if (ldu_exception_valid) begin
            // take new exception if this one older than curr
            if (
                ~exception_reg_valid
                | (
                    (ldu_exception_ROB_index - rob_kill_abs_head_index)
                    < (exception_reg_target_index - rob_kill_abs_head_index))
            ) begin
                next_exception_reg_valid = 1'b1;
                next_exception_reg_target_index = ldu_exception_ROB_index;
                if (ldu_exception_page_fault) begin
                    // load page fault -> [13]
                    next_exception_reg_cause = 32'h00002000;
                end
                else begin
                    // load access fault -> [5]
                    next_exception_reg_cause = 32'h00000020;
                end
                next_exception_reg_tval = ldu_exception_VA;
            end
            // clear current exception if killed
            else if (exception_reg_valid & killed_by_entry[exception_reg_target_index]) begin
                next_exception_reg_valid = 1'b0;
            end
        end
        else if (enq_perform & dispatch_exception_present) begin
            // take new exception if no curr
            if (~exception_reg_valid) begin
                next_exception_reg_valid = 1'b1;
                next_exception_reg_target_index = {tail_ptr, dispatch_exception_index};
                if (dispatch_is_page_fault) begin
                    // instr page fault -> [12]
                    next_exception_reg_cause = 32'h00001000;
                    next_exception_reg_tval = dispatch_PC_by_way[dispatch_exception_index];
                end
                else if (dispatch_is_access_fault) begin
                    // instr access fault -> [1]
                    next_exception_reg_cause = 32'h00000002;
                    next_exception_reg_tval = dispatch_PC_by_way[dispatch_exception_index];
                end
                else begin
                    // illegal instr -> [2]
                    next_exception_reg_cause = 32'h00000004;
                    next_exception_reg_tval = dispatch_illegal_instr32;
                end
            end
            // clear current exception if killed
            else if (exception_reg_valid & killed_by_entry[exception_reg_target_index]) begin
                next_exception_reg_valid = 1'b0;
            end
        end
    end
    always_comb begin
        exception_reg_target_mask_by_4way = {(ROB_ENTRIES/4){1'b1}} << exception_reg_target_index[LOG_ROB_ENTRIES-1:2];
    end

    // FF state
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_by_4way <= '0;
            checkpoint_present_by_4way <= '0;
            checkpoint_index_by_4way <= '0;
            WB_complete_by_entry <= '0;
            unit_complete_by_entry <= '0;
            killed_by_entry <= '0;
            wraparound_mask <= '1;

            head_ptr <= 0;
            tail_ptr <= 0;
        end
        else begin
            if (enq_perform) begin
                valid_by_4way[tail_ptr] <= 1'b1;
                checkpoint_present_by_4way[tail_ptr] <= dispatch_has_checkpoint;
                checkpoint_index_by_4way[tail_ptr] <= dispatch_checkpoint_index;
                
                for (int i = 0; i < 4; i++) begin
                    WB_complete_by_entry[4*tail_ptr+i] <= 1'b0;
                    unit_complete_by_entry[4*tail_ptr+i] <= 1'b0;
                    killed_by_entry[4*tail_ptr+i] <= dispatch_enq_killed;
                end

                tail_ptr <= tail_ptr + 1;
            end

            if (deq_perform) begin
                valid_by_4way[head_ptr] <= 1'b0;
                checkpoint_present_by_4way[head_ptr] <= 1'b0;

                for (int i = 0; i < 4; i++) begin
                    WB_complete_by_entry[4*head_ptr+i] <= 1'b0;
                    unit_complete_by_entry[4*head_ptr+i] <= 1'b0;
                    killed_by_entry[4*head_ptr+i] <= 1'b0;
                end

                if (~wraparound_mask[ROB_ENTRIES/4-2]) begin
                    wraparound_mask <= '1;
                end
                else begin
                    wraparound_mask <= {wraparound_mask[ROB_ENTRIES/4-2:0], 1'b0};
                end
                
                head_ptr <= head_ptr + 1;
            end

            if (rob_kill_valid) begin
                for (int entry = 0; entry < ROB_ENTRIES; entry++) begin
                    if (
                        valid_by_4way[entry[LOG_ROB_ENTRIES-1:2]]
                        & (
                            (entry - rob_kill_abs_head_index) 
                            > rob_kill_rel_kill_younger_index)
                    ) begin
                        killed_by_entry[entry] <= 1'b1;
                    end
                end
            end

            for (int i = 0; i < PRF_BANK_COUNT; i++) begin
                if (complete_bus_valid_by_bank[i]) begin
                    WB_complete_by_entry[complete_bus_ROB_index_by_bank[i]] <= 1'b1;
                end
            end

            if (ldu_complete_valid) begin
                unit_complete_by_entry[ldu_complete_ROB_index] <= 1'b1;
            end
            if (stamofu_complete_valid) begin
                unit_complete_by_entry[stamofu_complete_ROB_index] <= 1'b1;
            end
            if (branch_notif_valid) begin
                unit_complete_by_entry[branch_notif_ROB_index] <= 1'b1;
            end
        end
    end
    always_comb begin
        dispatch_ROB_index_by_way[0] = {tail_ptr, 2'h0};
        dispatch_ROB_index_by_way[1] = {tail_ptr, 2'h1};
        dispatch_ROB_index_by_way[2] = {tail_ptr, 2'h2};
        dispatch_ROB_index_by_way[3] = {tail_ptr, 2'h3};
    end

    // enq logic:
    always_comb begin
        // can't accept if has exception and stamofu or ldu trying to except this cycle
        dispatch_enq_ready = 
            ~valid_by_4way[tail_ptr]
            & ~(
                dispatch_exception_present
                & (stamofu_exception_valid | ldu_exception_valid)
            );

        enq_perform = dispatch_enq_valid & dispatch_enq_ready;
        
        bulk_bram_write_valid = enq_perform;
        bulk_bram_write_index = tail_ptr;
        bulk_bram_write_entry.valid_by_way = dispatch_valid_by_way;
        bulk_bram_write_entry.uncompressed_by_way = dispatch_uncompressed_by_way;
        bulk_bram_write_entry.is_rename_by_way = dispatch_is_rename_by_way;
        bulk_bram_write_entry.is_ldu_by_way = dispatch_attempt_ldu_dq_by_way;
        bulk_bram_write_entry.dest_AR_by_way = dispatch_dest_AR_by_way;
        bulk_bram_write_entry.dest_old_PR_by_way = dispatch_dest_old_PR_by_way;
        bulk_bram_write_entry.dest_new_PR_by_way = dispatch_dest_new_PR_by_way;

        PC_bram_write_valid = enq_perform;
        PC_bram_write_index = tail_ptr;
        PC_bram_write_PC_by_way = dispatch_PC_by_way;
    end

    // checkpoint selector
    always_comb begin
        checkpoint_present = |checkpoint_present_by_4way;
    end
    oldest_younger #(
        .VECTOR_WIDTH(ROB_ENTRIES/4)
    ) OLDEST_YOUNGER_CHECKPOINT (
        .req_vec(checkpoint_present_by_4way),
        .head_index(head_ptr),
        .head_mask(wraparound_mask),
        .target_index(restart_info_target_index[LOG_ROB_ENTRIES-1:2]),
        .target_mask(restart_info_target_mask_by_4way),
        .younger_present(next_younger_checkpoint_present),
        .oldest_younger_index(next_oldest_younger_checkpoint_4way_index)
    );
    youngest_older #(
        .VECTOR_WIDTH(ROB_ENTRIES/4)
    ) YOUNGEST_OLDER_CHECKPOINT (
        .req_vec(checkpoint_present_by_4way),
        .head_index(head_ptr),
        .head_mask(wraparound_mask),
        .target_index(restart_info_target_index[LOG_ROB_ENTRIES-1:2]),
        .target_mask(restart_info_target_mask_by_4way),
        .older_present(next_older_checkpoint_present),
        .youngest_older_index(next_youngest_older_checkpoint_4way_index)
    );
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            younger_checkpoint_present <= 1'b0;
            oldest_younger_checkpoint_4way_index <= 0;
            older_checkpoint_present <= 1'b0;
            youngest_older_checkpoint_4way_index <= 0;
        end
        else begin
            younger_checkpoint_present <= next_younger_checkpoint_present;
            oldest_younger_checkpoint_4way_index <= next_oldest_younger_checkpoint_4way_index;
            older_checkpoint_present <= next_older_checkpoint_present;
            youngest_older_checkpoint_4way_index <= next_youngest_older_checkpoint_4way_index;
        end
    end
    always_comb begin
        // if have younger and older, pick closest
        if (younger_checkpoint_present & older_checkpoint_present) begin
            if (
                (oldest_younger_checkpoint_4way_index - restart_info_target_index[LOG_ROB_ENTRIES-1:2])
                <
                (youngest_older_checkpoint_4way_index - restart_info_target_index[LOG_ROB_ENTRIES-1:2])
            ) begin
                // younger closer
                selected_checkpoint_nearest_4way_index = oldest_younger_checkpoint_4way_index;
                // mark younger only if not exactly target (map table needs to redo mapping if exactly target)
                selected_checkpoint_younger = oldest_younger_checkpoint_4way_index != restart_info_target_index[LOG_ROB_ENTRIES-1:2];
            end
            else begin
                // older closer
                selected_checkpoint_nearest_4way_index = youngest_older_checkpoint_4way_index;
                selected_checkpoint_younger = 1'b0;
            end
        end
        else if (younger_checkpoint_present) begin
            selected_checkpoint_nearest_4way_index = oldest_younger_checkpoint_4way_index;
            // mark younger only if not exactly target (map table needs to redo mapping if exactly target)
            selected_checkpoint_younger = oldest_younger_checkpoint_4way_index != restart_info_target_index[LOG_ROB_ENTRIES-1:2];
        end
        // inferred that older checkpoint present
        else begin
            selected_checkpoint_nearest_4way_index = youngest_older_checkpoint_4way_index;
            selected_checkpoint_younger = 1'b0;
        end
    end

    // deq/rollback logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            map_table_state_ptr <= 0;
            map_table_state_reversing <= 1'b0;

            restart_state <= DEQ;

            restart_info_valid <= 1'b0;
            restart_info_target_index <= 0;
            restart_info_target_mask_by_4way <= '1;
            restart_info_use_rob_PC <= 1'b1;
            restart_info_branch_target_PC <= 32'h00000000;
            restart_info_is_exception <= 1'b0;

            deq_launched_by_way <= 4'b0000;
            reset_rob_restart_valid <= ROB_RESTART_ON_RESET;
        end
        else begin
            map_table_state_ptr <= next_map_table_state_ptr;
            map_table_state_reversing <= next_map_table_state_reversing;

            restart_state <= next_restart_state;

            restart_info_valid <= next_restart_info_valid;
            restart_info_target_index <= next_restart_info_target_index;
            restart_info_target_mask_by_4way <= next_restart_info_target_mask_by_4way;
            restart_info_use_rob_PC <= next_restart_info_use_rob_PC;
            restart_info_branch_target_PC <= next_restart_info_branch_target_PC;
            restart_info_is_exception <= next_restart_info_is_exception;

            deq_launched_by_way <= next_deq_launched_by_way;
            reset_rob_restart_valid <= 1'b0;
        end
    end
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            // ldu needs unit complete
            // else, WB complete or unit complete
            deq_complete_by_way[i] = 
                (~bulk_bram_read_entry.is_ldu_by_way[i] & WB_complete_by_entry[4*head_ptr+i])
                | unit_complete_by_entry[4*head_ptr+i];
        end
    end
    always_comb begin
        if (checkpoint_perform) begin
            next_map_table_state_ptr = selected_checkpoint_nearest_4way_index;
            next_map_table_state_reversing = selected_checkpoint_younger; // reverse if checkpoint younger
        end
        else if (enq_perform) begin
            next_map_table_state_ptr = tail_ptr + 1;
            next_map_table_state_reversing = 1'b1; // reverse from late enq
        end
        else if (map_table_state_ptr_incr) begin
            next_map_table_state_ptr = map_table_state_ptr + 1;
            next_map_table_state_reversing = 1'b0; // maintain reversing
        end
        else if (map_table_state_ptr_decr) begin
            next_map_table_state_ptr = map_table_state_ptr - 1;
            next_map_table_state_reversing = 1'b1; // maintain not reversing
        end
        else begin
            next_map_table_state_ptr = map_table_state_ptr;
            next_map_table_state_reversing = 1'b1; // reverse on no checkpoint
        end
    end
    always_comb begin
        rob_commit_upper_index = head_ptr;
        rob_commit_lower_index_valid_mask = deq_launching_by_way;

        rob_restart_valid = reset_rob_restart_valid | central_rob_restart_valid;
        if (reset_rob_restart_valid) begin
            rob_restart_PC = env_restart_PC;
        end else begin
            rob_restart_PC = central_rob_restart_PC;
        end
        // mess with these when add csrf
        rob_restart_ASID = env_ASID;
        rob_restart_exec_mode = env_exec_mode;
        rob_restart_virtual_mode = env_virtual_mode;
        rob_restart_MXR = env_MXR;
        rob_restart_SUM = env_SUM;
        rob_restart_trap_sfence = env_trap_sfence;
        rob_restart_trap_wfi = env_trap_wfi;
        rob_restart_trap_sret = env_trap_sret;

        rob_kill_abs_head_index = {head_ptr, 2'h0};

        rob_map_table_write_AR_by_port = {
            bulk_bram_read_entry.dest_AR_by_way[3],
            bulk_bram_read_entry.dest_AR_by_way[2],
            bulk_bram_read_entry.dest_AR_by_way[1],
            bulk_bram_read_entry.dest_AR_by_way[0]
        };
        // map table writes:
            // undo mapping for target if exception, else don't undo target index
            // need to know if reversing to know which sub-entry mappings to undo vs. redo
        if (map_table_state_rolling_back) begin
            rob_map_table_write_valid_by_port = bulk_bram_read_entry.valid_by_way & bulk_bram_read_entry.is_rename_by_way;
        end
        else begin
            rob_map_table_write_valid_by_port = 4'b0000;
        end
        if (map_table_state_ptr == restart_info_target_index[LOG_ROB_ENTRIES-1:2]) begin
            if (map_table_state_reversing) begin
                if (restart_info_is_exception) begin
                    // undo all younger and self
                    case (restart_info_target_index[1:0])
                        2'h0:   rob_map_table_write_valid_by_port &= 4'b1111;
                        2'h1:   rob_map_table_write_valid_by_port &= 4'b1110;
                        2'h2:   rob_map_table_write_valid_by_port &= 4'b1100;
                        2'h3:   rob_map_table_write_valid_by_port &= 4'b1000;
                    endcase
                end
                else begin
                    // undo all younger
                    case (restart_info_target_index[1:0])
                        2'h0:   rob_map_table_write_valid_by_port &= 4'b1110;
                        2'h1:   rob_map_table_write_valid_by_port &= 4'b1100;
                        2'h2:   rob_map_table_write_valid_by_port &= 4'b1000;
                        2'h3:   rob_map_table_write_valid_by_port &= 4'b0000;
                    endcase
                end
            end
            else begin
                if (restart_info_is_exception) begin
                    // redo all older
                    case (restart_info_target_index[1:0])
                        2'h0:   rob_map_table_write_valid_by_port &= 4'b0000;
                        2'h1:   rob_map_table_write_valid_by_port &= 4'b0001;
                        2'h2:   rob_map_table_write_valid_by_port &= 4'b0011;
                        2'h3:   rob_map_table_write_valid_by_port &= 4'b0111;
                    endcase
                end
                else begin
                    // redo all older and self
                    case (restart_info_target_index[1:0])
                        2'h0:   rob_map_table_write_valid_by_port &= 4'b0001;
                        2'h1:   rob_map_table_write_valid_by_port &= 4'b0011;
                        2'h2:   rob_map_table_write_valid_by_port &= 4'b0111;
                        2'h3:   rob_map_table_write_valid_by_port &= 4'b1111;
                    endcase
                end
            end
        end
        // map table old vs new PR based on if reversing
        if (map_table_state_reversing) begin
            rob_map_table_write_PR_by_port = bulk_bram_read_entry.dest_old_PR_by_way;
        end
        else begin
            rob_map_table_write_PR_by_port = bulk_bram_read_entry.dest_new_PR_by_way;
        end
    end
    always_comb begin
        // state machine
            // read bulk @ head ptr on transitions to DEQ for AR, PR info
            // read bulk and PC @ restart index on transition to RESTART_SEND for restart PC info
            // read bulk @ arch state ptr on transitions to ROLLBACK for AR, PR info
        case (restart_state)

            RESTART_SEND:
            begin
                // send restart no matter what
                rob_controlling_rename = 1'b1;
                exception_sent = 1'b0; // send this when done rollback
                map_table_state_rolling_back = 1'b0; // send on rollback's
                map_table_state_ptr_incr = 1'b0; // send on rollback's
                map_table_state_ptr_decr = 1'b0; // send on rollback's
                deq_perform = 1'b0;
                checkpoint_perform = 1'b0;
                next_deq_launched_by_way = deq_launched_by_way; // save DEQ progress
                deq_launching_by_way = 4'b0000;
                central_rob_restart_valid = 1'b1;
                // restart PC selection
                // exception restart -> handler addr
                    // TODO: switch to mtvec/stvec functionality
                if (restart_info_is_exception) begin
                    central_rob_restart_PC = env_tvec_BASE_PC;
                end
                // general restart -> next PC
                // fence, ldu restart -> rob PC + 4/2
                else if (restart_info_use_rob_PC) begin
                    // uncompressed -> PC + 4
                    if (bulk_bram_read_entry.uncompressed_by_way[restart_info_target_index[1:0]]) begin
                        central_rob_restart_PC = PC_bram_read_PC_by_way[restart_info_target_index[1:0]] + 32'h4;
                    end
                    // compressed -> PC + 2
                    else begin
                        central_rob_restart_PC = PC_bram_read_PC_by_way[restart_info_target_index[1:0]] + 32'h2;
                    end
                end
                // branch restart -> given branch target PC
                else begin
                    central_rob_restart_PC = restart_info_branch_target_PC;
                end
                rob_kill_valid = 1'b1;
                rob_kill_rel_kill_younger_index = restart_info_target_index - rob_kill_abs_head_index;
                rob_checkpoint_map_table_restore_valid = 1'b0;
                rob_checkpoint_map_table_restore_index = checkpoint_index_by_4way[selected_checkpoint_nearest_4way_index];
                rob_checkpoint_clear_valid = 1'b0;
                rob_checkpoint_clear_index = checkpoint_index_by_4way[head_ptr];

                // check for new older restart if not doing exception and no older exception
                if (
                    ~restart_info_is_exception
                    & new_restart_valid
                    & (
                        (new_restart_target_index - rob_kill_abs_head_index)
                        <
                        (restart_info_target_index - rob_kill_abs_head_index)
                    )
                    & (
                        ~exception_reg_valid
                        | (
                            (new_restart_target_index - rob_kill_abs_head_index)
                            <
                            (exception_reg_target_index - rob_kill_abs_head_index)
                        )
                    )
                ) begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = new_restart_target_index[LOG_ROB_ENTRIES-1:2];
                    PC_bram_read_restart_control = 1'b1;
                    next_restart_state = RESTART_SEND;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = new_restart_target_index;
                    next_restart_info_target_mask_by_4way = new_restart_target_mask_by_4way;
                    next_restart_info_use_rob_PC = new_restart_use_rob_PC;
                    next_restart_info_branch_target_PC = new_restart_branch_target_PC;
                    next_restart_info_is_exception = 1'b0;
                end
                // otherwise, check for checkpoint:
                else if (checkpoint_present) begin
                    bulk_bram_read_next_valid = 1'b0; // start read next cycle
                    bulk_bram_read_next_index = new_restart_target_index[LOG_ROB_ENTRIES-1:2];;
                    PC_bram_read_restart_control = 1'b0;
                    next_restart_state = CHECKPOINT_RESTORE;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = restart_info_target_index;
                    next_restart_info_target_mask_by_4way = restart_info_target_mask_by_4way;
                    next_restart_info_use_rob_PC = restart_info_use_rob_PC;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = restart_info_is_exception;
                end
                // otherwise, continue to rollback
                else begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = next_map_table_state_ptr;
                    PC_bram_read_restart_control = 1'b0;
                    next_restart_state = CHECKPOINT_RESTORE;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = restart_info_target_index;
                    next_restart_info_target_mask_by_4way = restart_info_target_mask_by_4way;
                    next_restart_info_use_rob_PC = restart_info_use_rob_PC;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = restart_info_is_exception;
                end
            end

            CHECKPOINT_RESTORE:
            begin
                // perform checkpoint restore no matter what
                rob_controlling_rename = 1'b1;
                exception_sent = 1'b0; // send this when done rollback
                map_table_state_rolling_back = 1'b0; // send on rollback's
                map_table_state_ptr_incr = 1'b0; // send on rollback's
                map_table_state_ptr_decr = 1'b0; // send on rollback's
                deq_perform = 1'b0;
                checkpoint_perform = 1'b1;
                next_deq_launched_by_way = deq_launched_by_way; // save DEQ progress
                deq_launching_by_way = 4'b0000;
                central_rob_restart_valid = 1'b0;
                central_rob_restart_PC = restart_info_branch_target_PC;
                rob_kill_valid = 1'b0;
                rob_kill_rel_kill_younger_index = restart_info_target_index - rob_kill_abs_head_index;
                rob_checkpoint_map_table_restore_valid = 1'b1;
                rob_checkpoint_map_table_restore_index = checkpoint_index_by_4way[selected_checkpoint_nearest_4way_index];
                rob_checkpoint_clear_valid = 1'b0;
                rob_checkpoint_clear_index = checkpoint_index_by_4way[head_ptr];

                // check for new older restart if not doing exception and no older exception
                if (
                    ~restart_info_is_exception
                    & new_restart_valid
                    & (
                        (new_restart_target_index - rob_kill_abs_head_index)
                        <
                        (restart_info_target_index - rob_kill_abs_head_index)
                    )
                    & (
                        ~exception_reg_valid
                        | (
                            (new_restart_target_index - rob_kill_abs_head_index)
                            <
                            (exception_reg_target_index - rob_kill_abs_head_index)
                        )
                    )
                ) begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = new_restart_target_index[LOG_ROB_ENTRIES-1:2];
                    PC_bram_read_restart_control = 1'b1;
                    next_restart_state = RESTART_SEND;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = new_restart_target_index;
                    next_restart_info_target_mask_by_4way = new_restart_target_mask_by_4way;
                    next_restart_info_use_rob_PC = new_restart_use_rob_PC;
                    next_restart_info_branch_target_PC = new_restart_branch_target_PC;
                    next_restart_info_is_exception = 1'b0;
                end
                // otherwise, continue rollback
                else begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = next_map_table_state_ptr;
                    PC_bram_read_restart_control = 1'b0;
                    next_restart_state = ROLLBACK;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = restart_info_target_index;
                    next_restart_info_target_mask_by_4way = restart_info_target_mask_by_4way;
                    next_restart_info_use_rob_PC = restart_info_use_rob_PC;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = restart_info_is_exception;
                end
            end

            ROLLBACK:
            begin
                // perform rollback no matter what
                rob_controlling_rename = 1'b1;
                map_table_state_rolling_back = 1'b1;
                map_table_state_ptr_incr = ~map_table_state_reversing;
                map_table_state_ptr_decr = map_table_state_reversing;
                deq_perform = 1'b0;
                checkpoint_perform = 1'b0;
                next_deq_launched_by_way = deq_launched_by_way; // save DEQ progress
                deq_launching_by_way = 4'b0000;
                central_rob_restart_valid = 1'b0;
                central_rob_restart_PC = restart_info_branch_target_PC;
                rob_kill_valid = 1'b0;
                rob_kill_rel_kill_younger_index = restart_info_target_index - rob_kill_abs_head_index;
                rob_checkpoint_map_table_restore_valid = 1'b0;
                rob_checkpoint_map_table_restore_index = checkpoint_index_by_4way[selected_checkpoint_nearest_4way_index];
                rob_checkpoint_clear_valid = 1'b0;
                rob_checkpoint_clear_index = checkpoint_index_by_4way[head_ptr];

                // check for new older restart if not doing exception and no older exception
                if (
                    ~restart_info_is_exception
                    & new_restart_valid
                    & (
                        (new_restart_target_index - rob_kill_abs_head_index)
                        <
                        (restart_info_target_index - rob_kill_abs_head_index)
                    )
                    & (
                        ~exception_reg_valid
                        | (
                            (new_restart_target_index - rob_kill_abs_head_index)
                            <
                            (exception_reg_target_index - rob_kill_abs_head_index)
                        )
                    )
                ) begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = new_restart_target_index[LOG_ROB_ENTRIES-1:2];
                    PC_bram_read_restart_control = 1'b1;
                    exception_sent = 1'b0;
                    next_restart_state = RESTART_SEND;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = new_restart_target_index;
                    next_restart_info_target_mask_by_4way = new_restart_target_mask_by_4way;
                    next_restart_info_use_rob_PC = new_restart_use_rob_PC;
                    next_restart_info_branch_target_PC = new_restart_branch_target_PC;
                    next_restart_info_is_exception = 1'b0;
                end
                // otherwise, check for rollback arrival
                    // double check no enq, which will mess up map table state
                    // automatically arrived if matching ptr and target 4way index
                else if (
                    ~enq_perform
                    & map_table_state_ptr == restart_info_target_index[LOG_ROB_ENTRIES-1:2]
                ) begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = head_ptr + 1;
                    PC_bram_read_restart_control = 1'b0;
                    exception_sent = restart_info_is_exception;
                    next_restart_state = DEQ;
                    next_restart_info_valid = 1'b0;
                    next_restart_info_target_index = restart_info_target_index;
                    next_restart_info_target_mask_by_4way = restart_info_target_mask_by_4way;
                    next_restart_info_use_rob_PC = restart_info_use_rob_PC;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = restart_info_is_exception;
                end
                // otherwise, continue rollback
                else begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = next_map_table_state_ptr;
                    PC_bram_read_restart_control = 1'b0;
                    exception_sent = 1'b0;
                    next_restart_state = ROLLBACK;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = restart_info_target_index;
                    next_restart_info_target_mask_by_4way = restart_info_target_mask_by_4way;
                    next_restart_info_use_rob_PC = restart_info_use_rob_PC;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = restart_info_is_exception;
                end
            end
            
            default: // DEQ
            begin
                rob_controlling_rename = 1'b0;
                exception_sent = 1'b0; // send this when done rollback
                map_table_state_rolling_back = 1'b0; // send on rollback's
                map_table_state_ptr_incr = 1'b0; // send on rollback's
                map_table_state_ptr_decr = 1'b0; // send on rollback's
                checkpoint_perform = 1'b0;
                central_rob_restart_valid = 1'b0;
                central_rob_restart_PC = restart_info_branch_target_PC;
                rob_kill_valid = 1'b0;
                rob_kill_rel_kill_younger_index = restart_info_target_index - rob_kill_abs_head_index;
                rob_checkpoint_map_table_restore_valid = 1'b0;
                rob_checkpoint_map_table_restore_index = checkpoint_index_by_4way[selected_checkpoint_nearest_4way_index];
                rob_checkpoint_clear_index = checkpoint_index_by_4way[head_ptr];

                // check for exception to take now
                    // deq'd everything older than excepting instr
                if (
                    exception_reg_valid
                    & (exception_reg_target_index[LOG_ROB_ENTRIES-1:2] == head_ptr)
                    & (
                        ((exception_reg_target_index[1:0] == 2'h0) & (deq_launched_by_way == 4'b0000))
                        | ((exception_reg_target_index[1:0] == 2'h1) & (deq_launched_by_way == 4'b0001))
                        | ((exception_reg_target_index[1:0] == 2'h2) & (deq_launched_by_way == 4'b0011))
                        | ((exception_reg_target_index[1:0] == 2'h3) & (deq_launched_by_way == 4'b0111))
                    )
                ) begin
                    bulk_bram_read_next_valid = 1'b0;
                    bulk_bram_read_next_index = exception_reg_target_index[LOG_ROB_ENTRIES-1:2];
                    PC_bram_read_restart_control = 1'b1;
                    next_restart_state = RESTART_SEND;
                    deq_perform = 1'b0;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = exception_reg_target_index;
                    next_restart_info_target_mask_by_4way = exception_reg_target_mask_by_4way;
                    next_restart_info_use_rob_PC = 1'b1;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = 1'b1;
                    next_deq_launched_by_way = deq_launched_by_way;
                    deq_launching_by_way = 4'b0000;
                    rob_checkpoint_clear_valid = 1'b0;
                end
                // otherwise, check for new restart if no older exception
                else if (
                    new_restart_valid
                    & (
                        ~exception_reg_valid
                        | (
                            (new_restart_target_index - rob_kill_abs_head_index)
                            <
                            (exception_reg_target_index - rob_kill_abs_head_index)
                        )
                    )
                ) begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = new_restart_target_index[LOG_ROB_ENTRIES-1:2];
                    PC_bram_read_restart_control = 1'b1;
                    next_restart_state = RESTART_SEND;
                    deq_perform = 1'b0;
                    next_restart_info_valid = 1'b1;
                    next_restart_info_target_index = new_restart_target_index;
                    next_restart_info_target_mask_by_4way = new_restart_target_mask_by_4way;
                    next_restart_info_use_rob_PC = new_restart_use_rob_PC;
                    next_restart_info_branch_target_PC = new_restart_branch_target_PC;
                    next_restart_info_is_exception = 1'b0;
                    next_deq_launched_by_way = deq_launched_by_way;
                    deq_launching_by_way = 4'b0000;
                    rob_checkpoint_clear_valid = 1'b0;
                end
                // otherwise, check for full deq
                    // 4way entry valid
                    // all sub-entries invalid or complete
                else if (
                    valid_by_4way[head_ptr]
                    & &(~bulk_bram_read_entry.valid_by_way | deq_complete_by_way)
                    & PR_free_q_enq_ready
                ) begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = head_ptr + 1; // incr with head
                    PC_bram_read_restart_control = 1'b0;
                    next_restart_state = DEQ;
                    deq_perform = 1'b1;
                    next_restart_info_valid = 1'b0;
                    next_restart_info_target_index = restart_info_target_index;
                    next_restart_info_target_mask_by_4way = restart_info_target_mask_by_4way;
                    next_restart_info_use_rob_PC = restart_info_use_rob_PC;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = restart_info_is_exception;
                    next_deq_launched_by_way = 4'b0000; // reset sub-entry launch state
                    deq_launching_by_way = ~deq_launched_by_way & bulk_bram_read_entry.valid_by_way; // launch remaining sub-entries
                    rob_checkpoint_clear_valid = checkpoint_present_by_4way[head_ptr];
                end
                // otherwise, check for partial/no deq
                else begin
                    bulk_bram_read_next_valid = 1'b1;
                    bulk_bram_read_next_index = head_ptr; // stay at head
                    PC_bram_read_restart_control = 1'b0;
                    next_restart_state = DEQ;
                    deq_perform = 1'b0;
                    next_restart_info_valid = 1'b0;
                    next_restart_info_target_index = restart_info_target_index;
                    next_restart_info_target_mask_by_4way = restart_info_target_mask_by_4way;
                    next_restart_info_use_rob_PC = restart_info_use_rob_PC;
                    next_restart_info_branch_target_PC = restart_info_branch_target_PC;
                    next_restart_info_is_exception = restart_info_is_exception;
                    // lowest 3 invalid or complete
                    if (
                        valid_by_4way[head_ptr]
                        & &(~bulk_bram_read_entry.valid_by_way[2:0] | deq_complete_by_way[2:0])
                    ) begin
                        deq_launching_by_way[3] = 1'b0;
                        deq_launching_by_way[2:0] = deq_complete_by_way[2:0] & ~deq_launched_by_way[2:0];
                    end
                    // lowest 2 invalid or complete
                    else if (
                        valid_by_4way[head_ptr]
                        & &(~bulk_bram_read_entry.valid_by_way[1:0] | deq_complete_by_way[1:0])
                    ) begin
                        deq_launching_by_way[3:2] = 2'b00;
                        deq_launching_by_way[1:0] = deq_complete_by_way[1:0] & ~deq_launched_by_way[1:0];
                    end
                    // lowest 1 invalid or complete
                    else if (
                        valid_by_4way[head_ptr]
                        & (~bulk_bram_read_entry.valid_by_way[0] | deq_complete_by_way[0])
                    ) begin
                        deq_launching_by_way[3:1] = 3'b000;
                        deq_launching_by_way[0] = deq_complete_by_way[0] & ~deq_launched_by_way[0];
                    end
                    else begin
                        deq_launching_by_way = 4'b0000;
                    end
                    next_deq_launched_by_way = deq_launched_by_way | deq_launching_by_way;
                    rob_checkpoint_clear_valid = 1'b0;
                end
            end
        endcase
    end

    // PC bram logic:
    always_comb begin
        ssu_mdp_update_ready = ~PC_bram_read_restart_control;

        PC_bram_read_next_valid = PC_bram_read_restart_control | ssu_mdp_update_valid;

        if (PC_bram_read_restart_control) begin
            // rob state machine control
            PC_bram_read_next_index = new_restart_target_index[LOG_ROB_ENTRIES-1:2];
        end
        else begin
            // ssu control
            PC_bram_read_next_index = ssu_mdp_update_ROB_index[LOG_ROB_ENTRIES-1:2];
        end
    end

    // ssu mdp update
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_unit_mdpt_update_valid <= 1'b0;
            fetch_unit_mdpt_update_ASID <= 'h0;
            fetch_unit_mdpt_update_mdp_info <= 'h0;

            ssu_mdp_update_saved_lower_ROB_index <= 2'h0;
        end
        else begin
            fetch_unit_mdpt_update_valid <= ssu_mdp_update_valid & ssu_mdp_update_ready;
            fetch_unit_mdpt_update_ASID <= env_ASID;
            fetch_unit_mdpt_update_mdp_info <= ssu_mdp_update_mdp_info;

            ssu_mdp_update_saved_lower_ROB_index <= ssu_mdp_update_ROB_index[1:0];
        end
    end
    always_comb begin
        fetch_unit_mdpt_update_start_full_PC = PC_bram_read_PC_by_way[ssu_mdp_update_saved_lower_ROB_index];
    end

    // PR free queue
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            PR_free_q_deq_invalid_mask <= 4'b0000;
        end
        else begin
            PR_free_q_deq_invalid_mask <= next_PR_free_q_deq_invalid_mask;
        end
    end
    always_comb begin
        PR_free_q_enq_valid = deq_perform;
        PR_free_q_enq_valid_by_way = bulk_bram_read_entry.valid_by_way & bulk_bram_read_entry.is_rename_by_way;
        for (int way = 0; way < 4; way++) begin
            if (killed_by_entry[{head_ptr, way}]) begin
                // if killed, free new
                PR_free_q_enq_PR_by_way[way] = bulk_bram_read_entry.dest_new_PR_by_way[way];
            end else begin
                // if not killed, free old
                PR_free_q_enq_PR_by_way[way] = bulk_bram_read_entry.dest_old_PR_by_way[way];
            end
        end

        rob_PR_free_req_valid_by_bank = 
            {4{PR_free_q_deq_valid}}
            & PR_free_q_deq_valid_by_way
            & ~PR_free_q_deq_invalid_mask;
        rob_PR_free_req_PR_by_bank = PR_free_q_deq_PR_by_way;
        PR_free_q_deq_ready = &(
            ~PR_free_q_deq_valid_by_way
            | PR_free_q_deq_invalid_mask
            | rob_PR_free_resp_ack_by_bank
        );

        if (PR_free_q_deq_valid & PR_free_q_deq_ready) begin
            // reset invalid mask on successful deq
            next_PR_free_q_deq_invalid_mask = 4'b0000; 
        end
        else begin
            // accumulate freed PR's into invalid mask
            next_PR_free_q_deq_invalid_mask = PR_free_q_deq_invalid_mask | rob_PR_free_resp_ack_by_bank;
        end
    end
    q_fast_ready #(
        .DATA_WIDTH(4*(1+LOG_PR_COUNT)),
        .NUM_ENTRIES(ROB_PR_FREE_Q_ENTRIES)
    ) PR_FREE_Q (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(PR_free_q_enq_valid),
        .enq_data({PR_free_q_enq_valid_by_way, PR_free_q_enq_PR_by_way}),
        .enq_ready(PR_free_q_enq_ready),
        .deq_valid(PR_free_q_deq_valid),
        .deq_data({PR_free_q_deq_valid_by_way, PR_free_q_deq_PR_by_way}),
        .deq_ready(PR_free_q_deq_ready)
    );

    // env vars
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            env_restart_PC <= INIT_PC; // can mess with this for trap handling
            env_ASID <= INIT_ASID;
            env_exec_mode <= INIT_EXEC_MODE;
            env_virtual_mode <= INIT_VIRTUAL_MODE;
            env_MXR <= INIT_MXR;
            env_SUM <= INIT_SUM;
            env_trap_sfence <= INIT_TRAP_SFENCE;
            env_trap_wfi <= INIT_TRAP_WFI;
            env_trap_sret <= INIT_TRAP_SRET;
            env_tvec_BASE_PC <= INIT_TVEC_BASE_PC;
        end
        else begin
            // for now, since no csrf, these are hardwired
        end
    end

    // ----------------------------------------------------------------
    // Memory Arrays:

    bram_1rport_1wport #(
        .INNER_WIDTH((($bits(bulk_bram_entry_t)-1)/8 + 1) * 8),
        .OUTER_WIDTH(ROB_ENTRIES/4)
    ) BULK_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(bulk_bram_read_next_valid),
        .rindex(bulk_bram_read_next_index),
        .rdata(bulk_bram_read_entry),
        .wen_byte({(($bits(bulk_bram_entry_t)-1)/8 + 1){bulk_bram_write_valid}}),
        .windex(bulk_bram_write_index),
        .wdata(bulk_bram_write_entry)        
    );
    
    bram_1rport_1wport #(
        .INNER_WIDTH(4 * 32),
        .OUTER_WIDTH(ROB_ENTRIES/4)
    ) PC_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(PC_bram_read_next_valid),
        .rindex(PC_bram_read_next_index),
        .rdata(PC_bram_read_PC_by_way),
        .wen_byte({(4*32/8){PC_bram_write_valid}}),
        .windex(PC_bram_write_index),
        .wdata(PC_bram_write_PC_by_way)
    );

endmodule