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

module rob (

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

    // ROB commit
    output logic [LOG_ROB_ENTRIES-3:0]  rob_commit_upper_index,
    output logic [3:0]                  rob_commit_lower_index_valid_mask,

    // restart from ROB
    output logic            rob_restart_valid,
    output logic [31:0]     rob_restart_PC,
    output logic [1:0]      rob_restart_exec_mode,
    output logic            rob_restart_virtual_mode,
    output logic [8:0]      rob_restart_ASID,
    output logic            rob_restart_MXR,
    output logic            rob_restart_SUM,
    output logic            rob_restart_trap_sfence,
    output logic            rob_restart_trap_wfi,
    output logic            rob_restart_trap_sret,

    // ROB kill
    output logic                        rob_kill_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_kill_abs_head_index, // must also always be true head index
    output logic [LOG_ROB_ENTRIES-1:0]  rob_kill_rel_kill_younger_index,

    // branch update from ROB
    output logic                            rob_branch_update_valid,
    output logic                            rob_branch_update_has_checkpoint,
    output logic                            rob_branch_update_is_mispredict,
    output logic                            rob_branch_update_is_taken,
    output logic                            rob_branch_update_use_upct,
    output logic [BTB_PRED_INFO_WIDTH-1:0]  rob_branch_update_intermediate_pred_info,
    output logic                            rob_branch_update_pred_lru,
    output logic [31:0]                     rob_branch_update_start_PC,
    output logic [31:0]                     rob_branch_update_target_PC,

    // ROB control of rename
    output logic                                rob_controlling_rename,
    output logic                                rob_checkpoint_restore_valid,
    output logic                                rob_checkpoint_restore_clear,
    output logic [CHECKPOINT_INDEX_WIDTH-1:0]   rob_checkpoint_restore_index,
    output logic [3:0]                          rob_map_table_write_valid_by_port,
    output logic [3:0][LOG_AR_COUNT-1:0]        rob_map_table_write_AR_by_port,
    output logic [3:0][LOG_PR_COUNT-1:0]        rob_map_table_write_PR_by_port,

	// ROB physical register freeing
	output logic [3:0]						rob_PR_free_req_valid_by_bank,
	output logic [3:0][LOG_PR_COUNT-1:0]	rob_PR_free_req_PR_by_bank,
	input logic [3:0]                       rob_PR_free_resp_ack_by_bank,

    // mdp update to ROB
    input logic                         rob_mdp_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   rob_mdp_update_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_mdp_update_ROB_index
);

    // unexceptable head and true head
        // unexceptable head used to launch stores and AMO's
        // true head used to free registers and verify instruction completion
            // also safe to roll back architecture state with since know garbage value done being written
        // true head must wait for all instr's to be complete
        // unexceptable head just waits until no exception or misprediction possible for instr
            // ALU: technically don't need to wait as none are ever exceptable
            // BRU: when resolved
            // LDU: unexceptable once get dTLB resp
                // unless strict with when load marked as complete, (e.g. when no earlier stores are ambigious,
                // which means need another SQ CAM -> NO) then all loads are exceptable until the stores
                // older than them are all complete
                    // this functionality relies on stores only being marked as complete
            // STAMOFU: 
                // stores: once get dTLB resp
                    // need to make sure loads behind are restarted
                    // dTLB resp implies ldu_cq + ldu_mq CAM
                // AMO's: once get reg write
                    // dependent loads behind must wait until AMO returns so that can read updated value in dcache 
                    // heavy stall here
                // fence's: 
            // SYS: when CSR resolved

    // pretty sure just need unexceptable head, which can then be the true head
        // potential consequences
            // registers are freed earlier
                // this is good if possible
                // ALL INSTR'S MUST BE DONE WITH OLD VALUES
                    // this can be guaranteed since no isntr's older than amo which could use the old reg value are complete
            // ROB commit from head no longer means can check expected processor state for instr
                // e.g. load may eventually come in after dcache miss but value isn't there yet, may have to wait fairly arbitrary time
                // actually I don't think this will work then because loads must wait stay in LQ until value comes back
                    // wait no it's fine because loads have commit broadcasted, just delay dequeue from LQ until also have returned value
                // this is solid reason not to do this
        // "unexceptable" for this purpose then requires that operands have been read
        // since doing no instr kills in non-mem and non-sys pipelines, seems like forced to just wait for non-mem and non-sys to be fully complete before move on unexceptable head
            // maybe not since guaranteed reg write happens
    
    // solid plan for now: use true head
        // perform commit when 4-way @ head complete
            // perform free's if exist
            // clear checkpoint if exists
            // launch stamofu
                // can only do 1 per cycle
                    // repeat as needed
                        // prolly invalidating entries as go anyway so will naturally move onto the next store on the next cycle
                // AMO's not fully complete until read returned, so head stalled
                // multiple stores in 4-way and AMO's are rare case, just eat the (potential) perf hit
                    // only a perf hit if ejection rate of stores/amos/fences or ROB capacity are limiters for program
                // compromise: ROB can broadcast completion of full 4-way per cycle
                    // then up to stamofu to maintain avg bandwidth of 1/cycle commit to dcache
                // ended up being simplified in stamofu design
                    // send 4-way commits
                    // stamofu can apply all commits to associated entries at once
                    // with at least 1-cycle delay, stamofu independently launches one store/amo per cycle 

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
        // already separately tracking stamofu, bru, sys, etc.

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

    logic [LOG_ROB_ENTRIES-2-1:0] tail_ptr, next_tail_ptr;
    logic [LOG_ROB_ENTRIES-2-1:0] head_ptr, next_head_ptr;

    logic enq_perform;
    logic deq_perform;

    // FF arrays
        // need to PE over or multiple referenced simultaneously
    logic [ROB_ENTRIES/4-1:0] valid_by_4way;
    logic [ROB_ENTRIES/4-1:0] has_checkpoint_by_4way;

    logic [ROB_ENTRIES-1:0] complete_by_entry;
    logic [ROB_ENTRIES-1:0] killed_by_entry;

    // bulk bram array
    typedef struct packed {
        logic [3:0]                         valid_by_way; // need for deq/rollback
        logic [3:0]                         uncompressed_by_way; // need for deq/rollback
        logic [3:0]                         is_rename_by_way; // need for deq/rollback
        logic [3:0]                         is_ldu_by_way; // need for deq/rollback
        logic [3:0][4:0]                    dest_AR_by_way; // need for deq/rollback
        logic [3:0][LOG_PR_COUNT-1:0]       dest_old_PR_by_way; // need for deq/rollback
        logic [3:0][LOG_PR_COUNT-1:0]       dest_new_PR_by_way; // need for deq/rollback
        logic [CHECKPOINT_INDEX_WIDTH-1:0]  checkpoint_index; // need for deq/rollback, restart
    } bram_entry_t;

    logic                           bulk_bram_read_valid;
    logic [LOG_ROB_ENTRIES-2-1:0]   bulk_bram_read_index;
    bram_entry_t                    bulk_bram_read_entry;

    logic                           bulk_bram_write_valid;
    logic [LOG_ROB_ENTRIES-2-1:0]   bulk_bram_write_index;
    bram_entry_t                    bulk_bram_write_entry;

    // PC bram array
        // need for restart, mdp update
        // diff read index than bulk bram array due to mdp udpate
    logic [LOG_ROB_ENTRIES-2-1:0]   PC_bram_read_index;
    logic [3:0][31:0]               PC_bram_read_PC_by_way;

    logic                           PC_bram_write_valid;
    logic [LOG_ROB_ENTRIES-2-1:0]   PC_bram_write_index;
    logic [3:0][31:0]               PC_bram_write_PC_by_way;

    // exception reg
        // need for exception req, deq/rollback
    logic                           exception_reg_valid;
    logic [LOG_ROB_ENTRIES-1:0]     exception_reg_index;
    logic [31:0]                    exception_reg_cause;

    // ----------------------------------------------------------------
    // Logic:

    // FF state
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_by_4way <= '0;
            has_checkpoint_by_4way <= '0;
            complete_by_entry <= '0;
            killed_by_entry <= '0;

            kill_next_enq <= 1'b0;
        end
        else begin
            if (enq_perform) begin
                valid_by_4way[tail_ptr] <= 1'b1;
                has_checkpoint_by_4way[tail_ptr] <= dispatch_has_checkpoint;
                complete_by_entry[4*tail_ptr+3] <= 1'b0;
                complete_by_entry[4*tail_ptr+2] <= 1'b0;
                complete_by_entry[4*tail_ptr+1] <= 1'b0;
                complete_by_entry[4*tail_ptr+0] <= 1'b0;
                killed_by_entry[4*head_ptr+3] <= dispatch_rob_enq_killed;
                killed_by_entry[4*head_ptr+2] <= dispatch_rob_enq_killed;
                killed_by_entry[4*head_ptr+1] <= dispatch_rob_enq_killed;
                killed_by_entry[4*head_ptr+0] <= dispatch_rob_enq_killed;

                kill_next_enq <= 1'b0;
            end
            else if () begin
                kill_next_enq <= 1'b1;
            end

            if (deq_perform) begin
                valid_by_4way[head_ptr] <= 1'b0;
                has_checkpoint_by_4way[head_ptr] <= 1'b0;
                complete_by_entry[4*head_ptr+3] <= 1'b0;
                complete_by_entry[4*head_ptr+2] <= 1'b0;
                complete_by_entry[4*head_ptr+1] <= 1'b0;
                complete_by_entry[4*head_ptr+0] <= 1'b0;
                killed_by_entry[4*head_ptr+3] <= 1'b0;
                killed_by_entry[4*head_ptr+2] <= 1'b0;
                killed_by_entry[4*head_ptr+1] <= 1'b0;
                killed_by_entry[4*head_ptr+0] <= 1'b0;
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

            if (ldu_complete_valid) begin
                complete_by_entry[ldu_complete_ROB_index] <= 1'b1;
            end
            if (stamofu_complete_valid) begin
                complete_by_entry[stamofu_complete_ROB_index] <= 1'b1;
            end
            if (branch_notif_valid) begin

            end
        end
    end

    // enq logic:
    always_comb begin
        dispatch_enq_ready = valid_by_4way[tail_ptr];

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
        bulk_bram_write_entry.checkpoint_index = dispatch_checkpoint_index;

        PC_bram_write_valid = enq_perform;
        PC_bram_write_index = tail_ptr;
        PC_bram_write_PC_by_way = dispatch_PC_by_way;
    end

    // deq logic:
    always_comb begin

    end

endmodule