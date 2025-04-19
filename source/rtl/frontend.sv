/*
    Filename: frontend.sv
    Author: zlagpacan
    Description: RTL for Front End
    Spec: LOROF/spec/design/frontend.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module frontend #(
    parameter INIT_PC = 32'h0,
    parameter INIT_ASID = 9'h0,
    parameter INIT_EXEC_MODE = M_MODE
) (

    // seq
    input logic CLK,
    input logic nRST,

    // itlb req
    output logic                    itlb_req_valid,
    output logic                    itlb_req_exec_mode,
    output logic                    itlb_req_virtual_mode,
    output logic [VPN_WIDTH-1:0]    itlb_req_vpn,
    output logic [ASID_WIDTH-1:0]   itlb_req_ASID,

    // itlb resp
    input logic                     itlb_resp_valid,
    input logic [PPN_WIDTH-1:0]     itlb_resp_ppn,
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

    // op dispatch by way:

    // 4-way ROB entry valid
    output logic                                    dispatch_rob_valid,

    // general instr info
    output logic [3:0]                              dispatch_valid_by_way,
    output logic [3:0]                              dispatch_uncompressed_by_way,
    output logic [31:0]                             dispatch_PC_by_way,
    output logic [3:0]                              dispatch_is_rename_by_way,
    output logic [3:0][BTB_PRED_INFO_WIDTH-1:0]     dispatch_pred_info_by_way,
    output logic [3:0][MDPT_INFO_WIDTH-1:0]         dispatch_mdp_info_by_way,
    output logic                                    dispatch_wait_write_buffer,
    output logic [3:0][3:0]                         dispatch_op_by_way,
    output logic [19:0]                             dispatch_imm20_by_way,

    // ordering
    output logic [3:0]                              dispatch_mem_aq,
    output logic [3:0]                              dispatch_io_aq,
    output logic [3:0]                              dispatch_mem_rl,
    output logic [3:0]                              dispatch_io_rl,

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

    // mdpt update
    input logic                         mdpt_update_valid,
    input logic [31:0]                  mdpt_update_start_full_PC,
    input logic [ASID_WIDTH-1:0]        mdpt_update_ASID,
    input logic [MDPT_INFO_WIDTH-1:0]   mdpt_update_mdp_info,

    // fetch + decode restart from ROB
    input logic                             rob_restart_valid,
    input logic [31:0]                      rob_restart_PC,
    input logic [8:0]                       rob_restart_ASID,
    input logic [1:0]                       rob_restart_exec_mode,
    input logic                             rob_restart_virtual_mode,
    input logic                             rob_restart_trap_sfence,
    input logic                             rob_restart_trap_wfi,
    input logic                             rob_restart_trap_sret,

    // branch update from ROB
    input logic                             rob_branch_update_valid,
    input logic                             rob_branch_update_is_mispredict,
    input logic                             rob_branch_update_is_taken,
    input logic                             rob_branch_update_use_upct,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   rob_branch_update_updated_pred_info,
    input logic                             rob_branch_update_pred_lru,
    input logic [31:0]                      rob_branch_update_start_PC,
    input logic [31:0]                      rob_branch_update_target_PC,
    input logic                             rob_branch_update_have_checkpoint,

    // ROB control of map table
    input logic                             rob_controlling_map_table,
    input logic [3:0]                       rob_map_table_write_valid_by_port,
    input logic [3:0][LOG_AR_COUNT-1:0]     rob_map_table_write_AR_by_port,
    input logic [3:0][LOG_PR_COUNT-1:0]     rob_map_table_write_PR_by_port,

    // ROB control of checkpoint restore
    input logic                                 rob_checkpoint_restore_valid,
    input logic                                 rob_checkpoint_restore_clear,
    input logic [CHECKPOINT_INDEX_WIDTH-1:0]    rob_checkpoint_restore_index,

    // hardware failure
    output logic istream_unrecoverable_fault
);

    // ----------------------------------------------------------------
    // Signals:

    //////////////////////
    // Fetch Req Stage: //
    //////////////////////

    // state
    logic                   fetch_req_wait_for_restart_state, next_fetch_req_wait_for_restart_state;
    logic [VA_WIDTH-1:0]    fetch_req_PC_VA, next_fetch_req_PC_VA;
    logic [ASID_WIDTH-1:0]  fetch_req_ASID, next_fetch_req_ASID;
    logic [1:0]             fetch_req_exec_mode, next_fetch_req_exec_mode;
    logic                   fetch_req_virtual_mode, next_fetch_req_virtual_mode;

    // control
    logic fetch_req_valid;
    // logic fetch_req_clear; // have all info in restarts

    // interruptable access PC
    logic fetch_req_access_PC_change;
    logic [VA_WIDTH-1:0] fetch_req_access_PC_VA;

    // modules:

    // btb:

        // REQ stage
        logic                   btb_valid_REQ;
        logic [31:0]            btb_full_PC_REQ;
        logic [ASID_WIDTH-1:0]  btb_ASID_REQ;

        // RESP stage
        logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_PRED_INFO_WIDTH-1:0] btb_pred_info_by_instr_RESP;
        logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]                          btb_pred_lru_by_instr_RESP;
        logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_TARGET_WIDTH-1:0]    btb_target_by_instr_RESP;

        // Update 0
        logic                   btb_update0_valid;
        logic [31:0]            btb_update0_start_full_PC;
        logic [ASID_WIDTH-1:0]  btb_update0_ASID;

        // Update 1
        logic [BTB_PRED_INFO_WIDTH-1:0] btb_update1_pred_info;
        logic                           btb_update1_pred_lru;
        logic [31:0]                    btb_update1_target_full_PC;

    // lht:

        // REQ stage
        logic                     lht_valid_REQ;
        logic [31:0]              lht_full_PC_REQ;
        logic [ASID_WIDTH-1:0]    lht_ASID_REQ;

        // RESP stage
        logic [LHT_ENTRIES_PER_BLOCK-1:0][LH_LENGTH-1:0] lht_LH_by_instr_RESP;

        // Update 0 stage
        logic                     lht_update0_valid;
        logic [31:0]              lht_update0_start_full_PC;
        logic [ASID_WIDTH-1:0]    lht_update0_ASID;
        logic [LH_LENGTH-1:0]     lht_update0_LH;

    // mdpt:

        // REQ stage
        logic                   mdpt_valid_REQ;
        logic [31:0]            mdpt_full_PC_REQ;
        logic [ASID_WIDTH-1:0]  mdpt_ASID_REQ;

        // RESP stage
        logic [MDPT_ENTRIES_PER_BLOCK-1:0][MDPT_INFO_WIDTH-1:0] mdpt_mdp_info_by_instr_RESP;

        // MDPT Update 0 stage
        logic                           mdpt_mdpt_update0_valid;
        logic [31:0]                    mdpt_mdpt_update0_start_full_PC;
        logic [ASID_WIDTH-1:0]          mdpt_mdpt_update0_ASID;
        logic [MDPT_INFO_WIDTH-1:0]     mdpt_mdpt_update0_mdp_info;

    // itlb req:
        
        // in frontend interface

    // icache req:
    
        // in frontend interface

    ///////////////////////
    // Fetch Resp Stage: //
    ///////////////////////

    // state
    typedef enum logic [1:0] {
        FETCH_RESP_IDLE,
        FETCH_RESP_ACTIVE,
        FETCH_RESP_COMPLEX_BRANCH,
        // FETCH_RESP_ITLB_MISS, 
            // tlb misses are handled in ACTIVE and ICACHE_MISS states
            // can become TLB miss on invalidation during ICACHE_MISS
        FETCH_RESP_ICACHE_MISS
    } fetch_resp_state_t;

    fetch_resp_state_t fetch_resp_state, next_fetch_resp_state;

    // pipeline latch
    logic [VA_WIDTH-1:0]    fetch_resp_PC_VA, next_fetch_resp_PC_VA;
    logic [7:0]             fetch_resp_PC_mask;

    // control
    // logic fetch_resp_clear; // have all info in restarts
    logic fetch_resp_instr_yield;
    logic fetch_resp_perform_pred_actions;

    // ghr
    logic [GH_LENGTH-1:0] ghr, next_ghr;

    // hit logic
    logic ihit;
    logic [PA_WIDTH-1:0] fetch_resp_PC_PA;
    logic [ICACHE_FETCH_WIDTH-1:0][7:0] fetch_resp_selected_instr_16B;

    // pred logic
    logic [7:0]                     fetch_resp_raw_pred_vec;
    logic [7:0]                     fetch_resp_candidate_pred_vec;
    logic                           fetch_resp_pred_present;

    logic [7:0]                     fetch_resp_selected_one_hot;
    logic [7:0]                     fetch_resp_selected_cold_ack_mask;
    logic [2:0]                     fetch_resp_selected_index;
    logic [7:0]                     fetch_resp_selected_pred_info;
    logic [BTB_TARGET_WIDTH-1:0]    fetch_resp_selected_target;
    logic [LH_LENGTH-1:0]           fetch_resp_selected_LH;

    logic [7:0]                     fetch_resp_saved_one_hot, next_fetch_resp_saved_one_hot;
    logic [7:0]                     fetch_resp_saved_cold_ack_mask, next_fetch_resp_saved_cold_ack_mask;
    logic [2:0]                     fetch_resp_saved_index, next_fetch_resp_saved_index;
    logic [7:0]                     fetch_resp_saved_pred_info, next_fetch_resp_saved_pred_info;
    logic [BTB_TARGET_WIDTH-1:0]    fetch_resp_saved_target, next_fetch_resp_saved_target;
    logic [LH_LENGTH-1:0]           fetch_resp_saved_LH, next_fetch_resp_saved_LH;

    logic [31:0] fetch_resp_pred_PC_VA;

    logic fetch_resp_check_complex_branch_taken;
    logic fetch_resp_complex_branch_taken;

    // pred actions
    logic [7:0] fetch_resp_instr_16B_yield_vec;
    logic [7:0] fetch_resp_redirect_vec;

    // modules:

    // lbpt:

        // RESP stage
        logic                   lbpt_valid_RESP;
        logic [31:0]            lbpt_full_PC_RESP;
        logic [LH_LENGTH-1:0]   lbpt_LH_RESP;
        logic [ASID_WIDTH-1:0]  lbpt_ASID_RESP;

        // RESTART stage
        logic lbpt_pred_taken_RESTART;

        // Update 0
        logic                   lbpt_update0_valid;
        logic [31:0]            lbpt_update0_start_full_PC;
        logic [LH_LENGTH-1:0]   lbpt_update0_LH;
        logic [ASID_WIDTH-1:0]  lbpt_update0_ASID;
        logic                   lbpt_update0_taken;

        // Update 1
        logic lbpt_update1_correct;

    // gbpt:

        // RESP stage
        logic                   gbpt_valid_RESP;
        logic [31:0]            gbpt_full_PC_RESP;
        logic [GH_LENGTH-1:0]   gbpt_GH_RESP;
        logic [ASID_WIDTH-1:0]  gbpt_ASID_RESP;

        // RESTART stage
        logic gbpt_pred_taken_RESTART;

        // Update 0
        logic                   gbpt_update0_valid;
        logic [31:0]            gbpt_update0_start_full_PC;
        logic [GH_LENGTH-1:0]   gbpt_update0_GH;
        logic [ASID_WIDTH-1:0]  gbpt_update0_ASID;
        logic                   gbpt_update0_taken;

        // Update 1
        logic gbpt_update1_correct;

    // upct:

        // RESP stage
        logic                           upct_valid_RESP;
        logic [LOG_UPCT_ENTRIES-1:0]    upct_upct_index_RESP;
        logic [UPPER_PC_WIDTH-1:0]      upct_upper_PC_RESP;

        // Update 0
        logic           upct_update0_valid;
        logic [31:0]    upct_update0_start_full_PC;

        // Update 1
        logic [LOG_UPCT_ENTRIES-1:0]    upct_update1_upct_index;

    // ras:

        // RESP stage
        logic           ras_link_RESP;
        logic [31:0]    ras_link_full_PC_RESP;
        logic           ras_ret_RESP;

        logic [31:0]                ras_ret_full_PC_RESP;
        logic [RAS_INDEX_WIDTH-1:0] ras_ras_index_RESP;

        // Update 0
        logic                       ras_update0_valid;
        logic [RAS_INDEX_WIDTH-1:0] ras_update0_ras_index;

    // itlb resp:

        // in frontend interface

    // icache resp:

        // in frontend interface

    ////////////////////////
    // Update Prep Stage: //
    ////////////////////////

    // LH from checkpoint
    // GH from checkpoint

    logic [LH_LENGTH-1:0]           update_prep_LH;
    logic [GH_LENGTH-1:0]           update_prep_GH;
    logic [RAS_INDEX_WIDTH-1:0]     update_prep_ras_index;

    /////////////////////
    // Update 0 Stage: //
    /////////////////////

    // valid
    // start pc
    // ASID
    // LH
    // GH
    // ras index
    // taken

    logic                           update0_valid;
    logic [31:0]                    update0_start_full_PC;
    logic [ASID_WIDTH-1:0]          update0_ASID;
    logic [LH_LENGTH-1:0]           update0_LH;
    logic [GH_LENGTH-1:0]           update0_GH;
    logic [RAS_INDEX_WIDTH-1:0]     update0_ras_index;
    logic                           update0_taken;

    logic update0_update_checkpoint_dependent;

    /////////////////////
    // Update 1 Stage: //
    /////////////////////

    // correct
    // upct index
    // pred info
    // pred lru
    // target full pc

    logic update1_correct;
    logic [LOG_UPCT_ENTRIES-1:0] update1_upct_index;

    logic update1_update_checkpoint_dependent;

    /////////////////
    // Stream DeQ: //
    /////////////////

    // state

    // pipeline latch
        // istream acts as latch at beginning of stage

    // control
    logic istream_clear;
    // logic istream_stall_SDEQ;
        // decode stall

    // modules:

    // istream:

        // SENQ stage
        logic           istream_valid_SENQ;
        logic [7:0]     istream_valid_by_fetch_2B_SENQ;
        logic [7:0]     istream_one_hot_redirect_by_fetch_2B_SENQ;
            // means take after PC as pred PC
            // always the last instr in the fetch block
        logic [7:0][15:0]                       istream_instr_2B_by_fetch_2B_SENQ;
        logic [7:0][BTB_PRED_INFO_WIDTH-1:0]    istream_pred_info_by_fetch_2B_SENQ;
        logic [7:0]                             istream_pred_lru_by_fetch_2B_SENQ;
        logic [7:0][MDPT_INFO_WIDTH-1:0]        istream_mdp_info_by_fetch_2B_SENQ;
        logic [31:0]                            istream_after_PC_SENQ;
        logic [LH_LENGTH-1:0]                   istream_LH_SENQ;
        logic [GH_LENGTH-1:0]                   istream_GH_SENQ;
        logic [RAS_INDEX_WIDTH-1:0]             istream_ras_index_SENQ;
        logic                                   istream_page_fault_SENQ;
        logic                                   istream_access_fault_SENQ;

        // SENQ feedback
        logic istream_stall_SENQ;

        // SDEQ stage
        logic                                       istream_valid_SDEQ;
        logic [3:0]                                 istream_valid_by_way_SDEQ;
        logic [3:0]                                 istream_uncompressed_by_way_SDEQ;
        logic [3:0][1:0][15:0]                      istream_instr_2B_by_way_by_chunk_SDEQ;
        logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0]   istream_pred_info_by_way_by_chunk_SDEQ;
        logic [3:0][1:0]                            istream_pred_lru_by_way_by_chunk_SDEQ;
        logic [3:0][1:0]                            istream_redirect_by_way_by_chunk_SDEQ;
        logic [3:0][1:0][31:0]                      istream_pred_PC_by_way_by_chunk_SDEQ;
        logic [3:0][1:0]                            istream_page_fault_by_way_by_chunk_SDEQ;
        logic [3:0][1:0]                            istream_access_fault_by_way_by_chunk_SDEQ;
        logic [3:0][MDPT_INFO_WIDTH-1:0]            istream_mdp_info_by_way_SDEQ;
        logic [3:0][31:0]                           istream_PC_by_way_SDEQ;
        logic [3:0][LH_LENGTH-1:0]                  istream_LH_by_way_SDEQ;
        logic [3:0][GH_LENGTH-1:0]                  istream_GH_by_way_SDEQ;
        logic [3:0][RAS_INDEX_WIDTH-1:0]            istream_ras_index_by_way_SDEQ;

        // SDEQ feedback
        logic istream_stall_SDEQ;

        // restart
        logic         istream_restart;
        logic [31:0]  istream_restart_PC;

    ///////////////////
    // Decode Stage: //
    ///////////////////
    
    // state
    typedef enum logic [1:0] {
        DECODE_WAITING_FOR_RESTART,
        DECODE_RESTART_UPDATE0,
        DECODE_RESTART_UPDATE1
    } decode_state_t;

    decode_state_t decode_state, next_decode_state;

    logic [1:0]     decode_exec_mode;
    logic           decode_trap_sfence;
    logic           decode_trap_wfi;
    logic           decode_trap_sret;

    // pipeline latch

    // control
    logic decode_clear;
    logic decode_stall;
        // stage valid AND:
            // rename stall

    logic decode_restart_valid;
    logic decode_restart_PC;

    logic decode_wait_for_restart;

    // modules:

    // decoder by way:

        // environment info
        logic [3:0][1:0]    decoder_env_exec_mode_by_way;
        logic [3:0]         decoder_env_trap_sfence_by_way;
        logic [3:0]         decoder_env_trap_wfi_by_way;
        logic [3:0]         decoder_env_trap_sret_by_way;

        // instr info
        logic [3:0]                             decoder_uncompressed_by_way;
        logic [3:0][31:0]                       decoder_instr32_by_way;
        logic [3:0][BTB_PRED_INFO_WIDTH-1:0]    decoder_pred_info_chunk0_by_way;
        logic [3:0][BTB_PRED_INFO_WIDTH-1:0]    decoder_pred_info_chunk1_by_way;

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
        logic [3:0][3:0]    decoder_op_by_way;
        logic [3:0]         decoder_is_reg_write_by_way;
        
        // A operand
        logic [3:0][4:0]    decoder_A_AR_by_way;
        logic [3:0]         decoder_A_unneeded_by_way;
        logic [3:0]         decoder_A_is_zero_by_way;
        logic [3:0]         decoder_A_is_ret_ra_by_way;

        // B operand
        logic [3:0][4:0]    decoder_B_AR_by_way;
        logic [3:0]         decoder_B_unneeded_by_way;
        logic [3:0]         decoder_B_is_zero_by_way;

        // dest operand
        logic [3:0][4:0]    decoder_dest_AR_by_way;
        logic [3:0]         decoder_dest_is_zero_by_way;
        logic [3:0]         decoder_dest_is_link_ra_by_way;

        // imm
        logic [3:0][19:0] decoder_imm20_by_way;

        // pred info out
        logic [3:0][BTB_PRED_INFO_WIDTH-1:0]    decoder_pred_info_out_by_way;
        logic [3:0]                             decoder_missing_pred_by_way;

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

    ///////////////////
    // Rename Stage: //
    ///////////////////

    // state
    logic rename_valid;

    // pipeline latch

    // control
    logic rename_clear;
    logic rename_stall;
        // stage valid AND:
            // dispatch stall
            // free_list failed rename

    // modules:

    // free_list:

        // enqueue request
        logic [FREE_LIST_BANK_COUNT-1:0]                    free_list_enq_req_valid_by_bank;
        logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]  free_list_enq_req_PR_by_bank;

        // enqueue feedback
        logic [FREE_LIST_BANK_COUNT-1:0]                    free_list_enq_resp_ack_by_bank;

        // dequeue request
        logic [FREE_LIST_BANK_COUNT-1:0]                    free_list_deq_req_valid_by_bank;
        logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]  free_list_deq_req_PR_by_bank;

        // dequeue feedback
        logic [FREE_LIST_BANK_COUNT-1:0]                    free_list_deq_resp_ready_by_bank;

    // map_table:

        // 12x read ports
        logic [11:0][LOG_AR_COUNT-1:0]  map_table_read_AR_by_port;
        logic [11:0][LOG_PR_COUNT-1:0]  map_table_read_PR_by_port;

        // 4x write ports
        logic [3:0]                     map_table_write_valid_by_port;
        logic [3:0][LOG_AR_COUNT-1:0]   map_table_write_AR_by_port;
        logic [3:0][LOG_PR_COUNT-1:0]   map_table_write_PR_by_port;

        // checkpoint save
        logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]  map_table_save_map_table;

        // checkpoint restore
        logic                                   map_table_restore_valid;
        logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]  map_table_restore_map_table;

    // checkpoint_array:

        // checkpoint save
        logic                                   checkpoint_array_save_valid;
        logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]  checkpoint_array_save_map_table;
        logic [LH_LENGTH-1:0]                   checkpoint_array_save_LH;
        logic [GH_LENGTH-1:0]                   checkpoint_array_save_GH;
        logic [RAS_INDEX_WIDTH-1:0]             checkpoint_array_save_ras_index;

        logic                                   checkpoint_array_save_ready;
        logic [CHECKPOINT_INDEX_WIDTH-1:0]      checkpoint_array_save_index;

        // checkpoint restore
        logic                                   checkpoint_array_restore_valid;
        logic [CHECKPOINT_INDEX_WIDTH-1:0]      checkpoint_array_restore_index;

        logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]  checkpoint_array_restore_map_table;
        logic [LH_LENGTH-1:0]                   checkpoint_array_restore_LH;
        logic [GH_LENGTH-1:0]                   checkpoint_array_restore_GH;
        logic [RAS_INDEX_WIDTH-1:0]             checkpoint_array_restore_ras_index;

        // advertized threshold
        logic checkpoint_array_above_threshold;

    // ar_dep_check:

        // inputs by way
        logic [3:0][4:0]    ar_dep_check_A_AR_by_way;
        logic [3:0][4:0]    ar_dep_check_B_AR_by_way;
        logic [3:0]         ar_dep_check_regwrite_by_way;
        logic [3:0][4:0]    ar_dep_check_dest_AR_by_way;

        // outputs by way
        logic [3:0]         ar_dep_check_A_PR_dep_by_way;
        logic [3:0][1:0]    ar_dep_check_A_PR_sel_by_way;
        logic [3:0]         ar_dep_check_B_PR_dep_by_way;
        logic [3:0][1:0]    ar_dep_check_B_PR_sel_by_way;

    /////////////////////
    // Dispatch Stage: //
    /////////////////////

    // state

    // pipeline latch

    // control
    logic dispatch_clear;
    logic dispatch_stall;
        // stage valid AND:
            // failed IQ dispatch
            // ROB not ready

    // modules:

    // ready_table:

        // 8x read ports
        logic [7:0][LOG_PR_COUNT-1:0]   ready_table_read_PR_by_port;
        logic [7:0]                     ready_table_read_ready_by_port;

        // 4x set ports
        logic [3:0]                     ready_table_set_valid_by_port;
        logic [3:0][LOG_PR_COUNT-1:0]   ready_table_set_PR_by_port;

        // 4x clear ports
        logic [3:0]                     ready_table_clear_valid_by_port;
        logic [3:0][LOG_PR_COUNT-1:0]   ready_table_clear_PR_by_port;

    // ----------------------------------------------------------------
    // Logic:

    //////////////////////
    // Fetch Req Stage: //
    //////////////////////

    // FF logic;
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_req_wait_for_restart_state <= 1'b0;
            fetch_req_PC_VA <= INIT_PC;
            fetch_req_ASID <= INIT_ASID;
            fetch_req_exec_mode <= M_MODE;
            fetch_req_virtual_mode <= 1'b0;
        end
        else begin
            fetch_req_wait_for_restart_state <= next_fetch_req_wait_for_restart_state;
            fetch_req_PC_VA <= next_fetch_req_PC_VA;
            fetch_req_ASID <= next_fetch_req_ASID;
            fetch_req_exec_mode <= next_fetch_req_exec_mode;
            fetch_req_virtual_mode <= next_fetch_req_virtual_mode;
        end
    end

    // next state logic:
    always_comb begin

        next_fetch_req_wait_for_restart_state = fetch_req_wait_for_restart_state;
        next_fetch_req_PC_VA = fetch_req_PC_VA;
        next_fetch_req_ASID = fetch_req_ASID;
        next_fetch_req_exec_mode = fetch_req_exec_mode;
        next_fetch_req_virtual_mode = fetch_req_virtual_mode;

        if (rob_restart_valid) begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            next_fetch_req_PC_VA = rob_restart_PC;
            next_fetch_req_ASID = rob_restart_ASID;
            next_fetch_req_exec_mode = rob_restart_exec_mode;
            next_fetch_req_virtual_mode = rob_restart_virtual_mode;
        end
        else if (decode_restart_valid) begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            next_fetch_req_PC_VA = decode_restart_PC;
        end
        else if (decode_wait_for_restart) begin
            next_fetch_req_wait_for_restart_state = 1'b1;
        end
        else if (fetch_req_wait_for_restart_state) begin
            next_fetch_req_wait_for_restart_state = 1'b1;
        end
        else begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            if (fetch_req_access_PC_change) begin
                next_fetch_req_PC_VA = {{fetch_req_access_PC_VA[31:4] + 28'h1}[27:0], 4'b0000};
            end
            else begin
                next_fetch_req_PC_VA = {{fetch_req_PC_VA[31:4] + 28'h1}[27:0], 4'b0000};
            end
        end
    end

    // next pipeline latch
    always_comb begin
        next_fetch_resp_PC_VA = fetch_req_access_PC_VA;
    end

    // control
    always_comb begin
        fetch_req_valid = ~fetch_req_wait_for_restart_state;
    end

    // module connections:
    always_comb begin

        // btb:
        btb_valid_REQ = fetch_req_valid;
        btb_full_PC_REQ = fetch_req_access_PC_VA;
        btb_ASID_REQ = fetch_req_ASID;
        
        btb_update0_valid = 
        btb_update0_start_full_PC = 
        btb_update0_ASID = 

        btb_update1_pred_info = 
        btb_update1_pred_lru = 
        btb_update1_target_full_PC = 

        // lht:
        lht_valid_REQ = fetch_req_valid;
        lht_full_PC_REQ = fetch_req_access_PC_VA;
        lht_ASID_REQ = fetch_req_ASID;

        // check for restart value of LH
        if () begin
            lht_update0_valid = 
            lht_update0_start_full_PC = 
            lht_update0_ASID = 
            lht_update0_LH = 
        end
        // check for complex branch update present
        else if (fetch_resp_check_complex_branch_taken & fetch_resp_perform_pred_actions) begin
            // shift in based on if complex branch T/NT
            lht_update0_valid = 
            lht_update0_start_full_PC = 
            lht_update0_ASID = 
            lht_update0_LH = 
        end
        // otherwise no update
        else begin
            lht_update0_valid = 1'b0;
            lht_update0_start_full_PC = 
            lht_update0_ASID = 
            lht_update0_LH = 
        end

        // mdpt:
        mdpt_valid_REQ = fetch_req_valid;
        mdpt_full_PC_REQ = fetch_req_access_PC_VA;
        mdpt_ASID_REQ = fetch_req_ASID;

        mdpt_mdpt_update0_valid = 
        mdpt_mdpt_update0_start_full_PC = 
        mdpt_mdpt_update0_ASID = 
        mdpt_mdpt_update0_mdp_info = 

        // itlb:
        itlb_req_valid = fetch_req_valid;
        itlb_req_exec_mode = fetch_req_exec_mode;
        itlb_req_virtual_mode = fetch_req_virtual_mode;
        itlb_req_vpn = fetch_req_access_PC_VA;
        itlb_req_ASID = fetch_req_ASID;

        // icache:
        icache_req_valid = fetch_req_valid;
        icache_req_block_offset = fetch_req_access_PC_VA[ICACHE_BLOCK_OFFSET_WIDTH4]; // choose first or second 16B of 32B block
        icache_req_index = fetch_req_access_PC_VA[
            ICACHE_INDEX_WIDTH + ICACHE_BLOCK_OFFSET_WIDTH - 1 : ICACHE_BLOCK_OFFSET_WIDTH
        ];
    end

    // modules:

    btb BTB (
        .CLK(CLK),
        .nRST(nRST),
        .valid_REQ(btb_valid_REQ),
        .full_PC_REQ(btb_full_PC_REQ),
        .ASID_REQ(btb_ASID_REQ),
        .pred_info_by_instr_RESP(btb_pred_info_by_instr_RESP),
        .pred_lru_by_instr_RESP(btb_pred_lru_by_instr_RESP),
        .target_by_instr_RESP(btb_target_by_instr_RESP),
        .update0_valid(btb_update0_valid),
        .update0_start_full_PC(btb_update0_start_full_PC),
        .update0_ASID(btb_update0_ASID),
        .update1_pred_info(btb_update1_pred_info),
        .update1_pred_lru(btb_update1_pred_lru),
        .update1_target_full_PC(btb_update1_target_full_PC)
    );

    lht LHT (
        .CLK(CLK),
        .nRST(nRST),
        .valid_REQ(lht_valid_REQ),
        .full_PC_REQ(lht_full_PC_REQ),
        .ASID_REQ(lht_ASID_REQ),
        .LH_by_instr_RESP(lht_LH_by_instr_RESP),
        .update0_valid(lht_update0_valid),
        .update0_start_full_PC(lht_update0_start_full_PC),
        .update0_ASID(lht_update0_ASID),
        .update0_LH(lht_update0_LH)
    );

    mdpt MPDT (
        .CLK(CLK),
        .nRST(nRST),
        .valid_REQ(mdpt_valid_REQ),
        .full_PC_REQ(mdpt_full_PC_REQ),
        .ASID_REQ(mdpt_ASID_REQ),
        .mdp_info_by_instr_RESP(mdpt_mdp_info_by_instr_RESP),
        .mdpt_update0_valid(mdpt_mdpt_update0_valid),
        .mdpt_update0_start_full_PC(mdpt_mdpt_update0_start_full_PC),
        .mdpt_update0_ASID(mdpt_mdpt_update0_ASID),
        .mdpt_update0_mdp_info(mdpt_mdpt_update0_mdp_info)
    );

    ///////////////////////
    // Fetch Resp Stage: //
    ///////////////////////

    // FF logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_resp_state <= FETCH_RESP_NORMAL;
            ghr <= '0;
        end
        else begin
            if (rob_restart_valid | decode_restart_valid) begin
                fetch_resp_state <= FETCH_RESP_IDLE;
            end
            else begin
                fetch_resp_state <= next_fetch_resp_state;
            end

            // check for restart value of GHR
            if () begin
                ghr <= 
            end

            // check for complex branch update present
            else if (fetch_resp_check_complex_branch_taken & fetch_resp_perform_pred_actions) begin
                // shift in based on if complex branch T/NT
                ghr <= {ghr[GH_LENGTH-2:0], fetch_resp_complex_branch_taken};
            end
        end
    end

    // pipeline latch logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_resp_PC_VA <= 32'h0;
            fetch_resp_PC_mask <= 8'b11111111;

            fetch_resp_saved_one_hot <= 8'b00000000;
            fetch_resp_saved_cold_ack_mask <= 8'b11111111;
            fetch_resp_saved_index <= 3'h0;
            fetch_resp_saved_pred_info <= 8'b00000000;
            fetch_resp_saved_target <= '0;
            fetch_resp_saved_LH <= 8'h0;
        end
        else begin
            fetch_resp_PC_VA <= next_fetch_resp_PC_VA;

            // create PC mask
            case (next_fetch_resp_PC_VA[3:1])
                3'b000: fetch_resp_PC_mask <= 8'b11111111;
                3'b001: fetch_resp_PC_mask <= 8'b11111110;
                3'b010: fetch_resp_PC_mask <= 8'b11111100;
                3'b011: fetch_resp_PC_mask <= 8'b11111000;
                3'b100: fetch_resp_PC_mask <= 8'b11110000;
                3'b101: fetch_resp_PC_mask <= 8'b11100000;
                3'b110: fetch_resp_PC_mask <= 8'b11000000;
                3'b111: fetch_resp_PC_mask <= 8'b10000000;
            endcase

            fetch_resp_saved_one_hot <= next_fetch_resp_saved_one_hot;
            fetch_resp_saved_cold_ack_mask <= next_fetch_resp_saved_cold_ack_mask;
            fetch_resp_saved_index <= next_fetch_resp_saved_index;
            fetch_resp_saved_pred_info <= next_fetch_resp_saved_pred_info;
            fetch_resp_saved_target <= next_fetch_resp_saved_target;
            fetch_resp_saved_LH <= next_fetch_resp_saved_LH;
        end
    end

    // hit logic
    always_comb begin

        // defaults:
        ihit = 1'b0;
        fetch_resp_PC_PA = {itlb_resp_ppn, fetch_resp_PC_VA[PO_WIDTH-1:0]};
        fetch_resp_selected_instr_16B = icache_resp_instr_16B_by_way[0];

        icache_resp_hit_valid = 1'b0;
        icache_resp_hit_way = 1'b0;
        icache_resp_miss_valid = 1'b0;
        icache_resp_miss_tag = fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH];

        // TLB hit check
        if (itlb_resp_valid) begin

            // page fault or access fault
            if (itlb_resp_page_fault | itlb_resp_access_fault) begin

                // automatic ihit
                ihit = 1'b1;
            end

            // cache hit check way 0
            if (icache_resp_valid_by_way[0] & 
                icache_resp_tag_by_way[0] == fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH]
            ) begin
                ihit = 1'b1;
                fetch_resp_selected_instr_16B = icache_resp_instr_16B_by_way[0];

                icache_resp_hit_valid = 1'b1;
                icache_resp_hit_way = 1'b0;
            end
        
            // cache hit check way 1
            else if (icache_resp_valid_by_way[1] & 
                icache_resp_tag_by_way[1] == fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH]
            ) begin
                ihit = 1'b1;
                fetch_resp_selected_instr_16B = icache_resp_instr_16B_by_way[1];

                icache_resp_hit_valid = 1'b1;
                icache_resp_hit_way = 1'b1;
            end

            // otherwise, cache miss
            else begin
                ihit = 1'b0;

                // only send cache miss on first time missing
                    // can be in ACTIVE, COMPLEX_BRANCH, or ITLB_MISS state
                icache_resp_miss_valid = fetch_resp_state != FETCH_RESP_ICACHE_MISS;
                icache_resp_miss_tag = fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH];
            end
        end

        // otherwise, TLB miss
        else begin
            ihit = 1'b0;
        end
    end

    // pred selection logic:
    always_comb begin

        for (int i = 0; i < 8; i++) begin
            fetch_resp_raw_pred_vec[i] = 
                (
                    btb_pred_info_by_instr_RESP[i][6] 
                        // jump, ret, or complex branch
                    |
                    btb_pred_info_by_instr_RESP[i][7] & btb_pred_info_by_instr_RESP[i][5]
                        // simple branch taken
                )
                & fetch_resp_saved_cold_ack_mask[i];
            ;
        end

        fetch_resp_candidate_pred_vec = fetch_resp_raw_pred_vec & fetch_resp_PC_mask;

        fetch_resp_pred_present = |fetch_resp_candidate_pred_vec;

        // use one hot mux to quickly select out pred and target of interest
        fetch_resp_selected_pred_info = '0;
        fetch_resp_selected_target = '0;
        fetch_resp_selected_LH = '0;
        for (int i = 0; i < 8; i++) begin
            if (fetch_resp_selected_one_hot[i]) begin
                fetch_resp_selected_pred_info |= btb_pred_info_by_instr_RESP[i];
                fetch_resp_selected_target |= btb_target_by_instr_RESP[i];
                fetch_resp_selected_LH |= lht_LH_by_instr_RESP[i];
            end
        end
    end

    pe_lsb #(
        .WIDTH(8),
        .USE_ONE_HOT(1),
        .USE_COLD(1),
        .USE_INDEX(1)
    ) PRED_PE (
        .req_vec(fetch_resp_candidate_pred_vec),
        .ack_one_hot(fetch_resp_selected_one_hot),
        .cold_ack_mask(fetch_resp_selected_cold_ack_mask),
        .ack_index(fetch_resp_selected_index)
    );

    // fast pred actions
    always_comb begin

        // check use global for complex branch taken
        if (fetch_resp_saved_pred_info[5]) begin
            fetch_resp_complex_branch_taken = gbpt_pred_taken_RESTART;
        end
        // otherwise use local for complex branch taken
        else begin
            fetch_resp_complex_branch_taken = lbpt_pred_taken_RESTART;
        end

        // check for predicted complex branch
        if (fetch_resp_check_complex_branch_taken & fetch_resp_complex_branch_taken) begin
            // yield below complex branch (saved cold ack mask)
            fetch_resp_instr_16B_yield_vec = fetch_resp_PC_mask & ~fetch_resp_saved_cold_ack_mask;
            // redirect at complex branch (saved one hot)
            fetch_resp_redirect_vec = fetch_resp_saved_one_hot;
        end
        // check for simple branch or jump
        else if (fetch_resp_selected_pred_info[7] | fetch_resp_selected_pred_info[6]) begin
            // can yield up to and including branch and jump (this cold ack mask)
            fetch_resp_instr_16B_yield_vec = fetch_resp_PC_mask & ~fetch_resp_selected_cold_ack_mask;
            // redirect at this branch or jump (this one hot)
            fetch_resp_redirect_vec = fetch_resp_selected_one_hot;
        end
        // otherwise, no branches
        else begin
            // yield everything after PC
            fetch_resp_instr_16B_yield_vec = fetch_resp_PC_mask;
            fetch_resp_redirect_vec = 8'b10000000;
        end
    end

    // pred-specific actions
    always_comb begin
        fetch_resp_pred_PC_VA = {
            {fetch_resp_pred_PC_VA[31:32-UPPER_PC_WIDTH] 
            + 
            {{(UPPER_PC_WIDTH-2){fetch_resp_saved_pred_info[2]}}, fetch_resp_saved_pred_info[1:0]}
            }[UPPER_PC_WIDTH-1:0], 
            fetch_resp_saved_target, 1'b0};

        upct_valid_RESP = 1'b0;
        upct_upct_index_RESP = fetch_resp_saved_pred_info[2:0]; 

        ras_link_RESP = 1'b0;
        ras_ret_RESP = 1'b0;

        // check complex branch taken
        if (fetch_resp_check_complex_branch_taken & fetch_resp_complex_branch_taken) begin
            upct_upct_index_RESP = fetch_resp_saved_pred_info[2:0];
            // bit [3] tells if use upct
            if (fetch_resp_saved_pred_info[3]) begin
                upct_valid_RESP = 1'b1;
                fetch_resp_pred_PC_VA = {upct_upper_PC_RESP, fetch_resp_saved_target, 1'b0};
            end
            // otherwise, upper PC + 3bindex, target
            else begin
                fetch_resp_pred_PC_VA = {
                    {fetch_resp_pred_PC_VA[31:32-UPPER_PC_WIDTH] 
                    + 
                    {{(UPPER_PC_WIDTH-2){fetch_resp_saved_pred_info[2]}}, fetch_resp_saved_pred_info[1:0]}
                    }[UPPER_PC_WIDTH-1:0], 
                    fetch_resp_saved_target, 1'b0};
            end
        end
        // otherwise, other branch or don't care
        else begin
            upct_upct_index_RESP = fetch_resp_selected_pred_info[2:0];

            casez (fetch_resp_selected_pred_info[7:4])

                4'b00??: // no pred
                begin
                    // don't care
                end

                4'b0100: // J
                begin
                    // bit [3] tells if use upct
                    if (fetch_resp_saved_pred_info[3]) begin
                        upct_valid_RESP = 1'b1;
                        fetch_resp_pred_PC_VA = {
                            upct_upper_PC_RESP, 
                            fetch_resp_saved_target, 1'b0};
                    end
                    // otherwise, upper PC + 3bindex, target
                    else begin
                        fetch_resp_pred_PC_VA = {
                            {fetch_resp_pred_PC_VA[31:32-UPPER_PC_WIDTH] 
                            + 
                            {{(UPPER_PC_WIDTH-2){fetch_resp_saved_pred_info[2]}}, fetch_resp_saved_pred_info[1:0]}
                            }[UPPER_PC_WIDTH-1:0], 
                            fetch_resp_saved_target, 1'b0};
                    end
                end

                4'b0101: // JAL PC+2
                begin
                    // bit [3] tells if use upct
                    if (fetch_resp_saved_pred_info[3]) begin
                        upct_valid_RESP = 1'b1;
                        fetch_resp_pred_PC_VA = {upct_upper_PC_RESP, fetch_resp_saved_target, 1'b0};
                            // upct indexed by fetch_resp_saved_pred_info[2:0] already
                    end
                    // otherwise, upper PC + 3bindex, target
                    else begin
                        fetch_resp_pred_PC_VA = {
                            {fetch_resp_pred_PC_VA[31:32-UPPER_PC_WIDTH] 
                            + 
                            {{(UPPER_PC_WIDTH-2){fetch_resp_saved_pred_info[2]}}, fetch_resp_saved_pred_info[1:0]}
                            }[UPPER_PC_WIDTH-1:0], 
                            fetch_resp_saved_target, 1'b0};
                    end

                    // link
                    if (fetch_resp_perform_pred_actions) begin
                        ras_link_RESP = 1'b1;
                    end
                end

                4'b0110: // RET
                begin
                    // take directly from ras
                    fetch_resp_pred_PC_VA = ras_ret_full_PC_RESP;
                end

                4'b0111: // RETL PC+2
                begin
                    // take directly from ras
                    fetch_resp_pred_PC_VA = ras_ret_full_PC_RESP;

                    // link
                    if (fetch_resp_perform_pred_actions) begin
                        ras_link_RESP = 1'b1;
                    end
                end

                4'b10??: // simple branch
                begin
                    // just treat as taken, not taken will not be selected
                    fetch_resp_pred_PC_VA = {
                        fetch_resp_PC_VA[31:32-UPPER_PC_WIDTH], 
                        fetch_resp_selected_target, 1'b0};
                end

                4'b11??: // complex branch
                begin
                    // don't care
                end

            endcase
        end
    end

    // state machine + control + interruptable access PC
    always_comb begin

        fetch_req_access_PC_change = 1'b0;
        fetch_req_access_PC_VA = fetch_req_PC_VA;
            // interrupt on istream stall
            // interrupt on branch prediction
            // interrupt on itlb or icache miss

        next_fetch_resp_state = fetch_resp_state;

        // reset cold ack mask
        next_fetch_resp_saved_cold_ack_mask = '1;
        // keep saving pred info
        next_fetch_resp_saved_one_hot = fetch_resp_saved_one_hot;
        next_fetch_resp_saved_index = fetch_resp_saved_index;
        next_fetch_resp_saved_pred_info = fetch_resp_saved_pred_info;
        next_fetch_resp_saved_target = fetch_resp_saved_target;
        next_fetch_resp_saved_LH = fetch_resp_saved_LH;

        fetch_resp_check_complex_branch_taken = 1'b0;

        fetch_resp_instr_yield = 1'b0;
        fetch_resp_perform_pred_actions = 1'b0;

        // state machine:
            // restarts are taken care of in FF logic
        case (fetch_resp_state)

            FETCH_RESP_IDLE:
            begin
                // only go into active when fetch req not in wait for restart state
                if (fetch_req_valid) begin
                    next_fetch_resp_state = FETCH_RESP_ACTIVE;
                end
            end

            FETCH_RESP_ACTIVE:
            begin
                // check miss
                if (~ihit) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_change = 1'b1;
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;

                    // check itlb miss -> stay here
                    if (~itlb_resp_valid) begin
                        next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    end
                    // otherwise, icache miss
                    else begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                end
                // check istream stall with icache hit
                else if (istream_stall_SENQ) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_change = 1'b1;
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                end
                // otherwise, clean icache hit
                else begin

                    // can perform pred actions
                    fetch_resp_perform_pred_actions = 1'b1

                    // check for pred
                    if (fetch_resp_pred_present) begin

                        // check for complex branch
                        if (fetch_resp_selected_pred_info[7:6] == 2'b11) begin

                            // redo current fetch resp access in fetch req
                            fetch_req_access_PC_change = 1'b1;
                            fetch_req_access_PC_VA = fetch_resp_PC_VA;

                            // will get complex branch info next cycle
                            next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;

                            // save complex branch state
                            next_fetch_resp_saved_one_hot = fetch_resp_selected_one_hot;
                            next_fetch_resp_saved_cold_ack_mask = fetch_resp_selected_cold_ack_mask;
                            next_fetch_resp_saved_index = fetch_resp_selected_index;
                            next_fetch_resp_saved_pred_info = fetch_resp_selected_pred_info;
                            next_fetch_resp_saved_target = fetch_resp_selected_target;
                            next_fetch_resp_saved_LH = fetch_resp_selected_LH;

                            // no instr yields yet
                            fetch_resp_instr_yield = 1'b0;
                        end

                        // otherwise, branch or jump
                        else begin

                            // use predicted fetch resp access in fetch req
                            fetch_req_access_PC_change = 1'b1;
                            fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;

                            // yield instr's
                            fetch_resp_instr_yield = 1'b1;
                        end
                    end
                    // otherwise, simple move on
                    else begin

                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;
                    end
                end
            end

            FETCH_RESP_COMPLEX_BRANCH:
            begin
                // check for complex branch taken
                fetch_resp_check_complex_branch_taken = 1'b1;

                // check miss
                if (~ihit) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_change = 1'b1;
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;

                    // check itlb miss -> stay here
                    if (~itlb_resp_valid) begin
                    
                        // hold all complex branch state state
                        next_fetch_resp_saved_one_hot = fetch_resp_saved_one_hot;
                        next_fetch_resp_saved_cold_ack_mask = fetch_resp_saved_cold_ack_mask;
                        next_fetch_resp_saved_index = fetch_resp_saved_index;
                        next_fetch_resp_saved_pred_info = fetch_resp_saved_pred_info;
                        next_fetch_resp_saved_target = fetch_resp_saved_target;
                        next_fetch_resp_saved_LH = fetch_resp_saved_LH;

                        next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;
                    end
                    // otherwise, icache miss
                    else begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                end
                // if istream_stall_SENQ, hold all complex branch state
                else if (istream_stall_SENQ) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_change = 1'b1;
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                    
                    // hold all complex branch state
                    next_fetch_resp_saved_one_hot = fetch_resp_saved_one_hot;
                    next_fetch_resp_saved_cold_ack_mask = fetch_resp_saved_cold_ack_mask;
                    next_fetch_resp_saved_index = fetch_resp_saved_index;
                    next_fetch_resp_saved_pred_info = fetch_resp_saved_pred_info;
                    next_fetch_resp_saved_target = fetch_resp_saved_target;
                    next_fetch_resp_saved_LH = fetch_resp_saved_LH;
                end
                // if hit, continue using complex branch state
                else begin

                    // can perform pred actions
                    fetch_resp_perform_pred_actions = 1'b1
                    
                    // check this complex branch taken
                    if (fetch_resp_complex_branch_taken) begin

                        // use predicted fetch resp access in fetch req
                        fetch_req_access_PC_change = 1'b1;
                        fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;
                    
                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;

                        // back to active
                        next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    end
                    // else check for other pred
                    else if (fetch_resp_present) begin

                        // check for complex branch
                        if (fetch_resp_selected_pred_info[7:6] == 2'b11) begin

                            // redo current fetch resp access in fetch req
                            fetch_req_access_PC_change = 1'b1;
                            fetch_req_access_PC_VA = fetch_resp_PC_VA;

                            // will get complex branch info next cycle
                            next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;

                            // save complex branch state
                            next_fetch_resp_saved_one_hot = fetch_resp_selected_one_hot;
                            next_fetch_resp_saved_cold_ack_mask = fetch_resp_selected_cold_ack_mask;
                            next_fetch_resp_saved_index = fetch_resp_selected_index;
                            next_fetch_resp_saved_pred_info = fetch_resp_selected_pred_info;
                            next_fetch_resp_saved_target = fetch_resp_selected_target;
                            next_fetch_resp_saved_LH = fetch_resp_selected_LH;

                            // no instr yields yet
                            fetch_resp_instr_yield = 1'b0;
                        end

                        // otherwise, branch or jump
                        else begin

                            // use predicted fetch resp access in fetch req
                            fetch_req_access_PC_change = 1'b1;
                            fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;

                            // yield instr's
                            fetch_resp_instr_yield = 1'b1;

                            // back to active
                            next_fetch_resp_state = FETCH_RESP_ACTIVE;
                        end
                    end
                    // otherwise, simple move on
                    else begin

                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;

                        // back to active
                        next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    end
                end
            end

            FETCH_RESP_ICACHE_MISS:
            begin
                // check miss
                if (~ihit) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_change = 1'b1;
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;

                    // check itlb miss -> stay here
                    if (~itlb_resp_valid) begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                    // otherwise, icache miss
                    else begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                end
                // check istream stall with icache hit
                else if (istream_stall_SENQ) begin

                    // back to ACTIVE
                    next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_change = 1'b1;
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                end
                // otherwise, clean icache hit
                else begin

                    // back to ACTIVE
                    next_fetch_resp_state = FETCH_RESP_ACTIVE;

                    // can perform pred actions
                    fetch_resp_perform_pred_actions = 1'b1

                    // check for pred
                    if (fetch_resp_pred_present) begin

                        // check for complex branch
                        if (fetch_resp_selected_pred_info[7:6] == 2'b11) begin

                            // redo current fetch resp access in fetch req
                            fetch_req_access_PC_change = 1'b1;
                            fetch_req_access_PC_VA = fetch_resp_PC_VA;

                            // will get complex branch info next cycle
                            next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;

                            // save complex branch state
                            next_fetch_resp_saved_one_hot = fetch_resp_selected_one_hot;
                            next_fetch_resp_saved_cold_ack_mask = fetch_resp_selected_cold_ack_mask;
                            next_fetch_resp_saved_index = fetch_resp_selected_index;
                            next_fetch_resp_saved_pred_info = fetch_resp_selected_pred_info;
                            next_fetch_resp_saved_target = fetch_resp_selected_target;
                            next_fetch_resp_saved_LH = fetch_resp_selected_LH;

                            // no instr yields yet
                            fetch_resp_instr_yield = 1'b0;
                        end

                        // otherwise, branch or jump
                        else begin

                            // use predicted fetch resp access in fetch req
                            fetch_req_access_PC_change = 1'b1;
                            fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;

                            // yield instr's
                            fetch_resp_instr_yield = 1'b1;
                        end
                    end
                    // otherwise, simple move on
                    else begin

                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;
                    end
                end
            end

        endcase
    end

    // module connections:
    always_comb begin

        // lbpt:
        lbpt_valid_RESP = fetch_resp_selected_pred_info[7:6] == 2'b11;
        lbpt_full_PC_RESP = {fetch_resp_PC_VA[31:4], fetch_resp_selected_index, 1'b0};
        lbpt_LH_RESP = fetch_resp_selected_LH;
        lbpt_ASID_RESP = fetch_req_ASID;

        lbpt_update0_valid = ;
        lbpt_update0_start_full_PC = ;
        lbpt_update0_LH = ;
        lbpt_update0_ASID = ;
        lbpt_update0_taken = ;

        lbpt_update1_correct = ;

        // gbpt:
        gbpt_valid_RESP = fetch_resp_selected_pred_info[7:6] == 2'b11;
        gbpt_full_PC_RESP = {fetch_resp_PC_VA[31:4], fetch_resp_selected_index, 1'b0};;
        gbpt_GH_RESP = ghr;
        gbpt_ASID_RESP = fetch_req_ASID;
        
        gbpt_update0_valid = ;
        gbpt_update0_start_full_PC = ;
        gbpt_update0_GH = ;
        gbpt_update0_ASID = ;
        gbpt_update0_taken = ;

        gbpt_update1_correct = ;

        // upct:
        // upct_valid_RESP = ; // handled in pred-specific actions
        // upct_upct_index_RESP = ; // handled in pred-specific actions
        
        upct_update0_valid = ;
        upct_update0_start_full_PC = ;
        
        upct_update1_upct_index = ;

        // ras:
        // ras_link_RESP = ; // handled in pred-specific actions
        if (fetch_resp_selected_one_hot[7]) begin
            // use PC+16 if link on last instr in this 16B
            ras_link_full_PC_RESP = {fetch_req_PC_VA, {fetch_resp_selected_index + 3'h1}[2:0], 1'b0};
        end
        else begin
            // use next instr PC link
            ras_link_full_PC_RESP = {fetch_resp_PC_VA, {fetch_resp_selected_index + 3'h1}[2:0], 1'b0};
        end
        // ras_ret_RESP = ; // handled in pred-specific actions

        ras_update0_valid = ;
        ras_update0_ras_index = ;
    end


    // determine what rob branch updates to make to which modules based on pred info and if restarting vs. clearing

endmodule