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
    output logic                            icache_resp_notif_valid,
    output logic                            icache_resp_notif_miss,
    output logic [ICACHE_ASSOC-1:0]         icache_resp_notif_way,
    output logic [ICACHE_TAG_WIDTH-1:0]     icache_resp_notif_tag,

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
    input logic                             rob_restart_virtual_mode,
    input logic [1:0]                       rob_restart_exec_mode,
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

    // restart sources:
        // rob restart
        // decode restart

    // wait for restart from decode

    // ----------------------------------------------------------------
    // Signals:

    //////////////////////
    // Fetch Req Stage: //
    //////////////////////

    // state
    logic                   fetch_req_wait_for_restart_state, next_fetch_req_wait_for_restart_state;
    logic [VA_WIDTH-1:0]    fetch_req_PC_VA, next_fetch_req_PC_VA;
    logic [ASID_WIDTH-1:0]  fetch_req_ASID, next_fetch_req_ASID;
    logic                   fetch_req_virtual_mode, next_fetch_req_virtual_mode;

    // control
    logic fetch_req_valid;
    logic fetch_req_output_valid;
    // logic fetch_req_clear; // have all info in restarts
    logic fetch_req_stall;
        // stage valid (not in wait for restart state) AND:
            // valid fetch resp not moving on

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
    typedef enum logic [2:0] {
        FETCH_RESP_IDLE,
        FETCH_RESP_FIRST_CYCLE,
        FETCH_RESP_HIT_COMPLEX_BRANCH,
        FETCH_RESP_ITLB_MISS,
        FETCH_RESP_ICACHE_MISS
    } fetch_resp_state_t;

    fetch_resp_state_t fetch_resp_state, next_fetch_resp_state;

    // pipeline latch
    logic [VA_WIDTH-1:0] fetch_resp_PC_VA, next_fetch_resp_PC_VA;

    // control
    logic fetch_resp_stall;
        // going to stall fetch resp state
        // istream_stall_SENQ
    logic fetch_resp_output_valid;

    // translated PC
    logic [PA_WIDTH-1:0] fetch_resp_PC_PA;

    // ghr
    logic [GH_LENGTH-1:0] ghr, next_ghr;

    // pred logic
    logic TODO;

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
        logic [7:0]     istream_one_hot_redirect_by_fetch_2B_SENQ,;
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
    // Signals:

    //////////////////////
    // Fetch Req Stage: //
    //////////////////////

    // FF logic;
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_req_wait_for_restart_state <= 1'b0;
            fetch_req_PC_VA <= INIT_PC;
            fetch_req_ASID <= INIT_ASID;
            fetch_req_virtual_mode <= 1'b0;
        end
        else begin
            fetch_req_wait_for_restart_state <= next_fetch_req_wait_for_restart_state;
            fetch_req_PC_VA <= next_fetch_req_PC_VA;
            fetch_req_ASID <= next_fetch_req_ASID;
            fetch_req_virtual_mode <= next_fetch_req_virtual_mode;
        end
    end

    // next state logic:
    always_comb begin

        next_fetch_req_wait_for_restart_state = fetch_req_wait_for_restart_state;
        next_fetch_req_PC_VA = fetch_req_PC_VA;
        next_fetch_req_ASID = fetch_req_ASID;
        next_fetch_req_virtual_mode = fetch_req_virtual_mode;

        if (rob_restart_valid) begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            next_fetch_req_PC_VA = rob_restart_PC;
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
        else if (fetch_req_stall) begin
            next_fetch_req_wait_for_restart_state = 1'b0;
        end
        else begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            if (fetch_req_access_PC_change) begin
                next_fetch_req_PC_VA = {fetch_req_access_PC_VA[31:4] + 28'h1, 4'b0000};
            end
            else begin
                next_fetch_req_PC_VA = {fetch_req_PC_VA[31:4] + 28'h1, 4'b0000};
            end
        end
    end

    // next pipeline latch
    always_comb begin
        next_fetch_resp_PC_VA = fetch_req_access_PC_VA;
    end

    // control
    always_comb begin
        fetch_req_stall = fetch_resp_stall;
        fetch_req_valid = ~fetch_req_wait_for_restart_state;
        fetch_req_output_valid = fetch_req_valid & ~fetch_req_stall;
    end

    // interruptable access PC
    always_comb begin
        fetch_req_access_PC_change = 1'b0;
        fetch_req_access_PC_VA = fetch_req_PC_VA;
    end

    // module connections:
    always_comb begin

        // btb:
        btb_valid_REQ = fetch_req_output_valid;
        btb_full_PC_REQ = fetch_req_access_PC_VA;
        btb_ASID_REQ = fetch_req_ASID;
        
        btb_update0_valid = 
        btb_update0_start_full_PC = 
        btb_update0_ASID = 

        btb_update1_pred_info = 
        btb_update1_pred_lru = 
        btb_update1_target_full_PC = 

        // lht:
        lht_valid_REQ = fetch_req_output_valid;
        lht_full_PC_REQ = fetch_req_access_PC_VA;
        lht_ASID_REQ = fetch_req_ASID;

        lht_update0_valid = 
        lht_update0_start_full_PC = 
        lht_update0_ASID = 
        lht_update0_LH = 

        // mdpt:
        mdpt_valid_REQ = fetch_req_output_valid;
        mdpt_full_PC_REQ = fetch_req_access_PC_VA;
        mdpt_ASID_REQ = fetch_req_ASID;

        mdpt_mdpt_update0_valid = 
        mdpt_mdpt_update0_start_full_PC = 
        mdpt_mdpt_update0_ASID = 
        mdpt_mdpt_update0_mdp_info = 

        // itlb:
        itlb_req_valid = fetch_req_output_valid;
        itlb_req_virtual_mode = fetch_req_virtual_mode;
        itlb_req_vpn = fetch_req_access_PC_VA;
        itlb_req_ASID = fetch_req_ASID;

        // icache:
        icache_req_valid = fetch_req_output_valid;
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
            fetch_resp_state <= next_fetch_resp_state;
            ghr <= next_ghr;
        end
    end

    // pipeline latch logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_resp_PC_VA <= 32'h0;
        end
        else begin
            if (rob_restart_valid) begin
                fetch_resp_PC_VA <= rob_restart_PC;
            end
            else if (decode_restart_valid) begin
                fetch_resp_PC_VA <= decode_restart_PC;
            end
            else if (~fetch_resp_stall) begin
                fetch_resp_PC_VA <= next_fetch_resp_PC_VA;
            end
        end
    end

    // pred logic + state machine
    always_comb begin

        fetch_resp_PC_PA = {itlb_resp_ppn, fetch_resp_PC_VA[PO_WIDTH-1:0]};

        next_fetch_resp_state = fetch_resp_state;
        fetch_resp_stall = 1'b0;
        fetch_resp_output_valid = 1'b0;
        next_ghr = ghr;

        case (fetch_resp_state)

            FETCH_RESP_IDLE:
            begin
                if (fetch_req_valid) begin
                    next_fetch_resp_state = FETCH_RESP_FIRST_CYCLE;
                end
            end

            FETCH_RESP_FIRST_CYCLE:
            begin

            end

            FETCH_RESP_HIT_COMPLEX_BRANCH:
            begin

            end

            FETCH_RESP_MISS:
            begin

            end
        endcase
    end

endmodule