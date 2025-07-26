/*
    Filename: stamofu_cq.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Central Queue
    Spec: LOROF/spec/design/stamofu_cq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_cq #(
    parameter STAMOFU_CQ_ENTRIES = 24,
    parameter LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to central queue
    input logic                                 stamofu_cq_enq_valid,
    input logic                                 stamofu_cq_enq_killed,
    input logic                                 stamofu_cq_enq_is_store,
    input logic                                 stamofu_cq_enq_is_amo,
    input logic                                 stamofu_cq_enq_is_fence,
    input logic [3:0]                           stamofu_cq_enq_op,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_cq_enq_mdp_info,
    input logic                                 stamofu_cq_enq_mem_aq,
    input logic                                 stamofu_cq_enq_io_aq,
    input logic                                 stamofu_cq_enq_mem_rl,
    input logic                                 stamofu_cq_enq_io_rl,
    input logic [LOG_PR_COUNT-1:0]              stamofu_cq_enq_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_cq_enq_ROB_index,

    // central queue enqueue feedback
    output logic                                stamofu_cq_enq_ready,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_cq_enq_index,

    // central queue info grab
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_grab_bank0_cq_index,
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_cq_info_grab_bank0_mdp_info,
    output logic                                stamofu_cq_info_grab_bank0_mem_aq,
    output logic                                stamofu_cq_info_grab_bank0_io_aq,
    output logic                                stamofu_cq_info_grab_bank0_mem_rl,
    output logic                                stamofu_cq_info_grab_bank0_io_rl,
    output logic [LOG_ROB_ENTRIES-1:0]          stamofu_cq_info_grab_bank0_ROB_index,
    
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_grab_bank1_cq_index,
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_cq_info_grab_bank1_mdp_info,
    output logic                                stamofu_cq_info_grab_bank1_mem_aq,
    output logic                                stamofu_cq_info_grab_bank1_io_aq,
    output logic                                stamofu_cq_info_grab_bank1_mem_rl,
    output logic                                stamofu_cq_info_grab_bank1_io_rl,
    output logic [LOG_ROB_ENTRIES-1:0]          stamofu_cq_info_grab_bank1_ROB_index,

    // central queue info ret
    input logic                                 stamofu_cq_info_ret_bank0_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_ret_bank0_cq_index,
    input logic                                 stamofu_cq_info_ret_bank0_dtlb_hit,
    input logic                                 stamofu_cq_info_ret_bank0_page_fault,
    input logic                                 stamofu_cq_info_ret_bank0_access_fault,
    input logic                                 stamofu_cq_info_ret_bank0_is_mem,
    input logic                                 stamofu_cq_info_ret_bank0_mem_aq,
    input logic                                 stamofu_cq_info_ret_bank0_io_aq,
    input logic                                 stamofu_cq_info_ret_bank0_mem_rl,
    input logic                                 stamofu_cq_info_ret_bank0_io_rl,
    input logic                                 stamofu_cq_info_ret_bank0_misaligned,
    input logic                                 stamofu_cq_info_ret_bank0_misaligned_exception,
    input logic [PA_WIDTH-2-1:0]                stamofu_cq_info_ret_bank0_PA_word,
    input logic [3:0]                           stamofu_cq_info_ret_bank0_byte_mask,
    input logic [31:0]                          stamofu_cq_info_ret_bank0_data,
    
    input logic                                 stamofu_cq_info_ret_bank1_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_ret_bank1_cq_index,
    input logic                                 stamofu_cq_info_ret_bank1_dtlb_hit,
    input logic                                 stamofu_cq_info_ret_bank1_page_fault,
    input logic                                 stamofu_cq_info_ret_bank1_access_fault,
    input logic                                 stamofu_cq_info_ret_bank1_is_mem,
    input logic                                 stamofu_cq_info_ret_bank1_mem_aq,
    input logic                                 stamofu_cq_info_ret_bank1_io_aq,
    input logic                                 stamofu_cq_info_ret_bank1_mem_rl,
    input logic                                 stamofu_cq_info_ret_bank1_io_rl,
    input logic                                 stamofu_cq_info_ret_bank1_misaligned,
    input logic                                 stamofu_cq_info_ret_bank1_misaligned_exception,
    input logic [PA_WIDTH-2-1:0]                stamofu_cq_info_ret_bank1_PA_word,
    input logic [3:0]                           stamofu_cq_info_ret_bank1_byte_mask,
    input logic [31:0]                          stamofu_cq_info_ret_bank1_data,

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
    input logic                                 stamofu_mq_info_ret_bank0_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank0_cq_index,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank0_mq_index,
    
    input logic                                 stamofu_mq_info_ret_bank1_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank1_cq_index,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank1_mq_index,

    // dtlb miss resp
    input logic                                 dtlb_miss_resp_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    dtlb_miss_resp_cq_index,
    input logic                                 dtlb_miss_resp_is_mq,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    dtlb_miss_resp_mq_index, // unused
    input logic [PPN_WIDTH-1:0]                 dtlb_miss_resp_PPN,
    input logic                                 dtlb_miss_resp_is_mem,
    input logic                                 dtlb_miss_resp_page_fault,
    input logic                                 dtlb_miss_resp_access_fault,

    // ldu CAM launch
    output logic                                ldu_CAM_launch_valid,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   ldu_CAM_launch_cq_index, // stamofu_cq index
    output logic                                ldu_CAM_launch_is_mq,
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   ldu_CAM_launch_mq_index, // stamofu_mq index
    output logic                                ldu_CAM_launch_is_amo,
    output logic [PA_WIDTH-2-1:0]               ldu_CAM_launch_PA_word,
    output logic [3:0]                          ldu_CAM_launch_byte_mask,
    output logic [31:0]                         ldu_CAM_launch_write_data,
    output logic [MDPT_INFO_WIDTH-1:0]          ldu_CAM_launch_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]          ldu_CAM_launch_ROB_index,

    // ldu CAM launch feedback
        // externally select stamofu_cq vs. stamofu_mq launch this cycle
        // not ready if doing mq this cycle
    input logic                                 ldu_CAM_launch_ready,

    // ldu CAM return
    input logic                                 ldu_CAM_return_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    ldu_CAM_return_cq_index, // stamofu_cq index
    input logic                                 ldu_CAM_return_is_mq,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    ldu_CAM_return_mq_index, // stamofu_mq index
    input logic                                 ldu_CAM_return_forward,

    // stamofu CAM launch
    input logic                                 stamofu_CAM_launch_bank0_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_launch_bank0_cq_index,  // ldu_cq index
    input logic                                 stamofu_CAM_launch_bank0_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_launch_bank0_mq_index,  // ldu_mq index
    input logic [PA_WIDTH-2-1:0]                stamofu_CAM_launch_bank0_PA_word,
    input logic [3:0]                           stamofu_CAM_launch_bank0_byte_mask,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_CAM_launch_bank0_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_launch_bank0_mdp_info,

    input logic                                 stamofu_CAM_launch_bank1_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_launch_bank1_cq_index,  // ldu_cq index
    input logic                                 stamofu_CAM_launch_bank1_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_launch_bank1_mq_index,  // ldu_mq index
    input logic [PA_WIDTH-2-1:0]                stamofu_CAM_launch_bank1_PA_word,
    input logic [3:0]                           stamofu_CAM_launch_bank1_byte_mask,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_CAM_launch_bank1_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_launch_bank1_mdp_info,

    // stamofu_mq CAM stage 2 info
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_mq_CAM_return_bank0_updated_mdp_info,
    input logic                                 stamofu_mq_CAM_return_bank0_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_CAM_return_bank0_stall_count,
    input logic [3:0]                           stamofu_mq_CAM_return_bank0_forward,
    input logic                                 stamofu_mq_CAM_return_bank0_nasty_forward,
    input logic                                 stamofu_mq_CAM_return_bank0_forward_ROB_index,
    input logic [31:0]                          stamofu_mq_CAM_return_bank0_forward_data,
    
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_mq_CAM_return_bank1_updated_mdp_info,
    input logic                                 stamofu_mq_CAM_return_bank1_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_CAM_return_bank1_stall_count,
    input logic [3:0]                           stamofu_mq_CAM_return_bank1_forward,
    input logic                                 stamofu_mq_CAM_return_bank1_nasty_forward,
    input logic                                 stamofu_mq_CAM_return_bank1_forward_ROB_index,
    input logic [31:0]                          stamofu_mq_CAM_return_bank1_forward_data,

    // stamofu CAM return
    output logic                                stamofu_CAM_return_bank0_valid,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]       stamofu_CAM_return_bank0_cq_index, // ldu_cq index
    output logic                                stamofu_CAM_return_bank0_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]       stamofu_CAM_return_bank0_mq_index, // ldu_mq index, unused
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_CAM_return_bank0_updated_mdp_info,
    output logic                                stamofu_CAM_return_bank0_stall,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_CAM_return_bank0_stall_count,
    output logic [3:0]                          stamofu_CAM_return_bank0_forward,
    output logic                                stamofu_CAM_return_bank0_nasty_forward,
    output logic                                stamofu_CAM_return_bank0_forward_ROB_index,
    output logic [31:0]                         stamofu_CAM_return_bank0_forward_data,
    
    output logic                                stamofu_CAM_return_bank1_valid,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]       stamofu_CAM_return_bank1_cq_index, // ldu_cq index
    output logic                                stamofu_CAM_return_bank1_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]       stamofu_CAM_return_bank1_mq_index, // ldu_mq index, unused
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_CAM_return_bank1_updated_mdp_info,
    output logic                                stamofu_CAM_return_bank1_stall,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_CAM_return_bank1_stall_count,
    output logic [3:0]                          stamofu_CAM_return_bank1_forward,
    output logic                                stamofu_CAM_return_bank1_nasty_forward,
    output logic                                stamofu_CAM_return_bank1_forward_ROB_index,
    output logic [31:0]                         stamofu_CAM_return_bank1_forward_data,

    // misaligned queue info grab
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   stamofu_mq_info_grab_mq_index,
    output logic                                stamofu_mq_info_grab_clear_entry,
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)   
    input logic [PA_WIDTH-2-1:0]                stamofu_mq_info_grab_PA_word,
    input logic [3:0]                           stamofu_mq_info_grab_byte_mask,
    input logic [31:0]                          stamofu_mq_info_grab_data,

    // write buffer enq
    output logic                    wr_buf_enq_valid,
    output logic                    wr_buf_enq_is_amo,
    output logic [3:0]              wr_buf_enq_op,
    output logic                    wr_buf_enq_is_mem,
    output logic [PA_WIDTH-2-1:0]   wr_buf_enq_PA_word,
    output logic [3:0]              wr_buf_enq_byte_mask,
    output logic [31:0]             wr_buf_enq_data,

    // write buffer enq feedback
    input logic                     wr_buf_ready,
    input logic                     wr_buf_mem_present,
    input logic                     wr_buf_io_present,

    // fence restart notification to ROB
    output logic                        fence_restart_notif_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  fence_restart_notif_ROB_index,

    // exception to ROB
    output logic                        rob_exception_valid,
    output logic [VA_WIDTH-1:0]         rob_exception_VA,
    output logic                        rob_exception_is_lr,
    output logic                        rob_exception_page_fault,
    output logic                        rob_exception_access_fault,
    output logic                        rob_exception_misaligned_exception,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_exception_ROB_index,

    // exception backpressure from ROB
    input logic                         rob_exception_ready,

    // store set commit update
        // implied no dep
    output logic                        ssu_commit_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_commit_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_commit_update_ROB_index,

    // oldest stamofu advertisement
    output logic                        stamofu_active,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_oldest_ROB_index,

    // stamofu mq complete notif
    input logic                                 stamofu_mq_complete_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_complete_cq_index,

    // ROB complete notif
    output logic                        stamofu_complete_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_complete_ROB_index,

    // op dequeue from acquire queue
    output logic                        stamofu_aq_deq_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_deq_ROB_index,

    // ROB commit
    input logic [LOG_ROB_ENTRIES-3:0]   rob_commit_upper_index,
    input logic [3:0]                   rob_commit_lower_index_valid_mask,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

    // cq needs to be nosey if mq gets page fault or access fault so knows to raise exception

    // ----------------------------------------------------------------
    // Signals:

    typedef struct packed {
        logic                               valid;
        logic                               misaligned;
        logic                               misaligned_complete;
        logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  mq_index;
        logic                               killed;
        logic                               dtlb_hit;
        logic                               forward;
        logic                               committed;
        logic                               ldu_CAM_launch_req;
        logic                               ldu_CAM_launch_sent;
        logic                               ldu_CAM_launch_returned;
        logic                               complete_req;
        logic                               complete;
        logic                               exception_req;
        logic                               exception_sent;
        logic                               is_mem;
        logic                               mem_aq;
        logic                               io_aq;
        logic                               mem_rl;
        logic                               io_rl;
        logic                               page_fault;
        logic                               access_fault;
        logic                               misaligned_exception;
        logic                               is_store;
        logic                               is_amo;
        logic                               is_fence;
        logic [3:0]                         op;
        logic                               mdp_present;
        logic [MDPT_INFO_WIDTH-1:0]         mdp_info;
        logic [LOG_PR_COUNT-1:0]            dest_PR;
        logic [LOG_ROB_ENTRIES-1:0]         ROB_index;
        logic [3:0]                         lower_ROB_index_one_hot;
        logic [PA_WIDTH-3:0]                PA_word;
        logic [3:0]                         byte_mask;
        logic [31:0]                        data;
    } entry_t;

    entry_t [STAMOFU_CQ_ENTRIES-1:0] entry_array, next_entry_array;

    logic [LOG_STAMOFU_CQ_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    logic enq_perform;
    logic deq_perform;

    // demux's
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_ret_bank0_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_info_ret_bank1_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_info_ret_bank0_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_info_ret_bank1_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] dtlb_miss_resp_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_return_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_complete_valid_by_entry;

    logic [STAMOFU_CQ_ENTRIES-1:0] wraparound_mask;

    // req pe's
    logic [STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_launch_unmasked_req_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] rob_exception_unmasked_req_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_complete_unmasked_req_by_entry;
    
    logic [STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_launch_unmasked_req_ack_one_hot_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] rob_exception_unmasked_req_ack_one_hot_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_complete_unmasked_req_ack_one_hot_by_entry;
    
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  ldu_CAM_launch_unmasked_req_ack_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  rob_exception_unmasked_req_ack_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stamofu_complete_unmasked_req_ack_index;
    
    logic [STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_launch_masked_req_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] rob_exception_masked_req_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_complete_masked_req_by_entry;
    
    logic [STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_launch_masked_req_ack_one_hot_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] rob_exception_masked_req_ack_one_hot_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_complete_masked_req_ack_one_hot_by_entry;
    
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  ldu_CAM_launch_masked_req_ack_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  rob_exception_masked_req_ack_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stamofu_complete_masked_req_ack_index;
    
    logic [STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_launch_final_req_ack_one_hot_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] rob_exception_final_req_ack_one_hot_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_complete_final_req_ack_one_hot_by_entry;
    
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  ldu_CAM_launch_final_req_ack_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  rob_exception_final_req_ack_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stamofu_complete_final_req_ack_index;

    logic [LOG_STAMOFU_CQ_ENTRIES-1:0] rob_exception_cq_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_complete_cq_index;

    logic [STAMOFU_CQ_ENTRIES-1:0] rel_ROB_index_by_entry;

    // stamofu CAM pipeline bank 0
    logic                               CAM_stage0_bank0_valid;
    
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_addr_match_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_byte_overlap_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_older_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_mdp_match_by_entry;
    
    logic                               CAM_stage1_bank0_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_return_cq_index; // ldu_cq index
    logic                               CAM_stage1_bank0_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_return_mq_index; // ldu_mq index, unused

    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_unmasked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_masked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_mdp_match_by_entry;
                       
    logic                               CAM_stage1_bank0_found_forward;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_selected_one_hot_by_entry;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank0_load_selected_index;   
    logic                               CAM_stage1_bank0_load_is_subset;
    logic                               CAM_stage1_bank0_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank0_stall_count;

    logic                               CAM_stage2_bank0_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage2_bank0_return_cq_index; // ldu_cq index
    logic                               CAM_stage2_bank0_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage2_bank0_return_mq_index; // ldu_mq index, unused

    logic                               CAM_stage2_bank0_found_forward;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage2_bank0_load_selected_one_hot_by_entry;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank0_load_selected_index;   
    logic                               CAM_stage2_bank0_load_is_subset;
    logic                               CAM_stage2_bank0_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank0_stall_count;

    logic [MDPT_INFO_WIDTH-1:0]         CAM_stage2_bank0_updated_mdp_info;
    logic                               CAM_stage2_bank0_forward;
    logic                               CAM_stage2_bank0_nasty_forward;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank0_forward_ROB_index;
    logic [31:0]                        CAM_stage2_bank0_forward_data;
    
    // stamofu CAM pipeline bank 1
    logic                               CAM_stage0_bank1_valid;
    
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_addr_match_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_byte_overlap_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_older_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_mdp_match_by_entry;
    
    logic                               CAM_stage1_bank1_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_return_cq_index; // ldu_cq index
    logic                               CAM_stage1_bank1_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_return_mq_index; // ldu_mq index, unused

    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_unmasked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_masked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_mdp_match_by_entry;
                       
    logic                               CAM_stage1_bank1_found_forward;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_selected_one_hot_by_entry;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank1_load_selected_index;   
    logic                               CAM_stage1_bank1_load_is_subset;
    logic                               CAM_stage1_bank1_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank1_stall_count;

    logic                               CAM_stage2_bank1_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage2_bank1_return_cq_index; // ldu_cq index
    logic                               CAM_stage2_bank1_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage2_bank1_return_mq_index; // ldu_mq index, unused

    logic                               CAM_stage2_bank1_found_forward;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage2_bank1_load_selected_one_hot_by_entry;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank1_load_selected_index;   
    logic                               CAM_stage2_bank1_load_is_subset;
    logic                               CAM_stage2_bank1_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank1_stall_count;

    logic [MDPT_INFO_WIDTH-1:0]         CAM_stage2_bank1_updated_mdp_info;
    logic                               CAM_stage2_bank1_forward;
    logic                               CAM_stage2_bank1_nasty_forward;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank1_forward_ROB_index;
    logic [31:0]                        CAM_stage2_bank1_forward_data;

    // ----------------------------------------------------------------
    // Logic:

    assign enq_ptr_plus_1 = (enq_ptr == STAMOFU_CQ_ENTRIES-1) ? 0 : enq_ptr + 1;
    assign deq_ptr_plus_1 = (deq_ptr == STAMOFU_CQ_ENTRIES-1) ? 0 : deq_ptr + 1;

    // event demux to entry
    always_comb begin
        stamofu_cq_info_ret_bank0_valid_by_entry = '0;
        stamofu_cq_info_ret_bank1_valid_by_entry = '0;
        stamofu_mq_info_ret_bank0_valid_by_entry = '0;
        stamofu_mq_info_ret_bank1_valid_by_entry = '0;
        dtlb_miss_resp_valid_by_entry = '0;
        ldu_CAM_return_valid_by_entry = '0;
        stamofu_mq_complete_valid_by_entry = '0;

        stamofu_cq_info_ret_bank0_valid_by_entry[stamofu_cq_info_ret_bank0_cq_index] = stamofu_cq_info_ret_bank0_valid;
        stamofu_cq_info_ret_bank1_valid_by_entry[stamofu_cq_info_ret_bank1_cq_index] = stamofu_cq_info_ret_bank1_valid;
        stamofu_mq_info_ret_bank0_valid_by_entry[stamofu_mq_info_ret_bank0_cq_index] = stamofu_mq_info_ret_bank0_valid;
        stamofu_mq_info_ret_bank1_valid_by_entry[stamofu_mq_info_ret_bank1_cq_index] = stamofu_mq_info_ret_bank1_valid;
        dtlb_miss_resp_valid_by_entry[dtlb_miss_resp_cq_index] = dtlb_miss_resp_valid & ~dtlb_miss_resp_is_mq;
        ldu_CAM_return_valid_by_entry[ldu_CAM_return_cq_index] = ldu_CAM_return_valid & ~ldu_CAM_return_is_mq;
        stamofu_mq_complete_valid_by_entry[stamofu_mq_complete_cq_index] = stamofu_mq_complete_valid;
    end

    // request PE's
    always_comb begin
        for (int i = 0; i < STAMOFU_CQ_ENTRIES; i++) begin
            ldu_CAM_launch_unmasked_req_by_entry[i] = entry_array[i].ldu_CAM_launch_req;
            rob_exception_unmasked_req_by_entry[i] = entry_array[i].exception_req;
            stamofu_complete_unmasked_req_by_entry[i] = entry_array[i].complete_req;
        end
        ldu_CAM_launch_masked_req_by_entry = ldu_CAM_launch_unmasked_req_by_entry & wraparound_mask;
        rob_exception_masked_req_by_entry = rob_exception_unmasked_req_by_entry & wraparound_mask;
        stamofu_complete_masked_req_by_entry = stamofu_complete_unmasked_req_by_entry & wraparound_mask;
    end
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) CAM_LAUNCH_UNMASKED_PE (
        .req_vec(ldu_CAM_launch_unmasked_req_by_entry),
        .ack_one_hot(ldu_CAM_launch_unmasked_req_ack_one_hot_by_entry),
        .ack_index(ldu_CAM_launch_unmasked_req_ack_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) CAM_LAUNCH_MASKED_PE (
        .req_vec(ldu_CAM_launch_masked_req_by_entry),
        .ack_one_hot(ldu_CAM_launch_masked_req_ack_one_hot_by_entry),
        .ack_index(ldu_CAM_launch_masked_req_ack_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) ROB_EXCEPTION_UNMASKED_PE (
        .req_vec(rob_exception_unmasked_req_by_entry),
        .ack_one_hot(rob_exception_unmasked_req_ack_one_hot_by_entry),
        .ack_index(rob_exception_unmasked_req_ack_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) ROB_EXCEPTION_MASKED_PE (
        .req_vec(rob_exception_masked_req_by_entry),
        .ack_one_hot(rob_exception_masked_req_ack_one_hot_by_entry),
        .ack_index(rob_exception_masked_req_ack_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) STAMOFU_COMPLETE_UNMASKED_PE (
        .req_vec(stamofu_complete_unmasked_req_by_entry),
        .ack_one_hot(stamofu_complete_unmasked_req_ack_one_hot_by_entry),
        .ack_index(stamofu_complete_unmasked_req_ack_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) STAMOFU_COMPLETE_MASKED_PE (
        .req_vec(stamofu_complete_masked_req_by_entry),
        .ack_one_hot(stamofu_complete_masked_req_ack_one_hot_by_entry),
        .ack_index(stamofu_complete_masked_req_ack_index)
    );
    always_comb begin
        if (|ldu_CAM_launch_masked_req_by_entry) begin
            ldu_CAM_launch_final_req_ack_one_hot_by_entry = ldu_CAM_launch_masked_req_ack_one_hot_by_entry;
            ldu_CAM_launch_final_req_ack_index = ldu_CAM_launch_masked_req_ack_index;
        end else begin
            ldu_CAM_launch_final_req_ack_one_hot_by_entry = ldu_CAM_launch_unmasked_req_ack_one_hot_by_entry;
            ldu_CAM_launch_final_req_ack_index = ldu_CAM_launch_unmasked_req_ack_index;
        end
        if (|rob_exception_masked_req_by_entry) begin
            rob_exception_final_req_ack_one_hot_by_entry = rob_exception_masked_req_ack_one_hot_by_entry;
            rob_exception_final_req_ack_index = rob_exception_masked_req_ack_index;
        end else begin
            rob_exception_final_req_ack_one_hot_by_entry = rob_exception_unmasked_req_ack_one_hot_by_entry;
            rob_exception_final_req_ack_index = rob_exception_unmasked_req_ack_index;
        end
        if (|stamofu_complete_masked_req_by_entry) begin
            stamofu_complete_final_req_ack_one_hot_by_entry = stamofu_complete_masked_req_ack_one_hot_by_entry;
            stamofu_complete_final_req_ack_index = stamofu_complete_masked_req_ack_index;
        end else begin
            stamofu_complete_final_req_ack_one_hot_by_entry = stamofu_complete_unmasked_req_ack_one_hot_by_entry;
            stamofu_complete_final_req_ack_index = stamofu_complete_unmasked_req_ack_index;
        end
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            ldu_CAM_launch_valid <= 1'b0;
            ldu_CAM_launch_cq_index <= '0;
        end
        else if (ldu_CAM_launch_ready) begin
            ldu_CAM_launch_valid <= |ldu_CAM_launch_unmasked_req_by_entry;
            ldu_CAM_launch_cq_index <= ldu_CAM_launch_final_req_ack_index;
        end
    end
    always_comb begin
        ldu_CAM_launch_is_mq = 1'b0;
        ldu_CAM_launch_mq_index = '0;
        ldu_CAM_launch_is_amo = entry_array[ldu_CAM_launch_cq_index].is_amo;
        ldu_CAM_launch_PA_word = entry_array[ldu_CAM_launch_cq_index].PA_word;
        ldu_CAM_launch_byte_mask = entry_array[ldu_CAM_launch_cq_index].byte_mask;
        ldu_CAM_launch_write_data = entry_array[ldu_CAM_launch_cq_index].data;
        ldu_CAM_launch_mdp_info = entry_array[ldu_CAM_launch_cq_index].mdp_info;
        ldu_CAM_launch_ROB_index = entry_array[ldu_CAM_launch_cq_index].ROB_index;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            rob_exception_valid <= 1'b0;
            rob_exception_cq_index <= '0;
        end
        else if (~rob_exception_ready) begin
            rob_exception_valid <= |rob_exception_unmasked_req_by_entry;
            rob_exception_cq_index <= rob_exception_final_req_ack_index;
        end
    end
    always_comb begin
        rob_exception_VA[31:2] = entry_array[rob_exception_cq_index].PA_word[29:0];
        case (entry_array[rob_exception_cq_index].byte_mask)
            4'b???1:    rob_exception_VA[1:0] = 2'h0;
            4'b??10:    rob_exception_VA[1:0] = 2'h1;
            4'b?100:    rob_exception_VA[1:0] = 2'h2;
            4'b1000:    rob_exception_VA[1:0] = 2'h3;
        endcase
        rob_exception_is_lr = 
            entry_array[rob_exception_cq_index].is_amo
            & (entry_array[rob_exception_cq_index].op == 4'b0010);
        rob_exception_page_fault = entry_array[rob_exception_cq_index].page_fault;
        rob_exception_access_fault = entry_array[rob_exception_cq_index].access_fault;
        rob_exception_misaligned_exception = entry_array[rob_exception_cq_index].misaligned_exception;
        rob_exception_ROB_index = entry_array[rob_exception_cq_index].ROB_index;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            stamofu_complete_valid <= 1'b0;
            stamofu_complete_cq_index <= '0;
        end
        else begin
            stamofu_complete_valid <= |stamofu_complete_unmasked_req_by_entry;
            stamofu_complete_cq_index <= stamofu_complete_final_req_ack_index;
        end
    end
    always_comb begin
        stamofu_complete_ROB_index = entry_array[stamofu_complete_cq_index].ROB_index;
    end

    // per-entry state machine
    always_comb begin
        next_entry_array = entry_array;

        for (int i = 0; i < STAMOFU_CQ_ENTRIES; i++) begin
            rel_ROB_index_by_entry[i] = entry_array[i].ROB_index - rob_kill_abs_head_index;

            // events with priority
                // stamofu_cq ret bank 0
                // stamofu_cq ret bank 1
                // dtlb miss resp
                // ldu CAM return
            
            // stamofu_cq ret bank 0
            if (stamofu_cq_info_ret_bank0_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                next_entry_array[i].misaligned = stamofu_cq_info_ret_bank0_misaligned;
                // next_entry_array[i].misaligned_complete = 
                // next_entry_array[i].mq_index = 
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = stamofu_cq_info_ret_bank0_dtlb_hit;
                // next_entry_array[i].forward = 
                // next_entry_array[i].committed = 
                // next_entry_array[i].ldu_CAM_launch_req = 
                // next_entry_array[i].ldu_CAM_launch_sent = 
                // next_entry_array[i].ldu_CAM_launch_returned = 
                // next_entry_array[i].complete_req = 
                // next_entry_array[i].complete = 
                // next_entry_array[i].exception_req = 
                // next_entry_array[i].exception_sent = 
                if (
                    stamofu_cq_info_ret_bank0_dtlb_hit
                    & (
                        stamofu_cq_info_ret_bank0_page_fault
                        | stamofu_cq_info_ret_bank0_access_fault
                        | stamofu_cq_info_ret_bank0_misaligned_exception)
                ) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                    next_entry_array[i].exception_req = 1'b1;
                end
                else if (stamofu_cq_info_ret_bank0_dtlb_hit) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b1;
                    next_entry_array[i].exception_req = 1'b0;
                end
                next_entry_array[i].is_mem = stamofu_cq_info_ret_bank0_is_mem;
                next_entry_array[i].mem_aq = stamofu_cq_info_ret_bank0_mem_aq;
                next_entry_array[i].io_aq = stamofu_cq_info_ret_bank0_io_aq;
                next_entry_array[i].mem_rl = stamofu_cq_info_ret_bank0_mem_rl;
                next_entry_array[i].io_rl = stamofu_cq_info_ret_bank0_io_rl;
                next_entry_array[i].page_fault = stamofu_cq_info_ret_bank0_page_fault;
                next_entry_array[i].access_fault = stamofu_cq_info_ret_bank0_access_fault;
                next_entry_array[i].misaligned_exception = stamofu_cq_info_ret_bank0_misaligned_exception;
                // next_entry_array[i].is_store = 
                // next_entry_array[i].is_amo = 
                // next_entry_array[i].is_fence = 
                // next_entry_array[i].op = 
                // next_entry_array[i].mdp_present = 
                // next_entry_array[i].mdp_info = 
                // next_entry_array[i].dest_PR = 
                // next_entry_array[i].ROB_index = 
                // next_entry_array[i].lower_ROB_index_one_hot = 
                next_entry_array[i].PA_word = stamofu_cq_info_ret_bank0_PA_word;
                next_entry_array[i].byte_mask = stamofu_cq_info_ret_bank0_byte_mask;
                next_entry_array[i].data = stamofu_cq_info_ret_bank0_data;
            end
            // stamofu_cq ret bank 1
            else if (stamofu_cq_info_ret_bank1_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                next_entry_array[i].misaligned = stamofu_cq_info_ret_bank1_misaligned;
                // next_entry_array[i].misaligned_complete = 
                // next_entry_array[i].mq_index = 
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = stamofu_cq_info_ret_bank1_dtlb_hit;
                // next_entry_array[i].forward = 
                // next_entry_array[i].committed = 
                // next_entry_array[i].ldu_CAM_launch_req = 
                // next_entry_array[i].ldu_CAM_launch_sent = 
                // next_entry_array[i].ldu_CAM_launch_returned = 
                // next_entry_array[i].complete_req = 
                // next_entry_array[i].complete = 
                // next_entry_array[i].exception_req = 
                // next_entry_array[i].exception_sent = 
                if (
                    stamofu_cq_info_ret_bank1_dtlb_hit
                    & (
                        stamofu_cq_info_ret_bank1_page_fault
                        | stamofu_cq_info_ret_bank1_access_fault
                        | stamofu_cq_info_ret_bank1_misaligned_exception)
                ) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                    next_entry_array[i].exception_req = 1'b1;
                end
                else if (stamofu_cq_info_ret_bank1_dtlb_hit) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b1;
                    next_entry_array[i].exception_req = 1'b0;
                end
                next_entry_array[i].is_mem = stamofu_cq_info_ret_bank1_is_mem;
                next_entry_array[i].mem_aq = stamofu_cq_info_ret_bank1_mem_aq;
                next_entry_array[i].io_aq = stamofu_cq_info_ret_bank1_io_aq;
                next_entry_array[i].mem_rl = stamofu_cq_info_ret_bank1_mem_rl;
                next_entry_array[i].io_rl = stamofu_cq_info_ret_bank1_io_rl;
                next_entry_array[i].page_fault = stamofu_cq_info_ret_bank1_page_fault;
                next_entry_array[i].access_fault = stamofu_cq_info_ret_bank1_access_fault;
                next_entry_array[i].misaligned_exception = stamofu_cq_info_ret_bank1_misaligned_exception;
                // next_entry_array[i].is_store = 
                // next_entry_array[i].is_amo = 
                // next_entry_array[i].is_fence = 
                // next_entry_array[i].op = 
                // next_entry_array[i].mdp_present = 
                // next_entry_array[i].mdp_info = 
                // next_entry_array[i].dest_PR = 
                // next_entry_array[i].ROB_index = 
                // next_entry_array[i].lower_ROB_index_one_hot = 
                next_entry_array[i].PA_word = stamofu_cq_info_ret_bank1_PA_word;
                next_entry_array[i].byte_mask = stamofu_cq_info_ret_bank1_byte_mask;
                next_entry_array[i].data = stamofu_cq_info_ret_bank1_data;
            end
            // dtlb miss resp
            else if (dtlb_miss_resp_valid_by_entry[i]) begin
                next_entry_array[i].dtlb_hit = 1'b1;
                // only update PA if not exception so can give VA on exception
                if (~dtlb_miss_resp_page_fault & ~dtlb_miss_resp_access_fault & ~entry_array[i].misaligned_exception) begin
                    next_entry_array[i].PA_word[PA_WIDTH-3:PA_WIDTH-2-PPN_WIDTH] = dtlb_miss_resp_PPN;
                    next_entry_array[i].ldu_CAM_launch_req = 1'b1;
                    next_entry_array[i].exception_req = 1'b0;
                end
                else begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                    next_entry_array[i].exception_req = 1'b1;
                end
                next_entry_array[i].is_mem = dtlb_miss_resp_is_mem;
                next_entry_array[i].page_fault = dtlb_miss_resp_page_fault;
                next_entry_array[i].access_fault = dtlb_miss_resp_access_fault;
            end
            // ldu CAM return
            else if (ldu_CAM_return_valid_by_entry[i]) begin
                next_entry_array[i].ldu_CAM_launch_returned = 1'b1;
                next_entry_array[i].forward |= ldu_CAM_return_forward;
            end

            // indep behavior:

            // stamofu_mq info ret bank 0 (indep)
            if (stamofu_mq_info_ret_bank0_valid_by_entry[i]) begin
                next_entry_array[i].mq_index = stamofu_mq_info_ret_bank0_mq_index;
            end

            // stamofu_mq info ret bank 1 (indep)
            if (stamofu_mq_info_ret_bank1_valid_by_entry[i]) begin
                next_entry_array[i].mq_index = stamofu_mq_info_ret_bank1_mq_index;
            end

            // stamofu_mq complete (indep)
            if (stamofu_mq_complete_valid_by_entry) begin
                next_entry_array[i].misaligned_complete = 1'b1;
            end

            // ROB complete (indep)
            if () begin
                 
            end
        end
    end

endmodule