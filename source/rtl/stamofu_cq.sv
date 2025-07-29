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
        // also interested in exceptions
    input logic                                 stamofu_mq_info_ret_bank0_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank0_cq_index,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank0_mq_index,
    input logic                                 stamofu_mq_info_ret_bank0_dtlb_hit,
    input logic                                 stamofu_mq_info_ret_bank0_page_fault,
    input logic                                 stamofu_mq_info_ret_bank0_access_fault,
    
    input logic                                 stamofu_mq_info_ret_bank1_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank1_cq_index,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank1_mq_index,
    input logic                                 stamofu_mq_info_ret_bank1_dtlb_hit,
    input logic                                 stamofu_mq_info_ret_bank1_page_fault,
    input logic                                 stamofu_mq_info_ret_bank1_access_fault,

    // dtlb miss resp
    input logic                                 dtlb_miss_resp_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    dtlb_miss_resp_cq_index,
    input logic                                 dtlb_miss_resp_is_mq,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    dtlb_miss_resp_mq_index, // unused
    input logic [PPN_WIDTH-1:0]                 dtlb_miss_resp_PPN,
    input logic                                 dtlb_miss_resp_is_mem,
    input logic                                 dtlb_miss_resp_page_fault,
    input logic                                 dtlb_miss_resp_access_fault,

    // ldu CAM launch from stamofu_mq
    input logic                                 stamofu_mq_ldu_CAM_launch_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_ldu_CAM_launch_cq_index, // stamofu_cq index
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_ldu_CAM_launch_mq_index, // stamofu_mq index
    input logic [PA_WIDTH-2-1:0]                stamofu_mq_ldu_CAM_launch_PA_word,
    input logic [3:0]                           stamofu_mq_ldu_CAM_launch_byte_mask,
    input logic [31:0]                          stamofu_mq_ldu_CAM_launch_write_data,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_mq_ldu_CAM_launch_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_mq_ldu_CAM_launch_ROB_index,

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
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_CAM_return_bank0_cq_index,
    input logic                                 stamofu_mq_CAM_return_bank0_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_CAM_return_bank0_stall_count,
    input logic [3:0]                           stamofu_mq_CAM_return_bank0_forward,
    input logic                                 stamofu_mq_CAM_return_bank0_nasty_forward,
    input logic                                 stamofu_mq_CAM_return_bank0_forward_ROB_index,
    input logic [31:0]                          stamofu_mq_CAM_return_bank0_forward_data,
    
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_CAM_return_bank1_cq_index,
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
    input logic                                 stamofu_mq_info_grab_is_mem,
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

    // fence restart notification backpressure from ROB
    input logic                         fence_restart_notif_ready,

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

    // store set CAM update bank 0
        // implied dep
    output logic                        ssu_CAM_update_bank0_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_bank0_ld_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_bank0_ld_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_bank0_stamo_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_bank0_stamo_ROB_index,

    // store set CAM update bank 1
        // implied dep
    output logic                        ssu_CAM_update_bank1_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_bank1_ld_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_bank1_ld_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_bank1_stamo_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_bank1_stamo_ROB_index,

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
        logic                               killed_in_dq;
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
    logic [STAMOFU_CQ_ENTRIES-1:0] dtlb_mq_miss_resp_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] ldu_CAM_return_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] stamofu_mq_complete_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0] clear_misaligned_by_entry;

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

    logic                               stamofu_cq_ldu_CAM_launch_valid;
    logic                               stamofu_cq_ldu_CAM_launch_ready;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stamofu_cq_ldu_CAM_launch_cq_index;

    logic                           next_stamofu_active;
    logic [LOG_ROB_ENTRIES-1:0]     next_stamofu_oldest_ROB_index;

    // stamofu CAM pipeline bank 0
    logic                               CAM_stage0_bank0_valid;
    
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage0_bank0_load_rel_age;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_addr_match_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_byte_overlap_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_valid_older_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_mdp_match_by_entry;
    
    logic                               CAM_stage1_bank0_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_return_cq_index; // ldu_cq index
    logic                               CAM_stage1_bank0_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_return_mq_index; // ldu_mq index, unused
    logic [MDPT_INFO_WIDTH-1:0]         CAM_stage1_bank0_load_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage1_bank0_load_ROB_index;

    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_mdp_match_by_entry;

    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_unmasked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_unmasked_one_hot;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank0_load_is_candidate_unmasked_index;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_masked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_masked_one_hot;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank0_load_is_candidate_masked_index;
    logic                               CAM_stage1_bank0_found_forward;
    // logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank0_load_selected_one_hot_by_entry;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank0_load_selected_index;
    logic                               CAM_stage1_bank0_load_is_subset;
    logic                               CAM_stage1_bank0_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank0_stall_count;

    logic                               CAM_stage2_bank0_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage2_bank0_return_cq_index; // ldu_cq index
    logic                               CAM_stage2_bank0_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage2_bank0_return_mq_index; // ldu_mq index, unused
    logic [MDPT_INFO_WIDTH-1:0]         CAM_stage2_bank0_load_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank0_load_ROB_index;

    logic                               CAM_stage2_bank0_found_forward;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank0_load_selected_index;
    logic                               CAM_stage2_bank0_load_is_subset;
    logic                               CAM_stage2_bank0_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank0_stall_count;

    logic                               CAM_stage2_bank0_forward;
    logic                               CAM_stage2_bank0_nasty_forward;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank0_forward_ROB_index;
    logic [31:0]                        CAM_stage2_bank0_forward_data;
    
    // stamofu CAM pipeline bank 1
    logic                               CAM_stage0_bank1_valid;
    
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage0_bank1_load_rel_age;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_addr_match_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_byte_overlap_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_valid_older_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_mdp_match_by_entry;
    
    logic                               CAM_stage1_bank1_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_return_cq_index; // ldu_cq index
    logic                               CAM_stage1_bank1_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_return_mq_index; // ldu_mq index, unused
    logic [MDPT_INFO_WIDTH-1:0]         CAM_stage1_bank1_load_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage1_bank1_load_ROB_index;

    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_subset_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_mdp_match_by_entry;

    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_unmasked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_unmasked_one_hot;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank1_load_is_candidate_unmasked_index;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_masked_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_masked_one_hot;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank1_load_is_candidate_masked_index;
    logic                               CAM_stage1_bank1_found_forward;
    // logic [STAMOFU_CQ_ENTRIES-1:0]      CAM_stage1_bank1_load_selected_one_hot_by_entry;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank1_load_selected_index;
    logic                               CAM_stage1_bank1_load_is_subset;
    logic                               CAM_stage1_bank1_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage1_bank1_stall_count;

    logic                               CAM_stage2_bank1_valid;

    logic [LOG_LDU_CQ_ENTRIES-1:0]      CAM_stage2_bank1_return_cq_index; // ldu_cq index
    logic                               CAM_stage2_bank1_return_is_mq;
    logic [LOG_LDU_MQ_ENTRIES-1:0]      CAM_stage2_bank1_return_mq_index; // ldu_mq index, unused
    logic [MDPT_INFO_WIDTH-1:0]         CAM_stage2_bank1_load_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank1_load_ROB_index;

    logic                               CAM_stage2_bank1_found_forward;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank1_load_selected_index;
    logic                               CAM_stage2_bank1_load_is_subset;
    logic                               CAM_stage2_bank1_stall;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  CAM_stage2_bank1_stall_count;

    logic                               CAM_stage2_bank1_forward;
    logic                               CAM_stage2_bank1_nasty_forward;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank1_forward_ROB_index;
    logic [31:0]                        CAM_stage2_bank1_forward_data;

    // ssu CAM update
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  ssu_CAM_update_bank0_cq_index;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  ssu_CAM_update_bank1_cq_index;

    logic [STAMOFU_CQ_ENTRIES-1:0]  ssu_CAM_update_bank0_valid_by_entry;
    logic [STAMOFU_CQ_ENTRIES-1:0]  ssu_CAM_update_bank1_valid_by_entry;

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
        dtlb_mq_miss_resp_valid_by_entry = '0;
        ldu_CAM_return_valid_by_entry = '0;
        stamofu_mq_complete_valid_by_entry = '0;

        stamofu_cq_info_ret_bank0_valid_by_entry[stamofu_cq_info_ret_bank0_cq_index] = stamofu_cq_info_ret_bank0_valid;
        stamofu_cq_info_ret_bank1_valid_by_entry[stamofu_cq_info_ret_bank1_cq_index] = stamofu_cq_info_ret_bank1_valid;
        stamofu_mq_info_ret_bank0_valid_by_entry[stamofu_mq_info_ret_bank0_cq_index] = stamofu_mq_info_ret_bank0_valid;
        stamofu_mq_info_ret_bank1_valid_by_entry[stamofu_mq_info_ret_bank1_cq_index] = stamofu_mq_info_ret_bank1_valid;
        dtlb_miss_resp_valid_by_entry[dtlb_miss_resp_cq_index] = dtlb_miss_resp_valid & ~dtlb_miss_resp_is_mq;
        dtlb_mq_miss_resp_valid_by_entry[dtlb_miss_resp_cq_index] = dtlb_miss_resp_valid & dtlb_miss_resp_is_mq;
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
            stamofu_cq_ldu_CAM_launch_valid <= 1'b0;
            stamofu_cq_ldu_CAM_launch_cq_index <= '0;
        end
        else if (stamofu_cq_ldu_CAM_launch_ready) begin
            stamofu_cq_ldu_CAM_launch_valid <= |ldu_CAM_launch_unmasked_req_by_entry;
            stamofu_cq_ldu_CAM_launch_cq_index <= ldu_CAM_launch_final_req_ack_index;
        end
    end
    always_comb begin

        // hardwired
        ldu_CAM_launch_valid = stamofu_cq_ldu_CAM_launch_valid | stamofu_mq_ldu_CAM_launch_valid;
        ldu_CAM_launch_mq_index = stamofu_mq_ldu_CAM_launch_mq_index;

        // muxed
        if (stamofu_mq_ldu_CAM_launch_valid) begin
            stamofu_cq_ldu_CAM_launch_ready = 1'b0;

            ldu_CAM_launch_cq_index = stamofu_mq_ldu_CAM_launch_cq_index;
            ldu_CAM_launch_is_mq = 1'b1;
            ldu_CAM_launch_is_amo = 1'b0;
            ldu_CAM_launch_PA_word = stamofu_mq_ldu_CAM_launch_PA_word;
            ldu_CAM_launch_byte_mask = stamofu_mq_ldu_CAM_launch_byte_mask;
            ldu_CAM_launch_write_data = stamofu_mq_ldu_CAM_launch_write_data;
            ldu_CAM_launch_mdp_info = stamofu_mq_ldu_CAM_launch_mdp_info;
            ldu_CAM_launch_ROB_index = stamofu_mq_ldu_CAM_launch_ROB_index;
        end
        else begin
            stamofu_cq_ldu_CAM_launch_ready = 1'b1;

            ldu_CAM_launch_cq_index = stamofu_cq_ldu_CAM_launch_cq_index;
            ldu_CAM_launch_is_mq = 1'b0;
            ldu_CAM_launch_is_amo = entry_array[stamofu_cq_ldu_CAM_launch_cq_index].is_amo;
            ldu_CAM_launch_PA_word = entry_array[stamofu_cq_ldu_CAM_launch_cq_index].PA_word;
            ldu_CAM_launch_byte_mask = entry_array[stamofu_cq_ldu_CAM_launch_cq_index].byte_mask;
            ldu_CAM_launch_write_data = entry_array[stamofu_cq_ldu_CAM_launch_cq_index].data;
            ldu_CAM_launch_mdp_info = entry_array[stamofu_cq_ldu_CAM_launch_cq_index].mdp_info;
            ldu_CAM_launch_ROB_index = entry_array[stamofu_cq_ldu_CAM_launch_cq_index].ROB_index;
        end
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
        casez (entry_array[rob_exception_cq_index].byte_mask)
            4'b0000:    rob_exception_VA[1:0] = 2'h0;
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
            
            // stamofu_cq ret bank 0
            if (stamofu_cq_info_ret_bank0_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                next_entry_array[i].misaligned = stamofu_cq_info_ret_bank0_misaligned;
                // next_entry_array[i].misaligned_complete = 
                // next_entry_array[i].mq_index = 
                // next_entry_array[i].killed_in_dq = 
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
                // next_entry_array[i].killed_in_dq = 
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
            // clear misaligned
            else if (clear_misaligned_by_entry[i]) begin
                next_entry_array[i].misaligned = 1'b0;
            end

            // indep behavior:

            // dtlb mq miss resp (indep)
            if (dtlb_mq_miss_resp_valid_by_entry[i]) begin
                // check lower word hasn't generated exception and upper word is
                if (
                    (dtlb_miss_resp_page_fault | dtlb_miss_resp_access_fault)
                    & ~(entry_array[i].exception_req | entry_array[i].exception_sent)
                    & ~next_entry_array[i].exception_req
                ) begin
                    next_entry_array[i].exception_req = 1'b1;
                    next_entry_array[i].page_fault = dtlb_miss_resp_page_fault;
                    next_entry_array[i].access_fault = dtlb_miss_resp_access_fault;
                end
            end

            // stamofu_mq info ret bank 0 (indep)
            if (stamofu_mq_info_ret_bank0_valid_by_entry[i]) begin
                next_entry_array[i].mq_index = stamofu_mq_info_ret_bank0_mq_index;

                // check lower word hasn't generated exception and upper word is excepting
                if (
                    stamofu_mq_info_ret_bank0_dtlb_hit
                    & (stamofu_mq_info_ret_bank0_page_fault | stamofu_mq_info_ret_bank0_access_fault)
                    & ~(entry_array[i].exception_req | entry_array[i].exception_sent)
                    & ~next_entry_array[i].exception_req
                ) begin
                    next_entry_array[i].exception_req = 1'b1;
                    next_entry_array[i].page_fault = stamofu_mq_info_ret_bank0_page_fault;
                    next_entry_array[i].access_fault = stamofu_mq_info_ret_bank0_access_fault;
                end
            end

            // stamofu_mq info ret bank 1 (indep)
            if (stamofu_mq_info_ret_bank1_valid_by_entry[i]) begin
                next_entry_array[i].mq_index = stamofu_mq_info_ret_bank1_mq_index;

                // check lower word hasn't generated exception and upper word is excepting
                if (
                    stamofu_mq_info_ret_bank1_dtlb_hit
                    & (stamofu_mq_info_ret_bank1_page_fault | stamofu_mq_info_ret_bank1_access_fault)
                    & ~(entry_array[i].exception_req | entry_array[i].exception_sent)
                    & ~next_entry_array[i].exception_req
                ) begin
                    next_entry_array[i].exception_req = 1'b1;
                    next_entry_array[i].page_fault = stamofu_mq_info_ret_bank1_page_fault;
                    next_entry_array[i].access_fault = stamofu_mq_info_ret_bank1_access_fault;
                end
            end

            // stamofu_mq complete (indep)
            if (stamofu_mq_complete_valid_by_entry[i]) begin
                next_entry_array[i].misaligned_complete = 1'b1;
            end

            // selected forward bank 0 (indep)
            if (ssu_CAM_update_bank0_valid_by_entry[i]) begin
                next_entry_array[i].forward = 1'b1;
            end

            // selected forward bank 1 (indep)
            if (ssu_CAM_update_bank1_valid_by_entry[i]) begin
                next_entry_array[i].forward = 1'b1;
            end

            // ROB complete req (indep)
            if (
                ~entry_array[i].complete
                & ~entry_array[i].complete_req
                & (~entry_array[i].misaligned | entry_array[i].misaligned_complete)
                & (
                    entry_array[i].killed_in_dq
                    | entry_array[i].is_fence
                    | entry_array[i].ldu_CAM_launch_returned
                    | entry_array[i].exception_sent)
            ) begin
                next_entry_array[i].complete_req = 1'b1;
            end

            // ROB commit (indep)
                // check within commit mask
            if (
                rob_commit_upper_index == entry_array[i].ROB_index[LOG_ROB_ENTRIES-1:2]
                & |(rob_commit_lower_index_valid_mask & entry_array[i].lower_ROB_index_one_hot)
            ) begin
                next_entry_array[i].committed = 1'b1;
            end

            // ROB kill (indep)
                // check younger than kill index
            if (
                rob_kill_valid
                & (rel_ROB_index_by_entry[i] > rob_kill_rel_kill_younger_index)
            ) begin
                next_entry_array[i].killed = 1'b1;
            end

            // req ack's (indep)
            if (ldu_CAM_launch_final_req_ack_one_hot_by_entry[i] & stamofu_cq_ldu_CAM_launch_ready) begin
                next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                next_entry_array[i].ldu_CAM_launch_sent = 1'b1;
            end
            if (rob_exception_final_req_ack_one_hot_by_entry[i] & rob_exception_ready) begin
                next_entry_array[i].exception_req = 1'b0;
                next_entry_array[i].exception_sent = 1'b1;
            end
            if (stamofu_complete_final_req_ack_one_hot_by_entry[i]) begin
                next_entry_array[i].complete_req = 1'b0;
                next_entry_array[i].complete = 1'b1; 
            end
        end
    end

    // stamofu CAM stage 0 bank 0
    always_comb begin
        CAM_stage0_bank0_valid = stamofu_CAM_launch_bank0_valid;
        CAM_stage0_bank0_load_rel_age = stamofu_CAM_launch_bank0_ROB_index - rob_kill_abs_head_index;

        for (int i = 0; i < STAMOFU_CQ_ENTRIES; i++) begin
            CAM_stage0_bank0_load_is_addr_match_by_entry[i] = 
                (entry_array[i].PA_word == stamofu_CAM_launch_bank0_PA_word)
            ;
            CAM_stage0_bank0_load_is_byte_overlap_by_entry[i] = 
                |(entry_array[i].byte_mask & stamofu_CAM_launch_bank0_byte_mask)
            ;
            // subset: CAM load byte -> entry byte
            CAM_stage0_bank0_load_is_subset_by_entry[i] = 
                &(~stamofu_CAM_launch_bank0_byte_mask | entry_array[i].byte_mask)
            ;
            CAM_stage0_bank0_load_is_valid_older_by_entry[i] = 
                entry_array[i].dtlb_hit
                & (entry_array[i].is_amo | entry_array[i].is_store)
                & (rel_ROB_index_by_entry[i] < CAM_stage0_bank0_load_rel_age)
            ;
            CAM_stage0_bank0_load_is_mdp_match_by_entry[i] = 
                entry_array[i].valid
                & ~entry_array[i].dtlb_hit
                & (entry_array[i].is_amo | entry_array[i].is_store)
                & |entry_array[i].mdp_info[7:6]
                & |stamofu_CAM_launch_bank0_mdp_info[7:6]
                & (entry_array[i].mdp_info[5:0] == stamofu_CAM_launch_bank0_mdp_info[5:0])
            ;
        end
    end
    // stamofu CAM stage 1 bank 0
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            CAM_stage1_bank0_valid <= 1'b0;
            CAM_stage1_bank0_return_cq_index <= 0;
            CAM_stage1_bank0_return_is_mq <= 0;
            CAM_stage1_bank0_return_mq_index <= 0;
            CAM_stage1_bank0_load_mdp_info <= 8'b00000000;
            CAM_stage1_bank0_load_ROB_index <= 7'h00;
            CAM_stage1_bank0_load_is_candidate_unmasked_by_entry <= '0;
            CAM_stage1_bank0_load_is_subset_by_entry <= '0;
            CAM_stage1_bank0_load_is_mdp_match_by_entry <= '0;
        end
        else begin
            CAM_stage1_bank0_valid <= CAM_stage0_bank0_valid;
            CAM_stage1_bank0_return_cq_index <= stamofu_CAM_launch_bank0_cq_index;
            CAM_stage1_bank0_return_is_mq <= stamofu_CAM_launch_bank0_is_mq;
            CAM_stage1_bank0_return_mq_index <= stamofu_CAM_launch_bank0_mq_index;
            CAM_stage1_bank0_load_mdp_info <= stamofu_CAM_launch_bank0_mdp_info;
            CAM_stage1_bank0_load_ROB_index <= stamofu_CAM_launch_bank0_ROB_index;
            CAM_stage1_bank0_load_is_candidate_unmasked_by_entry <= 
                CAM_stage0_bank0_load_is_addr_match_by_entry
                & CAM_stage0_bank0_load_is_byte_overlap_by_entry
                & CAM_stage0_bank0_load_is_valid_older_by_entry
            ;
            CAM_stage1_bank0_load_is_subset_by_entry <= CAM_stage0_bank0_load_is_subset_by_entry;
            CAM_stage1_bank0_load_is_mdp_match_by_entry <= CAM_stage0_bank0_load_is_mdp_match_by_entry;
        end
    end
    always_comb begin
        CAM_stage1_bank0_load_is_candidate_masked_by_entry = CAM_stage1_bank0_load_is_candidate_unmasked_by_entry & wraparound_mask;
        CAM_stage1_bank0_found_forward = |CAM_stage1_bank0_load_is_candidate_unmasked_by_entry;

        CAM_stage1_bank0_stall = |CAM_stage1_bank0_load_is_mdp_match_by_entry;
        CAM_stage1_bank0_stall_count = 0;
        for (int i = 0; i < STAMOFU_CQ_ENTRIES; i++) begin
            CAM_stage1_bank0_stall_count += CAM_stage1_bank0_load_is_mdp_match_by_entry[i];
        end
    end
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) CAM_SELECT_UNMASKED_PE_BANK0 (
        .req_vec(CAM_stage1_bank0_load_is_candidate_unmasked_by_entry),
        .ack_one_hot(CAM_stage1_bank0_load_is_candidate_unmasked_one_hot),
        .ack_index(CAM_stage1_bank0_load_is_candidate_unmasked_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) CAM_SELECT_MASKED_PE_BANK0 (
        .req_vec(CAM_stage1_bank0_load_is_candidate_masked_by_entry),
        .ack_one_hot(CAM_stage1_bank0_load_is_candidate_masked_one_hot),
        .ack_index(CAM_stage1_bank0_load_is_candidate_masked_index)
    );
    always_comb begin
        if (|CAM_stage1_bank0_load_is_candidate_masked_by_entry) begin
            CAM_stage1_bank0_load_selected_index = CAM_stage1_bank0_load_is_candidate_masked_index;
            CAM_stage1_bank0_load_is_subset = |(CAM_stage1_bank0_load_is_candidate_masked_one_hot & CAM_stage1_bank0_load_is_subset_by_entry);
        end else begin
            CAM_stage1_bank0_load_selected_index = CAM_stage1_bank0_load_is_candidate_unmasked_index;
            CAM_stage1_bank0_load_is_subset = |(CAM_stage1_bank0_load_is_candidate_unmasked_one_hot & CAM_stage1_bank0_load_is_subset_by_entry);
        end
    end
    // stamofu CAM stage 2 bank 0
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            CAM_stage2_bank0_valid <= 1'b0;
            CAM_stage2_bank0_return_cq_index <= 0;
            CAM_stage2_bank0_return_is_mq <= 1'b0;
            CAM_stage2_bank0_return_mq_index <= 0;
            CAM_stage2_bank0_load_mdp_info <= 8'b00000000;
            CAM_stage2_bank0_load_ROB_index <= 7'h00;
            CAM_stage2_bank0_found_forward <= 1'b0;
            CAM_stage2_bank0_load_selected_index <= 0;
            CAM_stage2_bank0_load_is_subset <= 1'b0;
            CAM_stage2_bank0_stall <= 1'b0;
            CAM_stage2_bank0_stall_count <= 0;
        end
        else begin
            CAM_stage2_bank0_valid <= CAM_stage1_bank0_valid;
            CAM_stage2_bank0_return_cq_index <= CAM_stage1_bank0_return_cq_index;
            CAM_stage2_bank0_return_is_mq <= CAM_stage1_bank0_return_is_mq;
            CAM_stage2_bank0_return_mq_index <= CAM_stage1_bank0_return_mq_index;
            CAM_stage2_bank0_load_mdp_info <= CAM_stage1_bank0_load_mdp_info;
            CAM_stage2_bank0_load_ROB_index <= CAM_stage1_bank0_load_ROB_index;
            CAM_stage2_bank0_found_forward <= CAM_stage1_bank0_found_forward;
            CAM_stage2_bank0_load_selected_index <= CAM_stage1_bank0_load_selected_index;
            CAM_stage2_bank0_load_is_subset <= CAM_stage1_bank0_load_is_subset;
            CAM_stage2_bank0_stall <= CAM_stage1_bank0_stall;
            CAM_stage2_bank0_stall_count <= CAM_stage1_bank0_stall_count;
        end
    end
    always_comb begin
        // nasty forward if not subset or amo
        CAM_stage2_bank0_forward = 
            CAM_stage2_bank0_found_forward
            & CAM_stage2_bank0_load_is_subset
            & ~entry_array[CAM_stage2_bank0_load_selected_index].is_amo
        ;
        CAM_stage2_bank0_nasty_forward =
            CAM_stage2_bank0_found_forward
            & (~CAM_stage2_bank0_load_is_subset | entry_array[CAM_stage2_bank0_load_selected_index].is_amo)
        ;
        CAM_stage2_bank0_forward_ROB_index = entry_array[CAM_stage2_bank0_load_selected_index].ROB_index;
        CAM_stage2_bank0_forward_data = entry_array[CAM_stage2_bank0_load_selected_index].data;
    end
    // stamofu_cq vs. stamofu_mq CAM bank 0
    always_comb begin
        stamofu_CAM_return_bank0_valid = CAM_stage2_bank0_valid;
        stamofu_CAM_return_bank0_cq_index = CAM_stage2_bank0_return_cq_index;
        stamofu_CAM_return_bank0_is_mq = CAM_stage2_bank0_return_is_mq;
        stamofu_CAM_return_bank0_mq_index = CAM_stage2_bank0_return_mq_index;

        // check for stamofu_mq (nasty) forward and stamofu_cq no (nasty) forward or stamofu_cq older
        if (
            (stamofu_mq_CAM_return_bank0_forward | stamofu_mq_CAM_return_bank0_nasty_forward)
            & (
                ~(CAM_stage2_bank0_forward | CAM_stage2_bank0_nasty_forward)
                | (
                    (CAM_stage2_bank0_forward_ROB_index - rob_kill_abs_head_index)
                    <
                    (stamofu_mq_CAM_return_bank0_forward_ROB_index - rob_kill_abs_head_index)
            ))
        ) begin
            stamofu_CAM_return_bank0_forward = stamofu_mq_CAM_return_bank0_forward;
            stamofu_CAM_return_bank0_nasty_forward = stamofu_mq_CAM_return_bank0_nasty_forward;
            stamofu_CAM_return_bank0_forward_ROB_index = stamofu_mq_CAM_return_bank0_forward_ROB_index;
            stamofu_CAM_return_bank0_forward_data = stamofu_mq_CAM_return_bank0_forward_data;

            // ssu CAM update from mq
            ssu_CAM_update_bank0_cq_index = stamofu_mq_CAM_return_bank0_cq_index;
        end
        else begin
            stamofu_CAM_return_bank0_forward = CAM_stage2_bank0_forward;
            stamofu_CAM_return_bank0_nasty_forward = CAM_stage2_bank0_nasty_forward;
            stamofu_CAM_return_bank0_forward_ROB_index = CAM_stage2_bank0_forward_ROB_index;
            stamofu_CAM_return_bank0_forward_data = CAM_stage2_bank0_forward_data;

            // ssu CAM update from cq
            ssu_CAM_update_bank0_cq_index = CAM_stage2_bank0_load_selected_index;
        end

        // accumulate stalls
        stamofu_CAM_return_bank0_stall = stamofu_mq_CAM_return_bank0_stall | CAM_stage2_bank0_stall;
        stamofu_CAM_return_bank0_stall_count = stamofu_mq_CAM_return_bank0_stall_count + CAM_stage2_bank0_stall_count;
        
        // ssu CAM update
        ssu_CAM_update_bank0_valid = 
            stamofu_CAM_return_bank0_valid 
            & (stamofu_CAM_return_bank0_forward | stamofu_CAM_return_bank0_nasty_forward)
        ;
        ssu_CAM_update_bank0_ld_mdp_info = CAM_stage2_bank0_load_mdp_info;
        ssu_CAM_update_bank0_ld_ROB_index = CAM_stage2_bank0_load_ROB_index;
        ssu_CAM_update_bank0_stamo_mdp_info = entry_array[ssu_CAM_update_bank0_cq_index].mdp_info;
        ssu_CAM_update_bank0_stamo_ROB_index = entry_array[ssu_CAM_update_bank0_cq_index].ROB_index;

        ssu_CAM_update_bank0_valid_by_entry = '0;
        ssu_CAM_update_bank0_valid_by_entry[ssu_CAM_update_bank0_cq_index] = ssu_CAM_update_bank0_valid;
    end

    // stamofu CAM stage 0 bank 1
    always_comb begin
        CAM_stage0_bank1_valid = stamofu_CAM_launch_bank1_valid;
        CAM_stage0_bank1_load_rel_age = stamofu_CAM_launch_bank1_ROB_index - rob_kill_abs_head_index;

        for (int i = 0; i < STAMOFU_CQ_ENTRIES; i++) begin
            CAM_stage0_bank1_load_is_addr_match_by_entry[i] = 
                (entry_array[i].PA_word == stamofu_CAM_launch_bank1_PA_word)
            ;
            CAM_stage0_bank1_load_is_byte_overlap_by_entry[i] = 
                |(entry_array[i].byte_mask & stamofu_CAM_launch_bank1_byte_mask)
            ;
            // subset: CAM load byte -> entry byte
            CAM_stage0_bank1_load_is_subset_by_entry[i] = 
                &(~stamofu_CAM_launch_bank1_byte_mask | entry_array[i].byte_mask)
            ;
            CAM_stage0_bank1_load_is_valid_older_by_entry[i] = 
                entry_array[i].dtlb_hit
                & (entry_array[i].is_amo | entry_array[i].is_store)
                & (rel_ROB_index_by_entry[i] < CAM_stage0_bank1_load_rel_age)
            ;
            CAM_stage0_bank1_load_is_mdp_match_by_entry[i] = 
                entry_array[i].valid
                & ~entry_array[i].dtlb_hit
                & (entry_array[i].is_amo | entry_array[i].is_store)
                & |entry_array[i].mdp_info[7:6]
                & |stamofu_CAM_launch_bank1_mdp_info[7:6]
                & (entry_array[i].mdp_info[5:0] == stamofu_CAM_launch_bank1_mdp_info[5:0])
            ;
        end
    end
    // stamofu CAM stage 1 bank 1
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            CAM_stage1_bank1_valid <= 1'b0;
            CAM_stage1_bank1_return_cq_index <= 0;
            CAM_stage1_bank1_return_is_mq <= 0;
            CAM_stage1_bank1_return_mq_index <= 0;
            CAM_stage1_bank1_load_mdp_info <= 8'b00000000;
            CAM_stage1_bank1_load_ROB_index <= 7'h00;
            CAM_stage1_bank1_load_is_candidate_unmasked_by_entry <= '0;
            CAM_stage1_bank1_load_is_subset_by_entry <= '0;
            CAM_stage1_bank1_load_is_mdp_match_by_entry <= '0;
        end
        else begin
            CAM_stage1_bank1_valid <= CAM_stage0_bank1_valid;
            CAM_stage1_bank1_return_cq_index <= stamofu_CAM_launch_bank1_cq_index;
            CAM_stage1_bank1_return_is_mq <= stamofu_CAM_launch_bank1_is_mq;
            CAM_stage1_bank1_return_mq_index <= stamofu_CAM_launch_bank1_mq_index;
            CAM_stage1_bank1_load_mdp_info <= stamofu_CAM_launch_bank1_mdp_info;
            CAM_stage1_bank1_load_ROB_index <= stamofu_CAM_launch_bank1_ROB_index;
            CAM_stage1_bank1_load_is_candidate_unmasked_by_entry <= 
                CAM_stage0_bank1_load_is_addr_match_by_entry
                & CAM_stage0_bank1_load_is_byte_overlap_by_entry
                & CAM_stage0_bank1_load_is_valid_older_by_entry
            ;
            CAM_stage1_bank1_load_is_subset_by_entry <= CAM_stage0_bank1_load_is_subset_by_entry;
            CAM_stage1_bank1_load_is_mdp_match_by_entry <= CAM_stage0_bank1_load_is_mdp_match_by_entry;
        end
    end
    always_comb begin
        CAM_stage1_bank1_load_is_candidate_masked_by_entry = CAM_stage1_bank1_load_is_candidate_unmasked_by_entry & wraparound_mask;
        CAM_stage1_bank1_found_forward = |CAM_stage1_bank1_load_is_candidate_unmasked_by_entry;

        CAM_stage1_bank1_stall = |CAM_stage1_bank1_load_is_mdp_match_by_entry;
        CAM_stage1_bank1_stall_count = 0;
        for (int i = 0; i < STAMOFU_CQ_ENTRIES; i++) begin
            CAM_stage1_bank1_stall_count += CAM_stage1_bank1_load_is_mdp_match_by_entry[i];
        end
    end
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) CAM_SELECT_UNMASKED_PE_BANK1 (
        .req_vec(CAM_stage1_bank1_load_is_candidate_unmasked_by_entry),
        .ack_one_hot(CAM_stage1_bank1_load_is_candidate_unmasked_one_hot),
        .ack_index(CAM_stage1_bank1_load_is_candidate_unmasked_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) CAM_SELECT_MASKED_PE_BANK1 (
        .req_vec(CAM_stage1_bank1_load_is_candidate_masked_by_entry),
        .ack_one_hot(CAM_stage1_bank1_load_is_candidate_masked_one_hot),
        .ack_index(CAM_stage1_bank1_load_is_candidate_masked_index)
    );
    always_comb begin
        if (|CAM_stage1_bank1_load_is_candidate_masked_by_entry) begin
            CAM_stage1_bank1_load_selected_index = CAM_stage1_bank1_load_is_candidate_masked_index;
            CAM_stage1_bank1_load_is_subset = |(CAM_stage1_bank1_load_is_candidate_masked_one_hot & CAM_stage1_bank1_load_is_subset_by_entry);
        end else begin
            CAM_stage1_bank1_load_selected_index = CAM_stage1_bank1_load_is_candidate_unmasked_index;
            CAM_stage1_bank1_load_is_subset = |(CAM_stage1_bank1_load_is_candidate_unmasked_one_hot & CAM_stage1_bank1_load_is_subset_by_entry);
        end
    end
    // stamofu CAM stage 2 bank 1
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            CAM_stage2_bank1_valid <= 1'b0;
            CAM_stage2_bank1_return_cq_index <= 0;
            CAM_stage2_bank1_return_is_mq <= 1'b0;
            CAM_stage2_bank1_return_mq_index <= 0;
            CAM_stage2_bank1_load_mdp_info <= 8'b00000000;
            CAM_stage2_bank1_load_ROB_index <= 7'h00;
            CAM_stage2_bank1_found_forward <= 1'b0;
            CAM_stage2_bank1_load_selected_index <= 0;
            CAM_stage2_bank1_load_is_subset <= 1'b0;
            CAM_stage2_bank1_stall <= 1'b0;
            CAM_stage2_bank1_stall_count <= 0;
        end
        else begin
            CAM_stage2_bank1_valid <= CAM_stage1_bank1_valid;
            CAM_stage2_bank1_return_cq_index <= CAM_stage1_bank1_return_cq_index;
            CAM_stage2_bank1_return_is_mq <= CAM_stage1_bank1_return_is_mq;
            CAM_stage2_bank1_return_mq_index <= CAM_stage1_bank1_return_mq_index;
            CAM_stage2_bank1_load_mdp_info <= CAM_stage1_bank1_load_mdp_info;
            CAM_stage2_bank1_load_ROB_index <= CAM_stage1_bank1_load_ROB_index;
            CAM_stage2_bank1_found_forward <= CAM_stage1_bank1_found_forward;
            CAM_stage2_bank1_load_selected_index <= CAM_stage1_bank1_load_selected_index;
            CAM_stage2_bank1_load_is_subset <= CAM_stage1_bank1_load_is_subset;
            CAM_stage2_bank1_stall <= CAM_stage1_bank1_stall;
            CAM_stage2_bank1_stall_count <= CAM_stage1_bank1_stall_count;
        end
    end
    always_comb begin
        // nasty forward if not subset or amo
        CAM_stage2_bank1_forward = 
            CAM_stage2_bank1_found_forward
            & CAM_stage2_bank1_load_is_subset
            & ~entry_array[CAM_stage2_bank1_load_selected_index].is_amo
        ;
        CAM_stage2_bank1_nasty_forward =
            CAM_stage2_bank1_found_forward
            & (~CAM_stage2_bank1_load_is_subset | entry_array[CAM_stage2_bank1_load_selected_index].is_amo)
        ;
        CAM_stage2_bank1_forward_ROB_index = entry_array[CAM_stage2_bank1_load_selected_index].ROB_index;
        CAM_stage2_bank1_forward_data = entry_array[CAM_stage2_bank1_load_selected_index].data;
    end
    // stamofu_cq vs. stamofu_mq CAM bank 1
    always_comb begin
        stamofu_CAM_return_bank1_valid = CAM_stage2_bank1_valid;
        stamofu_CAM_return_bank1_cq_index = CAM_stage2_bank1_return_cq_index;
        stamofu_CAM_return_bank1_is_mq = CAM_stage2_bank1_return_is_mq;
        stamofu_CAM_return_bank1_mq_index = CAM_stage2_bank1_return_mq_index;

        // check for stamofu_mq (nasty) forward and stamofu_cq no (nasty) forward or stamofu_cq older
        if (
            (stamofu_mq_CAM_return_bank1_forward | stamofu_mq_CAM_return_bank1_nasty_forward)
            & (
                ~(CAM_stage2_bank1_forward | CAM_stage2_bank1_nasty_forward)
                | (
                    (CAM_stage2_bank1_forward_ROB_index - rob_kill_abs_head_index)
                    <
                    (stamofu_mq_CAM_return_bank1_forward_ROB_index - rob_kill_abs_head_index)
            ))
        ) begin
            stamofu_CAM_return_bank1_forward = stamofu_mq_CAM_return_bank1_forward;
            stamofu_CAM_return_bank1_nasty_forward = stamofu_mq_CAM_return_bank1_nasty_forward;
            stamofu_CAM_return_bank1_forward_ROB_index = stamofu_mq_CAM_return_bank1_forward_ROB_index;
            stamofu_CAM_return_bank1_forward_data = stamofu_mq_CAM_return_bank1_forward_data;

            // ssu CAM update from mq
            ssu_CAM_update_bank1_cq_index = stamofu_mq_CAM_return_bank1_cq_index;
        end
        else begin
            stamofu_CAM_return_bank1_forward = CAM_stage2_bank1_forward;
            stamofu_CAM_return_bank1_nasty_forward = CAM_stage2_bank1_nasty_forward;
            stamofu_CAM_return_bank1_forward_ROB_index = CAM_stage2_bank1_forward_ROB_index;
            stamofu_CAM_return_bank1_forward_data = CAM_stage2_bank1_forward_data;

            // ssu CAM update from cq
            ssu_CAM_update_bank1_cq_index = CAM_stage2_bank1_load_selected_index;
        end

        // accumulate stalls
        stamofu_CAM_return_bank1_stall = stamofu_mq_CAM_return_bank1_stall | CAM_stage2_bank1_stall;
        stamofu_CAM_return_bank1_stall_count = stamofu_mq_CAM_return_bank1_stall_count + CAM_stage2_bank1_stall_count;
        
        // ssu CAM update
        ssu_CAM_update_bank1_valid = 
            stamofu_CAM_return_bank1_valid 
            & (stamofu_CAM_return_bank1_forward | stamofu_CAM_return_bank1_nasty_forward)
        ;
        ssu_CAM_update_bank1_ld_mdp_info = CAM_stage2_bank1_load_mdp_info;
        ssu_CAM_update_bank1_ld_ROB_index = CAM_stage2_bank1_load_ROB_index;
        ssu_CAM_update_bank1_stamo_mdp_info = entry_array[ssu_CAM_update_bank1_cq_index].mdp_info;
        ssu_CAM_update_bank1_stamo_ROB_index = entry_array[ssu_CAM_update_bank1_cq_index].ROB_index;

        ssu_CAM_update_bank1_valid_by_entry = '0;
        ssu_CAM_update_bank1_valid_by_entry[ssu_CAM_update_bank1_cq_index] = ssu_CAM_update_bank1_valid;
    end

    // central queue info grab
    always_comb begin
        stamofu_cq_info_grab_bank0_mdp_info = entry_array[stamofu_cq_info_grab_bank0_cq_index].mdp_info;
        stamofu_cq_info_grab_bank0_mem_aq = entry_array[stamofu_cq_info_grab_bank0_cq_index].mem_aq;
        stamofu_cq_info_grab_bank0_io_aq = entry_array[stamofu_cq_info_grab_bank0_cq_index].io_aq;
        stamofu_cq_info_grab_bank0_mem_rl = entry_array[stamofu_cq_info_grab_bank0_cq_index].mem_rl;
        stamofu_cq_info_grab_bank0_io_rl = entry_array[stamofu_cq_info_grab_bank0_cq_index].io_rl;
        stamofu_cq_info_grab_bank0_ROB_index = entry_array[stamofu_cq_info_grab_bank0_cq_index].ROB_index;
        
        stamofu_cq_info_grab_bank1_mdp_info = entry_array[stamofu_cq_info_grab_bank1_cq_index].mdp_info;
        stamofu_cq_info_grab_bank1_mem_aq = entry_array[stamofu_cq_info_grab_bank1_cq_index].mem_aq;
        stamofu_cq_info_grab_bank1_io_aq = entry_array[stamofu_cq_info_grab_bank1_cq_index].io_aq;
        stamofu_cq_info_grab_bank1_mem_rl = entry_array[stamofu_cq_info_grab_bank1_cq_index].mem_rl;
        stamofu_cq_info_grab_bank1_io_rl = entry_array[stamofu_cq_info_grab_bank1_cq_index].io_rl;
        stamofu_cq_info_grab_bank1_ROB_index = entry_array[stamofu_cq_info_grab_bank1_cq_index].ROB_index;
    end

    // enq
    assign enq_perform = ~entry_array[enq_ptr].valid & stamofu_cq_enq_valid;

    // enq feedback
    always_comb begin
        stamofu_cq_enq_ready = ~entry_array[enq_ptr].valid;
        stamofu_cq_enq_index = enq_ptr;
    end

    // // deq
    // assign deq_perform = entry_array[deq_ptr].valid & entry_array[deq_ptr].committed;

    // deq logic
    always_comb begin

        // hardwired connections
        stamofu_mq_info_grab_mq_index = entry_array[deq_ptr].mq_index;

        wr_buf_enq_is_amo = entry_array[deq_ptr].is_amo;
        wr_buf_enq_op = entry_array[deq_ptr].op;

        fence_restart_notif_ROB_index = entry_array[deq_ptr].ROB_index;

        // check for killed or exception deq
        if (
            entry_array[deq_ptr].valid
            & (entry_array[deq_ptr].killed | entry_array[deq_ptr].exception_sent)
        ) begin
            // can perform deq
            deq_perform = 1'b1;

            // no misaligned clear
            clear_misaligned_by_entry = '0;
            
            // clear mq entry if present
            stamofu_mq_info_grab_clear_entry = entry_array[deq_ptr].misaligned;

            // skip write buffer enq
            wr_buf_enq_valid = 1'b0;
            wr_buf_enq_is_mem = entry_array[deq_ptr].is_mem;
            wr_buf_enq_PA_word = entry_array[deq_ptr].PA_word;
            wr_buf_enq_byte_mask = entry_array[deq_ptr].byte_mask;
            wr_buf_enq_data = entry_array[deq_ptr].data;

            // no fence restart notif
            fence_restart_notif_valid = 1'b0;

            // clear aq entry if present
            stamofu_aq_deq_valid = entry_array[deq_ptr].mem_aq | entry_array[deq_ptr].io_aq;
        end
        
        // check for misaligned component
            // guaranteed is_store, no fencing
            // need write buffer ready
        else if (
            entry_array[deq_ptr].valid
            & entry_array[deq_ptr].misaligned
            & wr_buf_ready
            & (~entry_array[deq_ptr].is_fence | entry_array[deq_ptr])
        ) begin
            // don't perform deq yet
            deq_perform = 1'b0;

            // clear misaligned
            clear_misaligned_by_entry= '0;
            clear_misaligned_by_entry[deq_ptr] = 1'b1;

            // clear mq entry
            stamofu_mq_info_grab_clear_entry = 1'b1;

            // write buffer enq from stamofu_mq
            wr_buf_enq_valid = 1'b1;
            wr_buf_enq_is_mem = stamofu_mq_info_grab_is_mem;
            wr_buf_enq_PA_word = stamofu_mq_info_grab_PA_word;
            wr_buf_enq_byte_mask = stamofu_mq_info_grab_byte_mask;
            wr_buf_enq_data = stamofu_mq_info_grab_data;

            // no fence restart notif
            fence_restart_notif_valid = 1'b0;
            
            // no clear aq
            stamofu_aq_deq_valid = 1'b0;
        end

        // otherwise, aligned component
            // need write buffer ready if store or amo
            // need fence restart notif ready if SFENCE.VMA or FENCE.I
            // need no mem present if mem_rl
            // need no io present if io_rl
        else if (
            entry_array[deq_ptr].valid
            & ~entry_array[deq_ptr].misaligned
            & (
                ~(entry_array[deq_ptr].is_store | entry_array[deq_ptr].is_amo)
                | wr_buf_ready
            )
            & (
                ~(
                    entry_array[deq_ptr].is_fence
                    & |entry_array[deq_ptr].op[1:0]
                ) 
                | fence_restart_notif_ready
            )
            & (~entry_array[deq_ptr].mem_rl | ~wr_buf_mem_present)
            & (~entry_array[deq_ptr].io_rl | ~wr_buf_io_present)
        ) begin
            // can perform deq
            deq_perform = 1'b1;

            // no misaligned clear
            clear_misaligned_by_entry = '0;

            // no clear mq entry
            stamofu_mq_info_grab_clear_entry = 1'b0;

            // write buffer enq if store or amo from cq
            wr_buf_enq_valid = entry_array[deq_ptr].is_store | entry_array[deq_ptr].is_amo;
            wr_buf_enq_is_mem = entry_array[deq_ptr].is_mem;
            wr_buf_enq_PA_word = entry_array[deq_ptr].PA_word;
            wr_buf_enq_byte_mask = entry_array[deq_ptr].byte_mask;
            wr_buf_enq_data = entry_array[deq_ptr].data;

            // fence restart notif if SFENCE.VMA or FENCE.I
            fence_restart_notif_valid = entry_array[deq_ptr].is_fence & |entry_array[deq_ptr].op[1:0];

            // clear aq entry if present
            stamofu_aq_deq_valid = entry_array[deq_ptr].mem_aq | entry_array[deq_ptr].io_aq;
        end

        // otherwise, stall
        else begin
            deq_perform = 1'b0;
            clear_misaligned_by_entry= '0;
            stamofu_mq_info_grab_clear_entry = 1'b0;
            wr_buf_enq_valid = 1'b0;
            wr_buf_enq_is_mem = entry_array[deq_ptr].is_mem;
            wr_buf_enq_PA_word = entry_array[deq_ptr].PA_word;
            wr_buf_enq_byte_mask = entry_array[deq_ptr].byte_mask;
            wr_buf_enq_data = entry_array[deq_ptr].data;
            fence_restart_notif_valid = 1'b0;
            stamofu_aq_deq_valid = 1'b0;
        end
    end

    // perform store set commit update on deq
        // update already occurred if there was a forward
        // essentially, only do decrement update
    always_comb begin
        ssu_commit_update_valid = 
            deq_perform 
            & (entry_array[deq_ptr].is_amo | entry_array[deq_ptr].is_store)
            & ~entry_array[deq_ptr].forward;
        ssu_commit_update_mdp_info = entry_array[deq_ptr].mdp_info;
        ssu_commit_update_ROB_index = entry_array[deq_ptr].ROB_index;
    end

    // wraparound mask based on deq
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            wraparound_mask <= '1;
        end
        else if (deq_perform) begin

            // check for wraparound
                // n'b100000 -> n'b111111
                    // second msb == 1'b0
            if (~wraparound_mask[STAMOFU_CQ_ENTRIES-2]) begin
                wraparound_mask <= '1;
            end

            // otherwise, shift 0 in leftward
                // n'b111100 -> n'b111000
            else begin
                wraparound_mask <= {wraparound_mask[STAMOFU_CQ_ENTRIES-2], 1'b0};
            end
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            stamofu_active <= 1'b0;
            stamofu_oldest_ROB_index <= 7'h00;
        end
        else begin
            stamofu_active <= next_stamofu_active;
            stamofu_oldest_ROB_index <= next_stamofu_oldest_ROB_index;
        end
    end
    always_comb begin
        next_stamofu_active = 1'b0;
        for (int i = 0; i < STAMOFU_CQ_ENTRIES; i++) begin
            next_stamofu_active |= entry_array[i].valid;
        end
        next_stamofu_oldest_ROB_index = entry_array[deq_perform].ROB_index;
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            entry_array <= '0;

            enq_ptr <= 0;
            deq_ptr <= 0;
        end
        else begin
            entry_array <= next_entry_array;

            //////////
            // enq: //
            //////////
            if (enq_perform) begin
                entry_array[enq_ptr].valid <= 1'b1;
                entry_array[enq_ptr].misaligned <= 1'b0;
                entry_array[enq_ptr].misaligned_complete <= 1'b0;
                // entry_array[enq_ptr].mq_index <= 
                entry_array[enq_ptr].killed_in_dq <= stamofu_cq_enq_killed;
                entry_array[enq_ptr].killed <= stamofu_cq_enq_killed;
                entry_array[enq_ptr].dtlb_hit <= 1'b0;
                entry_array[enq_ptr].forward <= 1'b0;
                entry_array[enq_ptr].committed <= 1'b0;
                entry_array[enq_ptr].ldu_CAM_launch_req <= 1'b0;
                entry_array[enq_ptr].ldu_CAM_launch_sent <= 1'b0;
                entry_array[enq_ptr].ldu_CAM_launch_returned <= 1'b0;
                entry_array[enq_ptr].complete_req <= 1'b0;
                entry_array[enq_ptr].complete <= 1'b0;
                entry_array[enq_ptr].exception_req <= 1'b0;
                entry_array[enq_ptr].exception_sent <= 1'b0;
                entry_array[enq_ptr].is_mem <= 1'b0;
                entry_array[enq_ptr].mem_aq <= stamofu_cq_enq_mem_aq;
                entry_array[enq_ptr].io_aq <= stamofu_cq_enq_io_aq;
                entry_array[enq_ptr].mem_rl <= stamofu_cq_enq_mem_rl;
                entry_array[enq_ptr].io_rl <= stamofu_cq_enq_io_rl;
                entry_array[enq_ptr].page_fault <= 1'b0;
                entry_array[enq_ptr].access_fault <= 1'b0;
                entry_array[enq_ptr].misaligned_exception <= 1'b0;
                entry_array[enq_ptr].is_store <= stamofu_cq_enq_is_store;
                entry_array[enq_ptr].is_amo <= stamofu_cq_enq_is_amo;
                entry_array[enq_ptr].is_fence <= stamofu_cq_enq_is_fence;
                entry_array[enq_ptr].op <= stamofu_cq_enq_op;
                entry_array[enq_ptr].mdp_info <= stamofu_cq_enq_mdp_info;
                entry_array[enq_ptr].dest_PR <= stamofu_cq_enq_dest_PR;
                entry_array[enq_ptr].ROB_index <= stamofu_cq_enq_ROB_index;
                case (stamofu_cq_enq_ROB_index[1:0])
                    2'h0:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0001;
                    2'h1:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0010;
                    2'h2:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0100;
                    2'h3:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b1000;
                endcase
                // entry_array[enq_ptr].PA_word <= 
                // entry_array[enq_ptr].byte_mask <= 
                // entry_array[enq_ptr].data <= 

                enq_ptr <= enq_ptr_plus_1;
            end

            //////////
            // deq: //
            //////////
            if (deq_perform) begin
                entry_array[deq_ptr].valid <= 1'b1;
                entry_array[deq_ptr].misaligned <= 1'b0;
                entry_array[deq_ptr].misaligned_complete <= 1'b0;
                // entry_array[deq_ptr].mq_index <= 
                entry_array[deq_ptr].killed_in_dq <= 1'b0;
                entry_array[deq_ptr].killed <= 1'b0;
                entry_array[deq_ptr].dtlb_hit <= 1'b0;
                entry_array[deq_ptr].forward <= 1'b0;
                entry_array[deq_ptr].committed <= 1'b0;
                entry_array[deq_ptr].ldu_CAM_launch_req <= 1'b0;
                entry_array[deq_ptr].ldu_CAM_launch_sent <= 1'b0;
                entry_array[deq_ptr].ldu_CAM_launch_returned <= 1'b0;
                entry_array[deq_ptr].complete_req <= 1'b0;
                entry_array[deq_ptr].complete <= 1'b0;
                entry_array[deq_ptr].exception_req <= 1'b0;
                entry_array[deq_ptr].exception_sent <= 1'b0;
                // entry_array[deq_ptr].is_mem <= 
                // entry_array[deq_ptr].mem_aq <= 
                // entry_array[deq_ptr].io_aq <= 
                // entry_array[deq_ptr].mem_rl <= 
                // entry_array[deq_ptr].io_rl <= 
                // entry_array[deq_ptr].page_fault <= 
                // entry_array[deq_ptr].access_fault <= 
                // entry_array[deq_ptr].misaligned_exception <= 
                // entry_array[deq_ptr].is_store <= 
                // entry_array[deq_ptr].is_amo <= 
                // entry_array[deq_ptr].is_fence <= 
                // entry_array[deq_ptr].op <= 
                // entry_array[deq_ptr].mdp_info <= 
                // entry_array[deq_ptr].dest_PR <= 
                // entry_array[deq_ptr].ROB_index <= 
                // entry_array[deq_ptr].lower_ROB_index_one_hot <=
                // entry_array[deq_ptr].PA_word <= 
                // entry_array[deq_ptr].byte_mask <= 
                // entry_array[deq_ptr].data <= 

                deq_ptr <= deq_ptr_plus_1;
            end
        end
    end

endmodule