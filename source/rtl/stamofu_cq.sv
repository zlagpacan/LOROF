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
    input logic                             dtlb_miss_resp_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    dtlb_miss_resp_cq_index,
    input logic                             dtlb_miss_resp_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    dtlb_miss_resp_mq_index, // unused
    input logic [PPN_WIDTH-1:0]             dtlb_miss_resp_PPN,
    input logic                             dtlb_miss_resp_is_mem,
    input logic                             dtlb_miss_resp_page_fault,
    input logic                             dtlb_miss_resp_access_fault,

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
    input logic [PA_WIDTH-2-1:0]                stamofu_CAM_launch_bank0_PA_word,
    input logic [3:0]                           stamofu_CAM_launch_bank0_byte_mask,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_CAM_launch_bank0_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_launch_bank0_mdp_info,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_launch_bank0_cq_index,
    input logic                                 stamofu_CAM_launch_bank0_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_launch_bank0_mq_index,

    input logic                                 stamofu_CAM_launch_bank1_valid,
    input logic [PA_WIDTH-2-1:0]                stamofu_CAM_launch_bank1_PA_word,
    input logic [3:0]                           stamofu_CAM_launch_bank1_byte_mask,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_CAM_launch_bank1_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_launch_bank1_mdp_info,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_launch_bank1_cq_index,
    input logic                                 stamofu_CAM_launch_bank1_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_launch_bank1_mq_index,

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
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   stamofu_mq_info_grab_mq_index,
    input logic [PA_WIDTH-2-1:0]            stamofu_mq_info_grab_PA_word,
    input logic [3:0]                       stamofu_mq_info_grab_byte_mask,
    input logic [31:0]                      stamofu_mq_info_ret_data,

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
    output logic                        rob_exception_page_fault,
    output logic                        rob_exception_access_fault,
    output logic                        rob_exception_misaligned_exception,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_exception_ROB_index,

    // store set commit update
        // implied no dep
    output logic                        ssu_commit_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_commit_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_commit_update_ROB_index,

    // oldest stamofu advertisement
    output logic                        stamofu_active,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_oldest_ROB_index,

    // ROB complete notif
    output logic                        stamofu_complete_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_complete_ROB_index,

    // op dequeue from acquire queue
    input logic                         stamofu_aq_deq_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_aq_deq_ROB_index,

    // ROB commit
    input logic [LOG_ROB_ENTRIES-3:0]   rob_commit_upper_index,
    input logic [3:0]                   rob_commit_lower_index_valid_mask,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

endmodule