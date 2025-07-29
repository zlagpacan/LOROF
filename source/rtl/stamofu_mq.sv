/*
    Filename: stamofu_mq.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Misaligned Queue
    Spec: LOROF/spec/design/stamofu_mq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_mq #(
    parameter STAMOFU_MQ_ENTRIES = 4,
    parameter LOG_STAMOFU_MQ_ENTRIES = $clog2(STAMOFU_MQ_ENTRIES)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to misaligned queue
    input logic                                 stamofu_mq_enq_valid,

    // misaligned queue enqueue feedback
    output logic                                stamofu_mq_enq_ready,
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   stamofu_mq_enq_index,

    // misaligned queue info ret
    input logic                                 stamofu_mq_info_ret_bank0_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank0_cq_index,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank0_mq_index,
    input logic                                 stamofu_mq_info_ret_bank0_dtlb_hit,
    input logic                                 stamofu_mq_info_ret_bank0_page_fault,
    input logic                                 stamofu_mq_info_ret_bank0_access_fault,
    input logic                                 stamofu_mq_info_ret_bank0_is_mem,
    input logic [PA_WIDTH-2-1:0]                stamofu_mq_info_ret_bank0_PA_word,
    input logic [3:0]                           stamofu_mq_info_ret_bank0_byte_mask,
    input logic [31:0]                          stamofu_mq_info_ret_bank0_data,
    
    input logic                                 stamofu_mq_info_ret_bank1_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank1_cq_index,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_info_ret_bank1_mq_index,
    input logic                                 stamofu_mq_info_ret_bank1_dtlb_hit,
    input logic                                 stamofu_mq_info_ret_bank1_page_fault,
    input logic                                 stamofu_mq_info_ret_bank1_access_fault,
    input logic                                 stamofu_mq_info_ret_bank1_is_mem,
    input logic [PA_WIDTH-2-1:0]                stamofu_mq_info_ret_bank1_PA_word,
    input logic [3:0]                           stamofu_mq_info_ret_bank1_byte_mask,
    input logic [31:0]                          stamofu_mq_info_ret_bank1_data,

    // dtlb miss resp
    input logic                                 dtlb_miss_resp_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    dtlb_miss_resp_cq_index,
    input logic                                 dtlb_miss_resp_is_mq,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    dtlb_miss_resp_mq_index,
    input logic [PPN_WIDTH-1:0]                 dtlb_miss_resp_PPN,
    input logic                                 dtlb_miss_resp_is_mem,
    input logic                                 dtlb_miss_resp_page_fault,
    input logic                                 dtlb_miss_resp_access_fault,

    // ldu CAM launch from stamofu_mq
    output logic                                stamofu_mq_ldu_CAM_launch_valid,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_mq_ldu_CAM_launch_cq_index, // stamofu_cq index
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   stamofu_mq_ldu_CAM_launch_mq_index, // stamofu_mq index
    output logic [PA_WIDTH-2-1:0]               stamofu_mq_ldu_CAM_launch_PA_word,
    output logic [3:0]                          stamofu_mq_ldu_CAM_launch_byte_mask,
    output logic [31:0]                         stamofu_mq_ldu_CAM_launch_write_data,
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_mq_ldu_CAM_launch_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]          stamofu_mq_ldu_CAM_launch_ROB_index,

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
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_mq_CAM_return_bank0_cq_index,
    output logic                                stamofu_mq_CAM_return_bank0_stall,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_mq_CAM_return_bank0_stall_count,
    output logic [3:0]                          stamofu_mq_CAM_return_bank0_forward,
    output logic                                stamofu_mq_CAM_return_bank0_nasty_forward,
    output logic                                stamofu_mq_CAM_return_bank0_forward_ROB_index,
    output logic [31:0]                         stamofu_mq_CAM_return_bank0_forward_data,
    
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_mq_CAM_return_bank1_cq_index,
    output logic                                stamofu_mq_CAM_return_bank1_stall,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_mq_CAM_return_bank1_stall_count,
    output logic [3:0]                          stamofu_mq_CAM_return_bank1_forward,
    output logic                                stamofu_mq_CAM_return_bank1_nasty_forward,
    output logic                                stamofu_mq_CAM_return_bank1_forward_ROB_index,
    output logic [31:0]                         stamofu_mq_CAM_return_bank1_forward_data,

    // misaligned queue info grab
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_info_grab_mq_index,
    input logic                                 stamofu_mq_info_grab_clear_entry,
        // this is mechanism to clear mq entry (commit doesn't have to be tracked)
    output logic                                stamofu_mq_info_grab_is_mem,
    output logic [PA_WIDTH-2-1:0]               stamofu_mq_info_grab_PA_word,
    output logic [3:0]                          stamofu_mq_info_grab_byte_mask,
    output logic [31:0]                         stamofu_mq_info_grab_data,

    // stamofu mq complete notif
    output logic                                stamofu_mq_complete_valid,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_mq_complete_cq_index,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

endmodule