/*
    Filename: ldu_cq.sv
    Author: zlagpacan
    Description: RTL for Load Unit Central Queue
    Spec: LOROF/spec/design/ldu_cq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ldu_cq #(
    parameter LDU_CQ_ENTRIES = 40,
    parameter LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to central queue
    input logic                         ldu_cq_enq_valid,
    input logic                         ldu_cq_enq_killed,
    input logic [3:0]                   ldu_cq_enq_op,
    input logic [MDPT_INFO_WIDTH-1:0]   ldu_cq_enq_mdp_info,
    input logic [LOG_PR_COUNT-1:0]      ldu_cq_enq_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_cq_enq_ROB_index,
    
    // second try
    output logic                            second_try_valid,
    output logic                            second_try_is_mq,
    output logic                            second_try_misaligned,
    output logic                            second_try_page_fault,
    output logic                            second_try_access_fault,
    output logic                            second_try_is_mem,
    output logic [PPN_WIDTH-1:0]            second_try_PPN,
    output logic [PO_WIDTH-3:0]             second_try_PO_word,
    output logic [3:0]                      second_try_byte_mask,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   second_try_cq_index,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   second_try_mq_index,

    // second try feedback
    input logic                             second_try_ack,
    
    // data try
    output logic                            data_try_valid,
    output logic                            data_try_do_mispred,
    output logic [31:0]                     data_try_data,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   data_try_cq_index,

    // data try feedback
    input logic                             data_try_ack,

    // dtlb miss resp
    input logic                             dtlb_miss_resp_valid,
    input logic [PPN_WIDTH-1:0]             dtlb_miss_resp_PPN,
    input logic                             dtlb_miss_resp_is_mem,
    input logic                             dtlb_miss_resp_page_fault,
    input logic                             dtlb_miss_resp_access_fault,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    dtlb_miss_resp_cq_index,
    input logic                             dtlb_miss_resp_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    dtlb_miss_resp_mq_index,

    // dcache miss resp
    input logic                             dcache_miss_resp_valid,
    input logic [31:0]                      dcache_miss_resp_data,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    dcache_miss_resp_cq_index,
    input logic                             dcache_miss_resp_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    dcache_miss_resp_mq_index,

    // ldu CAM launch
    output logic                                ldu_CAM_launch_valid,
    output logic [PA_WIDTH-2-1:0]               ldu_CAM_launch_PA_word,
    output logic [3:0]                          ldu_CAM_launch_byte_mask,
    output logic [31:0]                         ldu_CAM_launch_write_data,
    output logic [MDPT_INFO_WIDTH-1:0]          ldu_CAM_launch_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]          ldu_CAM_launch_ROB_index,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   ldu_CAM_launch_cq_index,
    output logic                                ldu_CAM_launch_is_mq,
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   ldu_CAM_launch_mq_index,

    // ldu CAM return

    // stamofu CAM return

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);
    
    // entry:
        // valid
        // killed
        // op
            // need for realignment of bytes and signed vs unsigned
        // mdp info
        // dest PR
        // ROB index
        // WB sent
        // misaligned
        // mq index
        // matching mdp count
        // mdp update req
        // forwarded
        // forwarded ROB index
        // nasty forward
        // PA word
        // byte mask
        // return data
        // return request
        // restart request
        // page fault
        // access fault

endmodule