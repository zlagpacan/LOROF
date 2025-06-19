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

    // central queue info ret
    output logic                            ldu_cq_info_ret_valid,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_ret_cq_index,
    output logic                            ldu_cq_info_ret_misaligned,
    output logic                            ldu_cq_info_ret_dtlb_hit,
    output logic                            ldu_cq_info_ret_page_fault,
    output logic                            ldu_cq_info_ret_access_fault,
    output logic                            ldu_cq_info_ret_dcache_hit,
    output logic                            ldu_cq_info_ret_is_mem,
    output logic                            ldu_cq_info_ret_aq_blocking,
    output logic [PA_WIDTH-2-1:0]           ldu_cq_info_ret_PA_word,
    output logic [3:0]                      ldu_cq_info_ret_byte_mask,
    output logic [31:0]                     ldu_cq_info_ret_data,

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
        // use cq_index ^
    output logic                            ldu_mq_info_ret_valid,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_ret_mq_index,

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
    input logic                                 ldu_CAM_launch_valid,
    input logic [PA_WIDTH-2-1:0]                ldu_CAM_launch_PA_word,
    input logic [3:0]                           ldu_CAM_launch_byte_mask,
    input logic [31:0]                          ldu_CAM_launch_write_data,
    input logic [MDPT_INFO_WIDTH-1:0]           ldu_CAM_launch_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]           ldu_CAM_launch_ROB_index,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    ldu_CAM_launch_cq_index, // stamofu_cq index
    input logic                                 ldu_CAM_launch_is_mq,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    ldu_CAM_launch_mq_index, // stamofu_mq index

    // ldu CAM return
    output logic                                ldu_CAM_return_valid,
    output logic                                ldu_CAM_return_forward,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    ldu_CAM_return_cq_index, // stamofu_cq index
    input logic                                 ldu_CAM_return_is_mq,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    ldu_CAM_return_mq_index, // stamofu_mq index

    // stamofu CAM return
    input logic                                 stamofu_CAM_return_valid,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_return_updated_mdp_info,
    input logic [3:0]                           stamofu_CAM_return_forward_byte_mask,
    input logic [31:0]                          stamofu_CAM_return_forward_data,
    input logic                                 stamofu_CAM_return_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_CAM_return_stall_count,
        // need to prevent issue of stamofu dependent entry doing an ldu_CAM just before 
        // this stamofu_CAM could update the stall count -> snoop active ldu_CAM's
        // prolly good idea to also have failsafe launch based on e.g. rob head index
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_return_cq_index, // ldu_cq index
    input logic                                 stamofu_CAM_return_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_return_mq_index, // ldu_mq index

    // store set CAM update
        // implied dep
    output logic                        ssu_CAM_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_ld_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_ld_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_stamo_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_stamo_ROB_index,

    // store set commit update
        // implied no dep
    output logic                        ssu_commit_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_commit_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_commit_update_ROB_index,

    // ROB commit
    input logic [LOG_ROB_ENTRIES-3:0]   rob_commit_upper_index,
    input logic [3:0]                   rob_commit_lower_index_valid_mask,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);
    
    // entry:
        // valid
        // killed
        // committed
        // op
            // need for realignment of bytes and signed vs unsigned
        // mdp info
        // dest PR
        // upper ROB index
        // lower ROB index one hot
        // WB sent
        // misaligned
        // mq index
        // mdp update req
        // forwarded
        // forwarded youngest ROB index
        // stalling
        // stall count
        // nasty forward
        // PA word
        // byte mask
        // return data
        // return request
        // restart request
        // page fault
        // access fault
    typedef struct packed {
        logic                               valid;
        logic                               killed;
        logic                               committed;
        logic                               WB_sent;
        logic                               mdp_update_req;
        logic                               misaligned;
        logic [LOG_LDU_MQ_ENTRIES-1:0]      mq_index;
        logic                               stalling;
        logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stall_count;
        logic                               forwarded;
        logic [LOG_ROB_ENTRIES-1:0]         forwarded_youngest_ROB_index;
        logic                               nasty_forward;
        logic                               return_req;
        logic                               restart_req;
        logic                               page_fault;
        logic                               access_fault;
        logic [3:0]                         op;
        logic [MDPT_INFO_WIDTH-1:0]         mdp_info;
        logic [LOG_PR_COUNT-1:0]            dest_PR;
        logic [LOG_ROB_ENTRIES-3:0]         upper_ROB_index;
        logic [3:0]                         lower_ROB_index_one_hot;
        logic [PA_WIDTH-3:0]                PA_word;
        logic [3:0]                         byte_mask;
        logic [31:0]                        return_data;
    } entry_t;

    entry_t [LDU_CQ_ENTRIES-1:0] entry_array;

endmodule