/*
    Filename: ldu_cq.sv
    Author: zlagpacan
    Description: RTL for Load Unit Central Queue
    Spec: LOROF/spec/design/ldu_cq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

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
    output logic                            second_try_bank0_valid,
    output logic                            second_try_bank1_valid,

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
    input logic                             second_try_bank0_ack,
    input logic                             second_try_bank1_ack,
    
    // data try
    output logic                            data_try_bank0_valid,
    output logic                            data_try_bank1_valid,

    output logic                            data_try_do_mispred,
    output logic [31:0]                     data_try_data,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   data_try_cq_index,

    // data try feedback
    input logic                             data_try_bank0_ack,
    input logic                             data_try_bank1_ack,

    // misaligned queue data try req
    input logic                             ldu_mq_data_try_req_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_mq_data_try_cq_index,

    // misaligned queue info grab
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_grab_mq_index,
    input logic [31:0]                      ldu_mq_info_grab_data,
    
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_grab_data_try_ack,

    // central queue info grab
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_cq_info_grab_bank0_cq_index,
    output logic [3:0]                      ldu_cq_info_grab_bank0_op,
    output logic [MDPT_INFO_WIDTH-1:0]      ldu_cq_info_grab_bank0_mdp_info,
    output logic [LOG_PR_COUNT-1:0]         ldu_cq_info_grab_bank0_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]      ldu_cq_info_grab_bank0_ROB_index,

    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_cq_info_grab_bank1_cq_index,
    output logic [3:0]                      ldu_cq_info_grab_bank1_op,
    output logic [MDPT_INFO_WIDTH-1:0]      ldu_cq_info_grab_bank1_mdp_info,
    output logic [LOG_PR_COUNT-1:0]         ldu_cq_info_grab_bank1_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]      ldu_cq_info_grab_bank1_ROB_index,

    // central queue info ret
    input logic                             ldu_cq_info_ret_bank0_valid,
    input logic                             ldu_cq_info_ret_bank0_WB_sent,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_cq_info_ret_bank0_cq_index,
    input logic                             ldu_cq_info_ret_bank0_misaligned,
    input logic                             ldu_cq_info_ret_bank0_dtlb_hit,
    input logic                             ldu_cq_info_ret_bank0_page_fault,
    input logic                             ldu_cq_info_ret_bank0_access_fault,
    input logic                             ldu_cq_info_ret_bank0_dcache_hit,
    input logic                             ldu_cq_info_ret_bank0_is_mem,
    input logic                             ldu_cq_info_ret_bank0_aq_blocking,
    input logic [PA_WIDTH-2-1:0]            ldu_cq_info_ret_bank0_PA_word,
    input logic [3:0]                       ldu_cq_info_ret_bank0_byte_mask,
    input logic [31:0]                      ldu_cq_info_ret_bank0_data,
    
    input logic                             ldu_cq_info_ret_bank1_valid,
    input logic                             ldu_cq_info_ret_bank1_WB_sent,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_cq_info_ret_bank1_cq_index,
    input logic                             ldu_cq_info_ret_bank1_misaligned,
    input logic                             ldu_cq_info_ret_bank1_dtlb_hit,
    input logic                             ldu_cq_info_ret_bank1_page_fault,
    input logic                             ldu_cq_info_ret_bank1_access_fault,
    input logic                             ldu_cq_info_ret_bank1_dcache_hit,
    input logic                             ldu_cq_info_ret_bank1_is_mem,
    input logic                             ldu_cq_info_ret_bank1_aq_blocking,
    input logic [PA_WIDTH-2-1:0]            ldu_cq_info_ret_bank1_PA_word,
    input logic [3:0]                       ldu_cq_info_ret_bank1_byte_mask,
    input logic [31:0]                      ldu_cq_info_ret_bank1_data,

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
        // use cq_index ^
    input logic                             ldu_mq_info_ret_bank0_valid,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_mq_info_ret_bank0_mq_index,
    
    input logic                             ldu_mq_info_ret_bank1_valid,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_mq_info_ret_bank1_mq_index,

    // dtlb miss resp
    input logic                             dtlb_miss_resp_valid,
    input logic                             dtlb_miss_resp_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    dtlb_miss_resp_mq_index,
    input logic [PPN_WIDTH-1:0]             dtlb_miss_resp_PPN,
    input logic                             dtlb_miss_resp_is_mem,
    input logic                             dtlb_miss_resp_page_fault,
    input logic                             dtlb_miss_resp_access_fault,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    dtlb_miss_resp_cq_index,

    // dcache miss resp
    input logic                             dcache_miss_resp_valid,
    input logic                             dcache_miss_resp_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    dcache_miss_resp_mq_index,
    input logic [31:0]                      dcache_miss_resp_data,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    dcache_miss_resp_cq_index,

    // stamofu CAM return
    input logic                                 stamofu_CAM_return_bank0_valid,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_return_bank0_updated_mdp_info,
    input logic                                 stamofu_CAM_return_bank0_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_CAM_return_bank0_stall_count,
    input logic [3:0]                           stamofu_CAM_return_bank0_forward,
    input logic                                 stamofu_CAM_return_bank0_nasty_forward,
    input logic                                 stamofu_CAM_return_bank0_forward_ROB_index,
    input logic [31:0]                          stamofu_CAM_return_bank0_forward_data,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_return_bank0_cq_index, // ldu_cq index
    input logic                                 stamofu_CAM_return_bank0_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_return_bank0_mq_index, // ldu_mq index
    
    input logic                                 stamofu_CAM_return_bank1_valid,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_return_bank1_updated_mdp_info,
    input logic                                 stamofu_CAM_return_bank1_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_CAM_return_bank1_stall_count,
    input logic [3:0]                           stamofu_CAM_return_bank1_forward,
    input logic                                 stamofu_CAM_return_bank1_nasty_forward,
    input logic                                 stamofu_CAM_return_bank1_forward_ROB_index,
    input logic [31:0]                          stamofu_CAM_return_bank1_forward_data,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_return_bank1_cq_index, // ldu_cq index
    input logic                                 stamofu_CAM_return_bank1_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_return_bank1_mq_index, // ldu_mq index

    // ldu CAM launch
    input logic                                 ldu_CAM_launch_valid,
    input logic                                 ldu_CAM_launch_is_amo,
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
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   ldu_CAM_return_cq_index, // stamofu_cq index
    output logic                                ldu_CAM_return_is_mq,
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   ldu_CAM_return_mq_index, // stamofu_mq index

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

    // acquire advertisement
    input logic                         stamofu_aq_mem_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_mem_aq_oldest_abs_ROB_index,
    input logic                         stamofu_aq_io_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_io_aq_oldest_abs_ROB_index,

    // oldest stamofu advertisement
    input logic                         stamofu_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_oldest_ROB_index,

    // ROB complete notif
    output logic                        ldu_complete_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  ldu_complete_ROB_index,

    // ROB commit
    input logic [LOG_ROB_ENTRIES-3:0]   rob_commit_upper_index,
    input logic [3:0]                   rob_commit_lower_index_valid_mask,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

    // need to prevent issue of stamofu dependent entry doing an ldu_CAM just before 
        // this ldu_CAM could update the stall count -> snoop active ldu_CAM's
        // prolly good idea to also have failsafe launch based on e.g. rob head index
    // OR: race doesn't exist if stamofu launches ldu_CAM from stamofu_cq/mq
        // instead of stamofu_launch_pipeline
        // this is 1 cycle and bunch of more logic tho (unnecessary PE's)
        // actually, need this for functionality: was missing stamofu dtlb miss path to ldu_CAM

    // if mq entry not ready but cq entry tries, will get cancelled when arbitrated for, 
        // and this single arbitrated entry can mux into the mq entry when trying to
        // arrange the data bytes
        // essentially:
            // on cq return, always try data return
                // if all hits, mq return will come in next cycle, data will be there to collect
                    // after arbitration cycle for cq data return, so all good
            // on mq return, only return if cq entry ready and not already trying data return

    // ----------------------------------------------------------------
    // Signals:

    typedef struct packed {
        logic                               valid;
        logic                               misaligned;
        logic [LOG_LDU_MQ_ENTRIES-1:0]      mq_index;
        logic                               killed;
        logic                               dtlb_hit;
        logic                               stamofu_CAM_returned;
        logic                               dcache_hit;
        logic                               aq_blocking;
        logic                               older_stamofu_active;
        logic                               stalling;
        logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stalling_count;
        logic                               forward;
        logic                               nasty_forward;
        logic                               previous_nasty_forward;
        logic [LOG_ROB_ENTRIES-1:0]         forward_ROB_index;
        logic                               mdp_present;
        logic                               WB_sent;
        logic                               complete;
        logic                               committed;
        logic                               second_try_req;
        logic                               unblock_data_try_req;
        logic                               new_data_try_req;
        logic                               data_try_req;
        logic                               data_try_just_sent;
        logic                               complete_req;
        logic                               page_fault;
        logic                               access_fault;
        logic                               is_mem;
        logic [3:0]                         op;
        logic [MDPT_INFO_WIDTH-1:0]         mdp_info;
        logic [LOG_PR_COUNT-1:0]            dest_PR;
        logic [LOG_ROB_ENTRIES-1:0]         ROB_index;
        logic [3:0]                         lower_ROB_index_one_hot;
        logic [PA_WIDTH-3:0]                PA_word;
        logic [3:0]                         byte_mask;
        logic                               bank;
        logic [31:0]                        data;
    } entry_t;

    entry_t [LDU_CQ_ENTRIES-1:0] entry_array, next_entry_array;

    logic [LOG_LDU_CQ_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_LDU_CQ_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    logic enq_perform;
    logic deq_perform;

    logic [LDU_CQ_ENTRIES-1:0] ldu_cq_info_ret_bank0_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] ldu_cq_info_ret_bank1_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] ldu_mq_info_ret_bank0_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] ldu_mq_info_ret_bank1_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] dtlb_miss_resp_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] dcache_miss_resp_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] ldu_mq_data_try_req_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] stamofu_CAM_return_bank0_valid_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] stamofu_CAM_return_bank1_valid_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] wraparound_mask;

    logic [LDU_CQ_ENTRIES-1:0] second_try_unmasked_req_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_unmasked_req_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_unmasked_req_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] second_try_masked_req_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_masked_req_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_masked_req_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] second_try_unmasked_req_ack_one_hot_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_unmasked_req_ack_one_hot_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_unmasked_req_ack_one_hot_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] second_try_unmasked_req_ack_index_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_unmasked_req_ack_index_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_unmasked_req_ack_index_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] second_try_masked_req_ack_one_hot_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_masked_req_ack_one_hot_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_masked_req_ack_one_hot_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] second_try_masked_req_ack_index_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_masked_req_ack_index_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_masked_req_ack_index_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] second_try_req_ack_one_hot_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_req_ack_one_hot_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_req_ack_one_hot_by_entry;

    logic [LDU_CQ_ENTRIES-1:0] second_try_req_ack_index_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] data_try_req_ack_index_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] complete_req_ack_index_by_entry;

    logic second_try_valid;
    logic data_try_valid;

    logic second_try_req_not_accepted;
    logic data_try_req_not_accepted;

    logic potential_data_try_valid;

    logic ldu_complete_cq_index;

    logic [LDU_CQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0] rel_ROB_index_by_entry;
    
    logic [LDU_CQ_ENTRIES-1:0] ldu_CAM_launch_forward_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] ldu_CAM_launch_nasty_forward_by_entry;
    logic [LDU_CQ_ENTRIES-1:0] stalling_count_subtract_by_entry;

    // ----------------------------------------------------------------
    // Logic:

    assign enq_ptr_plus_1 = (enq_ptr == LDU_CQ_ENTRIES-1) ? 0 : enq_ptr + 1;
    assign deq_ptr_plus_1 = (deq_ptr == LDU_CQ_ENTRIES-1) ? 0 : deq_ptr + 1;

    // event demux to entry
        // ldu_cq return
            // 2x banks
        // ldu_mq return
            // 2x banks
        // dtlb miss resp
        // dcache miss resp
        // stamofu CAM return
            // 2x banks
        // ldu_mq data try req
    always_comb begin
        ldu_cq_info_ret_bank0_valid_by_entry = '0;
        ldu_cq_info_ret_bank1_valid_by_entry = '0;
        ldu_mq_info_ret_bank0_valid_by_entry = '0;
        ldu_mq_info_ret_bank1_valid_by_entry = '0;
        dtlb_miss_resp_valid_by_entry = '0;
        dcache_miss_resp_valid_by_entry = '0;
        ldu_mq_data_try_req_valid_by_entry = '0;
        stamofu_CAM_return_bank0_valid_by_entry = '0;
        stamofu_CAM_return_bank1_valid_by_entry = '0;

        ldu_cq_info_ret_bank0_valid_by_entry[ldu_cq_info_ret_bank0_cq_index] = ldu_cq_info_ret_bank0_valid;
        ldu_cq_info_ret_bank1_valid_by_entry[ldu_cq_info_ret_bank1_cq_index] = ldu_cq_info_ret_bank1_valid;
        ldu_mq_info_ret_bank0_valid_by_entry[ldu_cq_info_ret_bank0_cq_index] = ldu_mq_info_ret_bank0_valid;
        ldu_mq_info_ret_bank1_valid_by_entry[ldu_cq_info_ret_bank1_cq_index] = ldu_mq_info_ret_bank1_valid;
        dtlb_miss_resp_valid_by_entry[dtlb_miss_resp_cq_index] = dtlb_miss_resp_valid & ~dtlb_miss_resp_is_mq;
        dcache_miss_resp_valid_by_entry[dcache_miss_resp_cq_index] = dcache_miss_resp_valid & ~dcache_miss_resp_is_mq;
        ldu_mq_data_try_req_valid_by_entry[ldu_mq_data_try_cq_index] = ldu_mq_data_try_req_valid;
        stamofu_CAM_return_bank0_valid_by_entry[stamofu_CAM_return_bank0_cq_index] = stamofu_CAM_return_bank0_valid & ~stamofu_CAM_return_bank0_is_mq;
        stamofu_CAM_return_bank1_valid_by_entry[stamofu_CAM_return_bank1_cq_index] = stamofu_CAM_return_bank1_valid & ~stamofu_CAM_return_bank1_is_mq;
    end

    // request PE's
    always_comb begin
        for (int i = 0; i < LDU_CQ_ENTRIES; i++) begin
            second_try_unmasked_req_by_entry[i] = entry_array[i].second_try_req;
            data_try_unmasked_req_by_entry[i] = entry_array[i].data_try_req;
            complete_unmasked_req_by_entry[i] = entry_array[i].complete_req;
        end
        second_try_masked_req_by_entry = second_try_unmasked_req_by_entry & wraparound_mask;
        data_try_masked_req_by_entry = data_try_unmasked_req_by_entry & wraparound_mask;
        complete_masked_req_by_entry = complete_unmasked_req_by_entry & wraparound_mask;
    end
    pe_lsb # (
        .WIDTH(LDU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) SECOND_TRY_UNMASKED_PE (
        .req_vec(second_try_unmasked_req_by_entry),
        .ack_one_hot(second_try_unmasked_req_ack_one_hot_by_entry),
        .ack_index(second_try_unmasked_req_ack_index_by_entry)
    );
    pe_lsb # (
        .WIDTH(LDU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) SECOND_TRY_MASKED_PE (
        .req_vec(second_try_masked_req_by_entry),
        .ack_one_hot(second_try_masked_req_ack_one_hot_by_entry),
        .ack_index(second_try_masked_req_ack_index_by_entry)
    );
    pe_lsb # (
        .WIDTH(LDU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) DATA_TRY_UNMASKED_PE (
        .req_vec(data_try_unmasked_req_by_entry),
        .ack_one_hot(data_try_unmasked_req_ack_one_hot_by_entry),
        .ack_index(data_try_unmasked_req_ack_index_by_entry)
    );
    pe_lsb # (
        .WIDTH(LDU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) DATA_TRY_MASKED_PE (
        .req_vec(data_try_masked_req_by_entry),
        .ack_one_hot(data_try_masked_req_ack_one_hot_by_entry),
        .ack_index(data_try_masked_req_ack_index_by_entry)
    );
    pe_lsb # (
        .WIDTH(LDU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) COMPLETE_UNMASKED_PE (
        .req_vec(complete_unmasked_req_by_entry),
        .ack_one_hot(complete_unmasked_req_ack_one_hot_by_entry),
        .ack_index(complete_unmasked_req_ack_index_by_entry)
    );
    pe_lsb # (
        .WIDTH(LDU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) COMPLETE_MASKED_PE (
        .req_vec(complete_masked_req_by_entry),
        .ack_one_hot(complete_masked_req_ack_one_hot_by_entry),
        .ack_index(complete_masked_req_ack_index_by_entry)
    );
    always_comb begin
        if (|second_try_masked_req_by_entry) begin
            second_try_req_ack_one_hot_by_entry = second_try_masked_req_ack_one_hot_by_entry;
            second_try_req_ack_index_by_entry = second_try_masked_req_ack_index_by_entry;
        end else begin
            second_try_req_ack_one_hot_by_entry = second_try_unmasked_req_ack_one_hot_by_entry;
            second_try_req_ack_index_by_entry = second_try_unmasked_req_ack_index_by_entry;
        end
        if (|data_try_masked_req_by_entry) begin
            data_try_req_ack_one_hot_by_entry = data_try_masked_req_ack_one_hot_by_entry;
            data_try_req_ack_index_by_entry = data_try_masked_req_ack_index_by_entry;
        end else begin
            data_try_req_ack_one_hot_by_entry = data_try_unmasked_req_ack_one_hot_by_entry;
            data_try_req_ack_index_by_entry = data_try_unmasked_req_ack_index_by_entry;
        end
        if (|complete_masked_req_by_entry) begin
            complete_req_ack_one_hot_by_entry = complete_masked_req_ack_one_hot_by_entry;
            complete_req_ack_index_by_entry = complete_masked_req_ack_index_by_entry;
        end else begin
            complete_req_ack_one_hot_by_entry = complete_unmasked_req_ack_one_hot_by_entry;
            complete_req_ack_index_by_entry = complete_unmasked_req_ack_index_by_entry;
        end
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            second_try_valid <= 1'b0;
            second_try_cq_index <= 0;
        end
        else if (~second_try_req_not_accepted) begin
            second_try_valid <= |second_try_unmasked_req_by_entry;
            second_try_cq_index <= second_try_req_ack_index_by_entry;
        end
    end
    always_comb begin
        second_try_bank0_valid = second_try_valid & (entry_array[second_try_cq_index].bank == 1'b0);
        second_try_bank1_valid = second_try_valid & (entry_array[second_try_cq_index].bank == 1'b1);

        second_try_is_mq = 1'b0;
        second_try_misaligned = entry_array[second_try_cq_index].misaligned;
        second_try_page_fault = entry_array[second_try_cq_index].page_fault;
        second_try_access_fault = entry_array[second_try_cq_index].access_fault;
        second_try_is_mem = entry_array[second_try_cq_index].is_mem;
        second_try_PPN = entry_array[second_try_cq_index].PA_word[PA_WIDTH-3:PA_WIDTH-2-PPN_WIDTH];
        second_try_PO_word = entry_array[second_try_cq_index].PA_word[PA_WIDTH-2-PPN_WIDTH-1:0];
        second_try_byte_mask = entry_array[second_try_cq_index].byte_mask;
        second_try_mq_index = entry_array[second_try_cq_index].mq_index;

        second_try_req_not_accepted = 
            second_try_bank0_valid & ~second_try_bank0_ack
            | second_try_bank1_valid & ~second_try_bank1_ack;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            potential_data_try_valid <= 1'b0;
            data_try_cq_index <= 0;
        end
        else if (~data_try_req_not_accepted) begin
            potential_data_try_valid <= |data_try_unmasked_req_by_entry;
            data_try_cq_index <= data_try_req_ack_index_by_entry;
        end
    end
    always_comb begin
        if (entry_array[data_try_cq_index].misaligned) begin
            data_try_bank0_valid = potential_data_try_valid & ldu_mq_info_grab_data_try_req & (entry_array[data_try_cq_index].bank == 1'b0);
            data_try_bank1_valid = potential_data_try_valid & ldu_mq_info_grab_data_try_req & (entry_array[data_try_cq_index].bank == 1'b1);
            
            // arrange misaligned data:
            
            // LW
            if (entry_array[data_try_cq_index].op[1]) begin
                // 4'b1110, 4'b0001
                if (entry_array[data_try_cq_index].byte_mask[1]) begin
                    data_try_data = {ldu_mq_info_grab_data[7:0], entry_array[data_try_cq_index].data[31:8]};
                end
                // 4'b1100, 4'b0011
                else if (entry_array[data_try_cq_index].byte_mask[2]) begin
                    data_try_data = {ldu_mq_info_grab_data[15:0], entry_array[data_try_cq_index].data[31:16]};
                end
                // 4'b1000, 4'b0111
                else begin
                    data_try_data = {ldu_mq_info_grab_data[23:0], entry_array[data_try_cq_index].data[31:24]};
                end
            end
            // otherwise, LH, LHU
                // 4'b1000, 4'b0001
            else begin
                // LHU: unsigned
                if (entry_array[data_try_cq_index].op[2]) begin
                    data_try_data = {16'h0000, ldu_mq_info_grab_data[7:0], entry_array[data_try_cq_index].data[31:24]};
                end
                // LH: signed
                else begin
                    data_try_data = {{16{ldu_mq_info_grab_data[7]}}, ldu_mq_info_grab_data[7:0], entry_array[data_try_cq_index].data[31:24]};
                end
            end

            ldu_mq_info_grab_data_try_ack = 1'b1;
        end else begin
            data_try_bank0_valid = potential_data_try_valid & (entry_array[data_try_cq_index].bank == 1'b0);
            data_try_bank1_valid = potential_data_try_valid & (entry_array[data_try_cq_index].bank == 1'b1);

            data_try_data = entry_array[data_try_cq_index].data;

            ldu_mq_info_grab_data_try_ack = 1'b0;
        end
        data_try_do_mispred = entry_array[data_try_cq_index].WB_sent;

        ldu_mq_info_grab_mq_index = entry_array[data_try_cq_index].mq_index;

        data_try_req_not_accepted = 
            data_try_bank0_valid & ~data_try_bank0_ack
            | data_try_bank1_valid & ~data_try_bank1_ack;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            ldu_complete_valid <= 1'b0;
            ldu_complete_cq_index <= 0;
        end
        else begin
            ldu_complete_valid <= |complete_unmasked_req_by_entry;
            ldu_complete_cq_index <= complete_req_ack_index_by_entry;
        end
    end
    always_comb begin
        ldu_complete_ROB_index = entry_array[ldu_complete_cq_index].ROB_index;
    end

    // per-entry state machine
        // external events:
            // ldu_cq return
                // 2x banks
            // ldu_mq return
                // 2x banks
            // dtlb miss resp
            // dcache miss resp
            // stamofu CAM return
                // 2x banks
            // ldu CAM
            // ldu_mq data try req
            // second try req ack
            // data try req ack
            // complete req ack
            // aq age
            // oldest stamofu age
            // nasty forward stamofu age
            // ROB commit
            // ROB kill
    always_comb begin
        next_entry_array = entry_array;

        for (int i = 0; i < LDU_CQ_ENTRIES; i++) begin
            rel_ROB_index_by_entry[i] = entry_array[i].ROB_index - rob_kill_abs_head_index;

            next_entry_array[i].unblock_data_try_req = 1'b0;
            next_entry_array[i].new_data_try_req = 1'b0;

            // events with priority
                // ldu_cq bank 0
                // ldu_cq bank 1
                // stamofu CAM return bank 0
                // stamofu CAM return bank 1
                // ldu CAM
                // dcache miss resp

            // ldu_cq bank 0
            if (ldu_cq_info_ret_bank0_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                next_entry_array[i].misaligned = ldu_cq_info_ret_bank0_misaligned;
                // next_entry_array[i].mq_index = 
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = ldu_cq_info_ret_bank0_dtlb_hit;
                // next_entry_array[i].stamofu_CAM_returned = 
                next_entry_array[i].dcache_hit = ldu_cq_info_ret_bank0_dcache_hit;
                next_entry_array[i].aq_blocking = ldu_cq_info_ret_bank0_aq_blocking;
                // next_entry_array[i].older_stamofu_active = 
                // next_entry_array[i].stalling = 
                // next_entry_array[i].stalling_count = 
                // next_entry_array[i].forward = 
                // next_entry_array[i].nasty_forward = 
                // next_entry_array[i].previous_nasty_forward = 
                // next_entry_array[i].forward_ROB_index = 
                // next_entry_array[i].mdp_present = 
                next_entry_array[i].WB_sent |= ldu_cq_info_ret_bank0_WB_sent;
                // next_entry_array[i].complete = 
                // next_entry_array[i].committed = 
                // next_entry_array[i].second_try_req = 
                // next_entry_array[i].unblock_data_try_req = 
                // next_entry_array[i].new_data_try_req = 
                // next_entry_array[i].data_try_req = 
                // next_entry_array[i].data_try_just_sent = 
                // next_entry_array[i].complete_req = 
                next_entry_array[i].page_fault = ldu_cq_info_ret_bank0_page_fault;
                next_entry_array[i].access_fault = ldu_cq_info_ret_bank0_access_fault;
                next_entry_array[i].is_mem = ldu_cq_info_ret_bank0_is_mem;
                // next_entry_array[i].op = 
                // next_entry_array[i].mdp_info = 
                // next_entry_array[i].dest_PR = 
                // next_entry_array[i].ROB_index = 
                // next_entry_array[i].lower_ROB_index_one_hot = 
                next_entry_array[i].PA_word = ldu_cq_info_ret_bank0_PA_word;
                next_entry_array[i].byte_mask = ldu_cq_info_ret_bank0_byte_mask;
                next_entry_array[i].bank = ldu_cq_info_ret_bank0_PA_word[DCACHE_WORD_ADDR_BANK_BIT];
                next_entry_array[i].data = ldu_cq_info_ret_bank0_data;

                // trigger unblock data try req
                    // will needlessly try for all cases except misaligned
                        // if misaligned conditions are favorable, will do data try as needed
                        // else no data try
                next_entry_array[i].unblock_data_try_req = 1'b1;
                // next_entry_array[i].new_data_try_req = 
            end
            // ldu_cq bank 1
            else if (ldu_cq_info_ret_bank1_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                next_entry_array[i].misaligned = ldu_cq_info_ret_bank1_misaligned;
                // next_entry_array[i].mq_index = 
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = ldu_cq_info_ret_bank1_dtlb_hit;
                // next_entry_array[i].stamofu_CAM_returned = 
                next_entry_array[i].dcache_hit = ldu_cq_info_ret_bank1_dcache_hit;
                next_entry_array[i].aq_blocking = ldu_cq_info_ret_bank1_aq_blocking;
                // next_entry_array[i].older_stamofu_active = 
                // next_entry_array[i].stalling = 
                // next_entry_array[i].stalling_count = 
                // next_entry_array[i].forward = 
                // next_entry_array[i].nasty_forward = 
                // next_entry_array[i].previous_nasty_forward = 
                // next_entry_array[i].forward_ROB_index = 
                // next_entry_array[i].mdp_present = 
                next_entry_array[i].WB_sent |= ldu_cq_info_ret_bank1_WB_sent;
                // next_entry_array[i].complete = 
                // next_entry_array[i].committed = 
                // next_entry_array[i].second_try_req = 
                // next_entry_array[i].unblock_data_try_req = 
                // next_entry_array[i].new_data_try_req = 
                // next_entry_array[i].data_try_req = 
                // next_entry_array[i].data_try_just_sent = 
                // next_entry_array[i].complete_req = 
                next_entry_array[i].page_fault = ldu_cq_info_ret_bank1_page_fault;
                next_entry_array[i].access_fault = ldu_cq_info_ret_bank1_access_fault;
                next_entry_array[i].is_mem = ldu_cq_info_ret_bank1_is_mem;
                // next_entry_array[i].op = 
                // next_entry_array[i].mdp_info = 
                // next_entry_array[i].dest_PR = 
                // next_entry_array[i].ROB_index = 
                // next_entry_array[i].lower_ROB_index_one_hot = 
                next_entry_array[i].PA_word = ldu_cq_info_ret_bank1_PA_word;
                next_entry_array[i].byte_mask = ldu_cq_info_ret_bank1_byte_mask;
                next_entry_array[i].bank = ldu_cq_info_ret_bank1_PA_word[DCACHE_WORD_ADDR_BANK_BIT];
                next_entry_array[i].data = ldu_cq_info_ret_bank1_data;

                // trigger unblock data try req
                    // will needlessly try for all cases except misaligned
                        // if misaligned conditions are favorable, will do data try as needed
                        // else no data try
                next_entry_array[i].unblock_data_try_req = 1'b1;
                // next_entry_array[i].new_data_try_req = 
            end
            // stamofu CAM return bank 0
            else if (stamofu_CAM_return_bank0_valid_by_entry[i]) begin
                next_entry_array[i].stamofu_CAM_returned = 1'b1;
                next_entry_array[i].mdp_info = stamofu_CAM_return_bank0_updated_mdp_info;
                next_entry_array[i].stalling = stamofu_CAM_return_bank0_stall;
                next_entry_array[i].stalling_count = stamofu_CAM_return_bank0_stall_count;
                next_entry_array[i].forward = stamofu_CAM_return_bank0_forward;
                next_entry_array[i].nasty_forward = stamofu_CAM_return_bank0_nasty_forward;
                next_entry_array[i].forward_ROB_index = stamofu_CAM_return_bank0_forward_ROB_index;
                
                // only update data if miss resp or CAM forward
                if (stamofu_CAM_return_bank0_forward) begin
                    next_entry_array[i].data = stamofu_CAM_return_bank0_forward_data;
                end
                else if (dcache_miss_resp_valid_by_entry[i]) begin
                    next_entry_array[i].data = dcache_miss_resp_data;
                end

                // trigger new data try req if forward or dcache miss resp
                next_entry_array[i].new_data_try_req |= stamofu_CAM_return_bank0_forward | dcache_miss_resp_valid_by_entry[i];
            end
            // stamofu CAM return bank 1
            else if (stamofu_CAM_return_bank1_valid_by_entry[i]) begin
                next_entry_array[i].stamofu_CAM_returned = 1'b1;
                next_entry_array[i].mdp_info = stamofu_CAM_return_bank1_updated_mdp_info;
                next_entry_array[i].stalling = stamofu_CAM_return_bank1_stall;
                next_entry_array[i].stalling_count = stamofu_CAM_return_bank1_stall_count;
                next_entry_array[i].forward = stamofu_CAM_return_bank1_forward;
                next_entry_array[i].nasty_forward = stamofu_CAM_return_bank1_nasty_forward;
                next_entry_array[i].forward_ROB_index = stamofu_CAM_return_bank1_forward_ROB_index;
                
                // only update data if miss resp or CAM forward
                if (stamofu_CAM_return_bank1_forward) begin
                    next_entry_array[i].data = stamofu_CAM_return_bank1_forward_data;
                end
                else if (dcache_miss_resp_valid_by_entry[i]) begin
                    next_entry_array[i].data = dcache_miss_resp_data;
                end

                // trigger new data try req if forward or dcache miss resp
                next_entry_array[i].new_data_try_req = |= stamofu_CAM_return_bank1_forward | dcache_miss_resp_valid_by_entry[i];
            end
            // ldu CAM forward
                // subset of stamofu CAM return
            else if (ldu_CAM_launch_forward_by_entry[i]) begin
                next_entry_array[i].forward = 1'b1;
                next_entry_array[i].nasty_forward = 1'b0;
                next_entry_array[i].forward_ROB_index = ldu_CAM_launch_ROB_index;

                next_entry_array[i].data = ldu_CAM_launch_write_data;

                // trigger new data try req
                next_entry_array[i].new_data_try_req = 1'b1;
            end
            // ldu CAM nasty forward
                // subset of stamofu CAM return
            else if (ldu_CAM_launch_nasty_forward_by_entry[i]) begin
                next_entry_array[i].forward = 1'b0;
                next_entry_array[i].nasty_forward = 1'b1;
                next_entry_array[i].forward_ROB_index = ldu_CAM_launch_ROB_index;

                // trigger new data try req
                next_entry_array[i].new_data_try_req = 1'b1;
            end
            // dcache miss resp
                // this is only case where take dcache miss resp data
            else if (dcache_miss_resp_valid_by_entry[i] & ~entry_array[i].forward & ~entry_array[i].nasty_forward) begin
                next_entry_array[i].data = dcache_miss_resp_data;

                // trigger new data try req
                next_entry_array[i].new_data_try_req = 1'b1;
            end

            // indep behavior:

            // ready for data try req
                // check data try req triggered and haven't already sent data OR have new data
                // new data try req OR WB not sent
                // not killed OR (not data try req AND not data try just sent AND WB not sent)
                    // this makes sure do 1 WB even if killed, but prevent extra unneeded WB's
                // dtlb hit
                // aq not blocking
                // forward OR dcache_hit
                // no nasty forward
                // no mem dep pred OR stamofu_CAM_returned
                // not stalling OR stamofu inactive OR no older stamofu active
                    // this is short circuit in case never escape stall count
            if (
                (
                    (   
                        entry_array[i].unblock_data_try_req 
                        & ~entry_array.data_try_req 
                        & ~entry_array[i].data_try_just_sent 
                        & ~entry_array[i].WB_sent
                    )
                    | entry_array[i].new_data_try_req
                )
                & (
                    ~entry_array[i].killed
                    | (~entry_array.data_try_req & ~entry_array[i].data_try_just_sent & ~entry_array[i].WB_sent)
                )
                & entry_array[i].dtlb_hit
                & ~entry_array[i].aq_blocking
                & (entry_array[i].forward | entry_array[i].dcache_hit)
                & ~entry_array[i].nasty_forward
                & (~entry_array[i].mdp_present | entry_array[i].stamofu_cam_returned)
                & (~entry_array[i].stalling | ~stamofu_active | ~entry_array[i].older_stamofu_active)
            ) begin
                next_entry_array[i].data_try_req = 1'b1;
            end

            // ready for complete req
                // not complete
                // no complete req
                // ~older_stamofu_active OR killed
                    // faster complete if killed
                // WB_sent
                    // WB_sent also performed for excepting load's in launch pipeline
                        // upon first try if got dtlb hit, or on second try if got dtlb miss
                    // need even if killed to make sure killed dependents complete
            if (
                ~entry_array[i].complete
                & ~entry_array[i].complete_req
                & (~entry_array[i].older_stamofu_active | entry_array[i].killed)
                & entry_array[i].WB_sent

                // also can't be in any part of data try process
                    // beware of possible race where complete arrives just before data try mispred restart
                & ~entry_array[i].unblock_data_try_req
                & ~entry_array[i].new_data_try_req
                & ~entry_array[i].data_try_req
                & ~entry_array[i].data_try_just_sent
            ) begin
                next_entry_array[i].complete_req = 1'b1;
            end

            // dcache miss return (indep)
                // only setting of dcache hit is indep
            if (dcache_miss_resp_valid_by_entry[i]) begin
                next_entry_array[i].dcache_hit = 1'b1;
            end

            // dtlb miss return (indep)
            if (dtlb_miss_resp_valid_by_entry[i]) begin
                next_entry_array[i].dtlb_hit = 1'b1;
                next_entry_array[i].PA_word = dtlb_miss_resp_PPN[PA_WIDTH-3:PA_WIDTH-2-PPN_WIDTH];
                next_entry_array[i].is_mem = dtlb_miss_resp_is_mem;
                next_entry_array[i].page_fault = dtlb_miss_resp_page_fault;
                next_entry_array[i].access_fault = dtlb_miss_resp_access_fault;

                // second try req
                next_entry_array[i].second_try_req = 1'b1;
            end

            // ldu_mq return (indep)
            if (ldu_mq_info_ret_bank0_valid_by_entry[i]) begin
                next_entry_array[i].mq_index = ldu_mq_info_ret_bank0_mq_index;
            end
            if (ldu_mq_info_ret_bank1_valid_by_entry[i]) begin
                next_entry_array[i].mq_index = ldu_mq_info_ret_bank1_mq_index;
            end

            // ldu_mq data try (indep)
                // special data try req set here which is trigger for data try if not already doing it
                    // if already triggered recently, mq data will be present in time to provide for data try retrieval
                // don't want to treat as check data try req as don't want to double-send req for misaligned
            if (ldu_mq_data_try_req_valid_by_entry[i] & ~entry_array[i].data_try_req & ~entry_array[i].data_try_just_sent) begin
                next_entry_array[i].data_try_req = 1'b1;
            end

            // aq blocking (indep)
                // condition to clear:
                    // dtlb hit
                    // currently aq blocking
                    // not mem OR no mem aq active OR older than mem aq
                    // not io OR no io aq active OR older than io aq
            if (
                entry_array[i].dtlb_hit
                & entry_array[i].aq_blocking
                & (
                    ~entry_array[i].is_mem
                    | ~stamofu_aq_mem_aq_active
                    | (rel_ROB_index_by_entry[i] < (stamofu_aq_mem_aq_oldest_abs_ROB_index - rob_kill_abs_head_index)))
                & (
                    entry_array[i].is_mem
                    | ~stamofu_aq_io_aq_active
                    | (rel_ROB_index_by_entry[i] < (stamofu_aq_io_aq_oldest_abs_ROB_index - rob_kill_abs_head_index)))
            ) begin
                next_entry_array[i].aq_blocking = 1'b0;

                // second try req
                next_entry_array[i].second_try_req = 1'b1;
            end

            // older stamofu active (indep)
                // before dtlb hit, try to set if older active
                // after dtlb hit, try to clear if no older active
                // condition to clear:
                    // dtlb hit -> do this so less likely to accidentally clear it due to late aq arriving at stamofu_aq 
                    // no stamofu active OR older than oldest stamofu
            if (
                ~entry_array[i].dtlb_hit
                & ~(
                    ~stamofu_active
                    | (rel_ROB_index_by_entry[i] < (stamofu_oldest_ROB_index - rob_kill_abs_head_index)))
            ) begin
                next_entry_array[i].older_stamofu_active = 1'b1;
            end
            if (
                entry_array[i].dtlb_hit
                & entry_array[i].older_stamofu_active
                & (
                    ~stamofu_active
                    | (rel_ROB_index_by_entry[i] < (stamofu_oldest_ROB_index - rob_kill_abs_head_index)))
            ) begin
                next_entry_array[i].older_stamofu_active = 1'b0;

                // trigger check data try req
                next_entry_array[i].unblock_data_try_req = 1'b1;
            end

            // past nasty forward (indep)
                // no stamofu active
                // nasty forward index older than oldest stamofu
            if (
                entry_array[i].nasty_forward
                & (
                    ~stamofu_active
                    | (entry_array[i].forward_ROB_index - rob_kill_abs_head_index) 
                        < (stamofu_oldest_ROB_index - rob_kill_abs_head_index))
            ) begin
                next_entry_array[i].nasty_forward = 1'b0;
                next_entry_array[i].previous_nasty_forward = 1'b1;

                // second try req
                next_entry_array[i].second_try_req = 1'b1;
            end

            // stalling count subtract (indep)
                // clear when get to 0
            if (stalling_count_subtract_by_entry[i]) begin
                next_entry_array[i].stalling_count = entry_array[i].stalling_count - 1;
                
                if (entry_array[i].stalling_count == 1) begin
                    next_entry_array[i].stalling = 1'b0;

                    // trigger check data try req
                    next_entry_array[i].unblock_data_try_req = 1'b1;
                end
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
            if (second_try_req_ack_one_hot_by_entry[i] & ~second_try_req_not_accepted) begin
                next_entry_array[i].second_try_req = 1'b0;
            end
            if (data_try_req_ack_one_hot_by_entry[i] & ~data_try_req_not_accepted) begin
                next_entry_array[i].data_try_req = 1'b0;
                next_entry_array[i].data_try_just_sent = 1'b1;
            end
            if (complete_req_ack_one_hot_by_entry[i]) begin
                next_entry_array[i].complete_req = 1'b0;
                next_entry_array[i].complete = 1'b1;
            end
            // wait to set WB sent on data try's until after mispred determined for this one
            if (entry_array[i].data_try_just_sent & ~data_try_req_not_accepted) begin
                next_entry_array[i].WB_sent |= data_try_valid;
                next_entry_array[i].data_try_just_sent = data_try_req_ack_one_hot_by_entry[i];
            end
        end
    end

    // ldu CAM
    always_comb begin

        TODO

        ldu_CAM_launch_forward_by_entry = '0;
        ldu_CAM_launch_nasty_forward_by_entry = '0;
        stalling_count_subtract_by_entry = '0;
    end

    // central queue info grab
    always_comb begin
        ldu_cq_info_grab_bank0_op = entry_array[ldu_cq_info_grab_bank0_cq_index].op;
        ldu_cq_info_grab_bank0_mdp_info = entry_array[ldu_cq_info_grab_bank0_cq_index].mdp_info;
        ldu_cq_info_grab_bank0_dest_PR = entry_array[ldu_cq_info_grab_bank0_cq_index].dest_PR;
        ldu_cq_info_grab_bank0_ROB_index = entry_array[ldu_cq_info_grab_bank0_cq_index].ROB_index;
        
        ldu_cq_info_grab_bank1_op = entry_array[ldu_cq_info_grab_bank1_cq_index].op;
        ldu_cq_info_grab_bank1_mdp_info = entry_array[ldu_cq_info_grab_bank1_cq_index].mdp_info;
        ldu_cq_info_grab_bank1_dest_PR = entry_array[ldu_cq_info_grab_bank1_cq_index].dest_PR;
        ldu_cq_info_grab_bank1_ROB_index = entry_array[ldu_cq_info_grab_bank1_cq_index].ROB_index;
    end

    // enq
    assign enq_perform = ~entry_array[enq_ptr].valid & ldu_cq_enq_valid;

    // deq
    assign deq_perform = entry_array[deq_ptr].valid & entry_array[deq_ptr].committed;

    // perform store set commit update on deq
        // update already occurred if there was a forward
        // essentially, only do decrement update
    always_comb begin
        ssu_commit_update_valid = 
            deq_perform 
            & ~(
                entry_array[deq_ptr].forward
                | entry_array[deq_ptr].previous_nasty_forward);
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
            if (~wraparound_mask[LDU_CQ_ENTRIES-2]) begin
                wraparound_mask <= '1;
            end

            // otherwise, shift 0 in leftward
                // n'b111100 -> n'b111000
            else begin
                wraparound_mask <= {wraparound_mask[LDU_CQ_ENTRIES-2], 1'b0};
            end
        end
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
                // entry_array[enq_ptr].misaligned
                // entry_array[enq_ptr].mq_index
                entry_array[enq_ptr].killed <= ldu_cq_enq_killed;
                entry_array[enq_ptr].dtlb_hit <= 1'b0;
                entry_array[enq_ptr].stamofu_CAM_returned <= 1'b0;
                entry_array[enq_ptr].dcache_hit <= 1'b0;
                entry_array[enq_ptr].aq_blocking <= 1'b0;
                entry_array[enq_ptr].older_stamofu_active <= 1'b0;
                entry_array[enq_ptr].stalling <= 1'b0;
                // entry_array[enq_ptr].stalling_count
                entry_array[enq_ptr].forward <= 1'b0;
                entry_array[enq_ptr].nasty_forward <= 1'b0;
                entry_array[enq_ptr].previous_nasty_forward <= 1'b0;
                // entry_array[enq_ptr].forward_ROB_index
                entry_array[enq_ptr].mdp_present <= |ldu_cq_enq_mdp_info[7:6];
                entry_array[enq_ptr].WB_sent <= 1'b0;
                entry_array[enq_ptr].complete <= 1'b0;
                entry_array[enq_ptr].committed <= 1'b0;
                entry_array[enq_ptr].second_try_req <= 1'b0;
                entry_array[enq_ptr].unblock_data_try_req <= 1'b0;
                entry_array[enq_ptr].new_data_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_just_sent <= 1'b0;
                entry_array[enq_ptr].complete_req <= 1'b0;
                entry_array[enq_ptr].page_fault <= 1'b0;
                entry_array[enq_ptr].access_fault <= 1'b0;
                entry_array[enq_ptr].is_mem <= 1'b0;
                entry_array[enq_ptr].op <= ldu_cq_enq_op;
                entry_array[enq_ptr].mdp_info <= ldu_cq_enq_mdp_info;
                entry_array[enq_ptr].dest_PR <= ldu_cq_enq_dest_PR;
                entry_array[enq_ptr].ROB_index <= ldu_cq_enq_ROB_index;
                case (ldu_cq_enq_ROB_index[1:0])
                    2'h0:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0001;
                    2'h1:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0010;
                    2'h2:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0100;
                    2'h3:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b1000;
                endcase
                // entry_array[enq_ptr].PA_word
                // entry_array[enq_ptr].byte_mask
                // entry_array[enq_ptr].bank
                // entry_array[enq_ptr].data

                enq_ptr <= enq_ptr_plus_1;
            end

            //////////
            // deq: //
            //////////
            if (deq_perform) begin
                entry_array[enq_ptr].valid <= 1'b0;
                // entry_array[enq_ptr].misaligned
                // entry_array[enq_ptr].mq_index
                entry_array[enq_ptr].killed <= 1'b0;
                entry_array[enq_ptr].dtlb_hit <= 1'b0;
                entry_array[enq_ptr].stamofu_CAM_returned <= 1'b0;
                entry_array[enq_ptr].dcache_hit <= 1'b0;
                entry_array[enq_ptr].aq_blocking <= 1'b0;
                entry_array[enq_ptr].older_stamofu_active <= 1'b0;
                entry_array[enq_ptr].stalling <= 1'b0;
                // entry_array[enq_ptr].stalling_count
                entry_array[enq_ptr].forward <= 1'b0;
                entry_array[enq_ptr].nasty_forward <= 1'b0;
                entry_array[enq_ptr].previous_nasty_forward <= 1'b0;
                // entry_array[enq_ptr].forward_ROB_index
                entry_array[enq_ptr].mdp_present <= 1'b0;
                entry_array[enq_ptr].WB_sent <= 1'b0;
                entry_array[enq_ptr].complete <= 1'b0;
                entry_array[enq_ptr].committed <= 1'b0;
                entry_array[enq_ptr].second_try_req <= 1'b0;
                entry_array[enq_ptr].unblock_data_try_req <= 1'b0;
                entry_array[enq_ptr].new_data_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_just_sent <= 1'b0;
                entry_array[enq_ptr].complete_req <= 1'b0;
                // entry_array[enq_ptr].page_fault
                // entry_array[enq_ptr].access_fault
                // entry_array[enq_ptr].is_mem
                // entry_array[enq_ptr].op
                // entry_array[enq_ptr].mdp_info
                // entry_array[enq_ptr].dest_PR
                // entry_array[enq_ptr].ROB_index
                // entry_array[enq_ptr].lower_ROB_index_one_hot
                // entry_array[enq_ptr].PA_word
                // entry_array[enq_ptr].byte_mask
                // entry_array[enq_ptr].bank
                // entry_array[enq_ptr].data

                deq_ptr <= deq_ptr_plus_1;
            end
        end
    end

endmodule