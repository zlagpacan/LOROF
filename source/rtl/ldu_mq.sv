/*
    Filename: ldu_mq.sv
    Author: zlagpacan
    Description: RTL for Load Unit Misaligned Queue
    Spec: LOROF/spec/design/ldu_mq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module ldu_mq #(
    parameter LDU_MQ_ENTRIES = 40,
    parameter LOG_LDU_MQ_ENTRIES = $clog2(LDU_MQ_ENTRIES)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to misaligned queue
    input logic                             ldu_mq_enq_valid,

    // misaligned queue enqueue feedback
    output logic                            ldu_mq_enq_ready,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_enq_index,
    
    // second try
        // prioritize this one from mq over cq's
    output logic                            second_try_bank0_valid,
    output logic                            second_try_bank1_valid,

    output logic                            second_try_do_mispred,
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

    // misaligned queue data try req
    output logic                            ldu_mq_data_try_req_valid,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_mq_data_try_cq_index,

    // misaligned queue info grab
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_mq_info_grab_mq_index,
    input logic                             ldu_mq_info_grab_data_try_ack,
    output logic                            ldu_mq_info_grab_data_try_req,
    output logic [31:0]                     ldu_mq_info_grab_data,

    // misaligned queue info ret
    input logic                             ldu_mq_info_ret_bank0_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_mq_info_ret_bank0_cq_index,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_mq_info_ret_bank0_mq_index,
    input logic [LOG_ROB_ENTRIES-1:0]       ldu_mq_info_ret_bank0_ROB_index,
    input logic                             ldu_mq_info_ret_bank0_WB_sent,
    input logic                             ldu_mq_info_ret_bank0_dtlb_hit,
    input logic                             ldu_mq_info_ret_bank0_page_fault,
    input logic                             ldu_mq_info_ret_bank0_access_fault,
    input logic                             ldu_mq_info_ret_bank0_dcache_hit,
    input logic                             ldu_mq_info_ret_bank0_is_mem,
    input logic                             ldu_mq_info_ret_bank0_aq_blocking,
    input logic [PA_WIDTH-2-1:0]            ldu_mq_info_ret_bank0_PA_word,
    input logic [3:0]                       ldu_mq_info_ret_bank0_byte_mask,
    input logic [31:0]                      ldu_mq_info_ret_bank0_data,
    
    input logic                             ldu_mq_info_ret_bank1_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_mq_info_ret_bank1_cq_index,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_mq_info_ret_bank1_mq_index,
    input logic [LOG_ROB_ENTRIES-1:0]       ldu_mq_info_ret_bank1_ROB_index,
    input logic                             ldu_mq_info_ret_bank1_WB_sent,
    input logic                             ldu_mq_info_ret_bank1_dtlb_hit,
    input logic                             ldu_mq_info_ret_bank1_page_fault,
    input logic                             ldu_mq_info_ret_bank1_access_fault,
    input logic                             ldu_mq_info_ret_bank1_dcache_hit,
    input logic                             ldu_mq_info_ret_bank1_is_mem,
    input logic                             ldu_mq_info_ret_bank1_aq_blocking,
    input logic [PA_WIDTH-2-1:0]            ldu_mq_info_ret_bank1_PA_word,
    input logic [3:0]                       ldu_mq_info_ret_bank1_byte_mask,
    input logic [31:0]                      ldu_mq_info_ret_bank1_data,

    // dtlb miss resp
    input logic                             dtlb_miss_resp_valid,
    input logic                             dtlb_miss_resp_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    dtlb_miss_resp_mq_index,
    input logic [PPN_WIDTH-1:0]             dtlb_miss_resp_PPN,
    input logic                             dtlb_miss_resp_is_mem,
    input logic                             dtlb_miss_resp_page_fault,
    input logic                             dtlb_miss_resp_access_fault,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    dtlb_miss_resp_cq_index, // unused

    // dcache miss resp
    input logic                             dcache_miss_resp_valid,
    input logic                             dcache_miss_resp_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    dcache_miss_resp_mq_index,
    input logic [31:0]                      dcache_miss_resp_data,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    dcache_miss_resp_cq_index, // unused

    // stamofu CAM return
    input logic                                 stamofu_CAM_return_bank0_valid,
    input logic                                 stamofu_CAM_return_bank0_is_mq,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_return_bank0_cq_index, // ldu_cq index
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_return_bank0_mq_index, // ldu_mq index
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_return_bank0_updated_mdp_info,
    input logic                                 stamofu_CAM_return_bank0_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_CAM_return_bank0_stall_count,
    input logic [3:0]                           stamofu_CAM_return_bank0_forward,
    input logic                                 stamofu_CAM_return_bank0_nasty_forward,
    input logic                                 stamofu_CAM_return_bank0_forward_ROB_index,
    input logic [31:0]                          stamofu_CAM_return_bank0_forward_data,
    
    input logic                                 stamofu_CAM_return_bank1_valid,
    input logic                                 stamofu_CAM_return_bank1_is_mq,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_return_bank1_cq_index, // ldu_cq index
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_return_bank1_mq_index, // ldu_mq index
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_CAM_return_bank1_updated_mdp_info,
    input logic                                 stamofu_CAM_return_bank1_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_CAM_return_bank1_stall_count,
    input logic [3:0]                           stamofu_CAM_return_bank1_forward,
    input logic                                 stamofu_CAM_return_bank1_nasty_forward,
    input logic                                 stamofu_CAM_return_bank1_forward_ROB_index,
    input logic [31:0]                          stamofu_CAM_return_bank1_forward_data,

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
    output logic                                ldu_CAM_return_forward, // other info comes from ldu_cq

    // store set CAM update
        // implied dep
        // prioritize this one from mq over cq's
    output logic                        ssu_CAM_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_ld_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_ld_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_stamo_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_stamo_ROB_index,

    // store set commit update
        // implied no dep
        // prioritize this one from mq over cq's
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

    // ROB commit
    input logic [LOG_ROB_ENTRIES-3:0]   rob_commit_upper_index,
    input logic [3:0]                   rob_commit_lower_index_valid_mask,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

    // mq enq race condition: all mq entries younger than old mq entry trying to enq now
        // can keep timer in mq checking for too many cycles where
        // input enq ROB index older than all mq ROB index's

    // ----------------------------------------------------------------
    // Signals:

    typedef struct packed {
        logic                               valid;
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
        logic                               committed;
        logic                               second_try_req;
        logic                               data_ready;
        logic                               data_try_req;
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
        logic [LOG_LDU_CQ_ENTRIES-1:0]      cq_index;
    } entry_t;

    entry_t [LDU_MQ_ENTRIES-1:0] entry_array, next_entry_array;

    logic [LOG_LDU_MQ_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_LDU_MQ_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;
    
    logic [LDU_MQ_ENTRIES-1:0] ldu_mq_info_ret_bank0_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] ldu_mq_info_ret_bank1_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] dtlb_miss_resp_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] dcache_miss_resp_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] stamofu_CAM_return_bank0_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] stamofu_CAM_return_bank1_valid_by_entry;
    
    logic [LDU_MQ_ENTRIES-1:0] second_try_req_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] data_try_req_by_entry;

    logic [LDU_MQ_ENTRIES-1:0] second_try_req_ack_one_hot_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] data_try_req_ack_one_hot_by_entry;

    logic [LDU_MQ_ENTRIES-1:0] second_try_req_ack_index_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] data_try_req_ack_index_by_entry;

    logic second_try_valid;

    logic second_try_req_not_accepted;

    logic [LDU_MQ_ENTRIES-1:0] ldu_mq_data_try_mq_index;

    logic [LDU_MQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0] rel_ROB_index_by_entry;
    
    logic [LDU_MQ_ENTRIES-1:0] ldu_CAM_launch_forward_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] ldu_CAM_launch_nasty_forward_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] stalling_count_subtract_by_entry;

    logic [LDU_MQ_ENTRIES-1:0]      ssu_CAM_update_valid_by_entry;
    logic [LOG_LDU_MQ_ENTRIES-1:0]  ssu_CAM_update_index;

    // ----------------------------------------------------------------
    // Logic:

    assign enq_ptr_plus_1 = (enq_ptr == LDU_MQ_ENTRIES-1) ? 0 : enq_ptr + 1;
    assign deq_ptr_plus_1 = (deq_ptr == LDU_MQ_ENTRIES-1) ? 0 : deq_ptr + 1;

    // event demux to entry
        // ldu_mq return
            // 2x banks
        // dtlb miss resp
        // dcache miss resp
        // stamofu CAM return
            // 2x banks
    always_comb begin
        ldu_mq_info_ret_bank0_valid_by_entry = '0;
        ldu_mq_info_ret_bank1_valid_by_entry = '0;
        dtlb_miss_resp_valid_by_entry = '0;
        dcache_miss_resp_valid_by_entry = '0;
        stamofu_CAM_return_bank0_valid_by_entry = '0;
        stamofu_CAM_return_bank1_valid_by_entry = '0;
        
        ldu_mq_info_ret_bank0_valid_by_entry[ldu_mq_info_ret_bank0_mq_index] = ldu_mq_info_ret_bank0_valid;
        ldu_mq_info_ret_bank1_valid_by_entry[ldu_mq_info_ret_bank1_mq_index] = ldu_mq_info_ret_bank1_valid;
        dtlb_miss_resp_valid_by_entry[dtlb_miss_resp_mq_index] = dtlb_miss_resp_valid & dtlb_miss_resp_is_mq;
        dcache_miss_resp_valid_by_entry[dcache_miss_resp_mq_index] = dcache_miss_resp_valid & dcache_miss_resp_is_mq;
        stamofu_CAM_return_bank0_valid_by_entry[stamofu_CAM_return_bank0_mq_index] = stamofu_CAM_return_bank0_valid & stamofu_CAM_return_bank0_is_mq;
        stamofu_CAM_return_bank1_valid_by_entry[stamofu_CAM_return_bank1_mq_index] = stamofu_CAM_return_bank1_valid & stamofu_CAM_return_bank1_is_mq;
    end

    // request PE's
    always_comb begin
        for (int i = 0; i < LDU_MQ_ENTRIES; i++) begin
            second_try_req_by_entry[i] = entry_array[i].second_try_req;
            data_try_req_by_entry[i] = entry_array[i].data_try_req;
        end
    end
    pe_lsb # (
        .WIDTH(LDU_MQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) SECOND_TRY_PE (
        .req_vec(second_try_req_by_entry),
        .ack_one_hot(second_try_req_ack_one_hot_by_entry),
        .ack_index(second_try_req_ack_index_by_entry)
    );
    pe_lsb # (
        .WIDTH(LDU_MQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) DATA_TRY_PE (
        .req_vec(data_try_req_by_entry),
        .ack_one_hot(data_try_req_ack_one_hot_by_entry),
        .ack_index(data_try_req_ack_index_by_entry)
    );
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            second_try_valid <= 1'b0;
            second_try_mq_index <= 0;
        end
        else begin
            second_try_valid <= |second_try_unmasked_req_by_entry;
            second_try_mq_index <= second_try_req_ack_index_by_entry;
        end
    end
    always_comb begin
        second_try_bank0_valid = second_try_valid & (entry_array[second_try_mq_index].bank == 1'b0);
        second_try_bank1_valid = second_try_valid & (entry_array[second_try_mq_index].bank == 1'b1);

        second_try_do_mispred = entry_array[second_try_mq_index].WB_sent;
        second_try_is_mq = 1'b1;
        second_try_misaligned = 1'b1;
        second_try_page_fault = entry_array[second_try_mq_index].page_fault;
        second_try_access_fault = entry_array[second_try_mq_index].access_fault;
        second_try_is_mem = entry_array[second_try_mq_index].is_mem;
        second_try_PPN = entry_array[second_try_mq_index].PA_word[PA_WIDTH-3:PA_WIDTH-2-PPN_WIDTH];
        second_try_PO_word = entry_array[second_try_mq_index].PA_word[PA_WIDTH-2-PPN_WIDTH-1:0];
        second_try_byte_mask = entry_array[second_try_mq_index].byte_mask;
        second_try_cq_index = entry_array[second_try_mq_index].cq_index;

        second_try_req_not_accepted = 
            second_try_bank0_valid & ~second_try_bank0_ack
            | second_try_bank1_valid & ~second_try_bank1_ack;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            ldu_mq_data_try_req_valid <= 1'b0;
            ldu_mq_data_try_mq_index <= 0;
        end
        else begin
            ldu_mq_data_try_req_valid <= |data_try_req_by_entry;
            ldu_mq_data_try_mq_index <= data_try_req_ack_index_by_entry;
        end
    end
    always_comb begin
        ldu_mq_data_try_cq_index = entry_array[ldu_mq_data_try_mq_index].cq_index;
    end

    // per-entry state machine
        // external events:
            // ldu_mq return
                // 2x banks
            // dtlb miss resp
            // dcache miss resp
            // stamofu CAM return
                // 2x banks
            // ldu CAM
            // second try req ack
            // data try req ack
            // aq age
            // oldest stamofu age
            // nasty forward stamofu age
            // ROB commit
            // ROB kill
    always_comb begin
        next_entry_array = entry_array;

        for (int i = 0; i < LDU_MQ_ENTRIES; i++) begin
            rel_ROB_index_by_entry[i] = entry_array[i].ROB_index - rob_kill_abs_head_index;

            // events with priority
                // ldu_mq bank 0
                // ldu_mq bank 1
                // stamofu CAM return bank 0
                // stamofu CAM return bank 1
                // ldu CAM
                // dcache miss resp

            
        end
    end

endmodule