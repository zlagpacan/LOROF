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
    parameter LDU_MQ_ENTRIES = 4,
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
    input logic                             ldu_mq_info_ret_bank0_WB_sent, // unused
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
    input logic                             ldu_mq_info_ret_bank1_WB_sent, // unused
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
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_return_bank0_cq_index, // ldu_cq index, unused
    input logic                                 stamofu_CAM_return_bank0_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_return_bank0_mq_index, // ldu_mq index
    input logic                                 stamofu_CAM_return_bank0_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_CAM_return_bank0_stall_count,
    input logic [3:0]                           stamofu_CAM_return_bank0_forward,
    input logic                                 stamofu_CAM_return_bank0_nasty_forward,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_CAM_return_bank0_forward_ROB_index,
    input logic [31:0]                          stamofu_CAM_return_bank0_forward_data,
    
    input logic                                 stamofu_CAM_return_bank1_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]        stamofu_CAM_return_bank1_cq_index, // ldu_cq index, unused
    input logic                                 stamofu_CAM_return_bank1_is_mq,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]        stamofu_CAM_return_bank1_mq_index, // ldu_mq index
    input logic                                 stamofu_CAM_return_bank1_stall,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_CAM_return_bank1_stall_count,
    input logic [3:0]                           stamofu_CAM_return_bank1_forward,
    input logic                                 stamofu_CAM_return_bank1_nasty_forward,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_CAM_return_bank1_forward_ROB_index,
    input logic [31:0]                          stamofu_CAM_return_bank1_forward_data,

    // ldu CAM launch
    input logic                                 ldu_CAM_launch_valid,
    input logic                                 ldu_CAM_launch_is_amo,
    input logic [PA_WIDTH-2-1:0]                ldu_CAM_launch_PA_word,
    input logic [3:0]                           ldu_CAM_launch_byte_mask,
    input logic [31:0]                          ldu_CAM_launch_write_data,
    input logic [MDPT_INFO_WIDTH-1:0]           ldu_CAM_launch_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]           ldu_CAM_launch_ROB_index,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    ldu_CAM_launch_cq_index, // stamofu_cq index, unused
    input logic                                 ldu_CAM_launch_is_mq, // unused
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    ldu_CAM_launch_mq_index, // stamofu_mq index, unused

    // ldu CAM return
    output logic                                ldu_CAM_return_forward, // other info comes from ldu_cq

    // ldu_mq commit
    input logic                             ldu_cq_commit_mq_valid,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_cq_commit_mq_index,
    output logic                            ldu_cq_commit_mq_has_forward,

    // store set CAM update
        // implied dep
    output logic                        ssu_CAM_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_ld_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_ld_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]  ssu_CAM_update_stamo_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ssu_CAM_update_stamo_ROB_index,

    // acquire advertisement
    input logic                         stamofu_aq_mem_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_mem_aq_oldest_abs_ROB_index,
    input logic                         stamofu_aq_io_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_io_aq_oldest_abs_ROB_index,

    // oldest stamofu advertisement
    input logic                         stamofu_incomplete_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_oldest_incomplete_ROB_index,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

    // known theoretical bugs:

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
        logic                               older_stamofu_incomplete_active;
        logic                               stalling;
        logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stalling_count;
        logic                               forward;
        logic                               nasty_forward;
        logic                               previous_nasty_forward;
        logic [LOG_ROB_ENTRIES-1:0]         forward_ROB_index;
        logic                               committed;
        logic                               second_try_req;
        logic                               unblock_data_try_req;
        logic                               new_data_try_req;
        logic                               data_try_req;
        logic                               data_try_waiting;
        logic                               data_try_sent;
        logic                               page_fault;
        logic                               access_fault;
        logic                               is_mem;
        logic [MDPT_INFO_WIDTH-1:0]         mdp_info;
        logic [LOG_ROB_ENTRIES-1:0]         ROB_index;
        logic [PA_WIDTH-3:0]                PA_word;
        logic [3:0]                         byte_mask;
        logic [23:0]                        data;
        logic [LOG_LDU_CQ_ENTRIES-1:0]      cq_index;
    } entry_t;

    entry_t [LDU_MQ_ENTRIES-1:0] entry_array, next_entry_array;

    logic [LOG_LDU_MQ_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_LDU_MQ_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    logic enq_perform;
    logic deq_perform;
    
    logic [LDU_MQ_ENTRIES-1:0] ldu_mq_info_ret_bank0_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] ldu_mq_info_ret_bank1_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] ldu_mq_info_grab_data_try_ack_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] dtlb_miss_resp_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] dcache_miss_resp_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] stamofu_CAM_return_bank0_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] stamofu_CAM_return_bank1_valid_by_entry;
    logic [LDU_MQ_ENTRIES-1:0] commit_valid_by_entry;
    
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
        ldu_mq_info_grab_data_try_ack_by_entry = '0;
        dtlb_miss_resp_valid_by_entry = '0;
        dcache_miss_resp_valid_by_entry = '0;
        stamofu_CAM_return_bank0_valid_by_entry = '0;
        stamofu_CAM_return_bank1_valid_by_entry = '0;
        commit_valid_by_entry = '0;
        
        ldu_mq_info_ret_bank0_valid_by_entry[ldu_mq_info_ret_bank0_mq_index] = ldu_mq_info_ret_bank0_valid;
        ldu_mq_info_ret_bank1_valid_by_entry[ldu_mq_info_ret_bank1_mq_index] = ldu_mq_info_ret_bank1_valid;
        ldu_mq_info_grab_data_try_ack_by_entry[ldu_mq_info_grab_mq_index] = ldu_mq_info_grab_data_try_ack;
        dtlb_miss_resp_valid_by_entry[dtlb_miss_resp_mq_index] = dtlb_miss_resp_valid & dtlb_miss_resp_is_mq;
        dcache_miss_resp_valid_by_entry[dcache_miss_resp_mq_index] = dcache_miss_resp_valid & dcache_miss_resp_is_mq;
        stamofu_CAM_return_bank0_valid_by_entry[stamofu_CAM_return_bank0_mq_index] = stamofu_CAM_return_bank0_valid & stamofu_CAM_return_bank0_is_mq;
        stamofu_CAM_return_bank1_valid_by_entry[stamofu_CAM_return_bank1_mq_index] = stamofu_CAM_return_bank1_valid & stamofu_CAM_return_bank1_is_mq;
        commit_valid_by_entry[ldu_cq_commit_mq_index] = ldu_cq_commit_mq_valid;
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
            second_try_valid <= |second_try_req_by_entry;
            second_try_mq_index <= second_try_req_ack_index_by_entry;
        end
    end
    always_comb begin
        second_try_bank0_valid = second_try_valid & (entry_array[second_try_mq_index].PA_word[DCACHE_WORD_ADDR_BANK_BIT] == 1'b0);
        second_try_bank1_valid = second_try_valid & (entry_array[second_try_mq_index].PA_word[DCACHE_WORD_ADDR_BANK_BIT] == 1'b1);

        second_try_do_mispred = 1'b0; 
            // mispred will be handled on eventual data_try_do_mispred anyway since 
                // data try guaranteed for misaligned
            // don't care to do mispred here since
                // cq entry may not have sent in first place so may not be mispred 
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
            // ldu mq info grab data try ack
            // aq age
            // oldest stamofu age
            // nasty forward stamofu age
            // ROB commit
            // ROB kill
    always_comb begin
        next_entry_array = entry_array;

        for (int i = 0; i < LDU_MQ_ENTRIES; i++) begin
            rel_ROB_index_by_entry[i] = entry_array[i].ROB_index - rob_kill_abs_head_index;

            next_entry_array[i].unblock_data_try_req = 1'b0;
            next_entry_array[i].new_data_try_req = 1'b0;

            // events with priority
                // ldu_mq bank 0
                // ldu_mq bank 1
                // stamofu CAM return bank 0
                // stamofu CAM return bank 1
                // ldu CAM
                // dcache miss resp

            // ldu_mq bank 0
            if (ldu_mq_info_ret_bank0_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = ldu_mq_info_ret_bank0_dtlb_hit;
                // next_entry_array[i].stamofu_CAM_returned = 
                next_entry_array[i].dcache_hit = ldu_mq_info_ret_bank0_dcache_hit;
                next_entry_array[i].aq_blocking = ldu_mq_info_ret_bank0_aq_blocking;
                // next_entry_array[i].older_stamofu_incomplete_active = 
                // next_entry_array[i].stalling = 
                // next_entry_array[i].stalling_count = 
                // next_entry_array[i].forward = 
                // next_entry_array[i].nasty_forward = 
                // next_entry_array[i].previous_nasty_forward = 
                // next_entry_array[i].forward_ROB_index = 
                // next_entry_array[i].committed = 
                // next_entry_array[i].second_try_req = 
                // next_entry_array[i].unblock_data_try_req = 
                // next_entry_array[i].data_try_req = 
                // next_entry_array[i].data_try_waiting = 
                // next_entry_array[i].data_try_sent = 
                next_entry_array[i].page_fault = ldu_mq_info_ret_bank0_page_fault;
                next_entry_array[i].access_fault = ldu_mq_info_ret_bank0_access_fault;
                next_entry_array[i].is_mem = ldu_mq_info_ret_bank0_is_mem;
                // next_entry_array[i].mdp_info = 
                next_entry_array[i].ROB_index = ldu_mq_info_ret_bank0_ROB_index;
                next_entry_array[i].PA_word = ldu_mq_info_ret_bank0_PA_word;
                next_entry_array[i].byte_mask = ldu_mq_info_ret_bank0_byte_mask;
                next_entry_array[i].data = ldu_mq_info_ret_bank0_data;
                next_entry_array[i].cq_index = ldu_mq_info_ret_bank0_cq_index;

                next_entry_array[i].unblock_data_try_req = 1'b1;
            end
            // ldu_mq bank 1
            if (ldu_mq_info_ret_bank1_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = ldu_mq_info_ret_bank1_dtlb_hit;
                // next_entry_array[i].stamofu_CAM_returned = 
                next_entry_array[i].dcache_hit = ldu_mq_info_ret_bank1_dcache_hit;
                next_entry_array[i].aq_blocking = ldu_mq_info_ret_bank1_aq_blocking;
                // next_entry_array[i].older_stamofu_incomplete_active = 
                // next_entry_array[i].stalling = 
                // next_entry_array[i].stalling_count = 
                // next_entry_array[i].forward = 
                // next_entry_array[i].nasty_forward = 
                // next_entry_array[i].previous_nasty_forward = 
                // next_entry_array[i].forward_ROB_index = 
                // next_entry_array[i].committed = 
                // next_entry_array[i].second_try_req = 
                // next_entry_array[i].unblock_data_try_req = 
                // next_entry_array[i].data_try_req = 
                // next_entry_array[i].data_try_waiting = 
                // next_entry_array[i].data_try_sent = 
                next_entry_array[i].page_fault = ldu_mq_info_ret_bank1_page_fault;
                next_entry_array[i].access_fault = ldu_mq_info_ret_bank1_access_fault;
                next_entry_array[i].is_mem = ldu_mq_info_ret_bank1_is_mem;
                // next_entry_array[i].mdp_info = 
                next_entry_array[i].ROB_index = ldu_mq_info_ret_bank1_ROB_index;
                next_entry_array[i].PA_word = ldu_mq_info_ret_bank1_PA_word;
                next_entry_array[i].byte_mask = ldu_mq_info_ret_bank1_byte_mask;
                next_entry_array[i].data = ldu_mq_info_ret_bank1_data;
                next_entry_array[i].cq_index = ldu_mq_info_ret_bank1_cq_index;
                
                next_entry_array[i].unblock_data_try_req = 1'b1;
            end
            // stamofu CAM return bank 0
            else if (stamofu_CAM_return_bank0_valid_by_entry[i]) begin
                next_entry_array[i].stamofu_CAM_returned = 1'b1;
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
                next_entry_array[i].new_data_try_req |= stamofu_CAM_return_bank1_forward | dcache_miss_resp_valid_by_entry[i];
            end
            // ldu CAM forward
                // subset of stamofu CAM return if comes first
            else if (ldu_CAM_launch_forward_by_entry[i]) begin
                next_entry_array[i].forward = 1'b1;
                next_entry_array[i].nasty_forward = 1'b0;
                next_entry_array[i].forward_ROB_index = ldu_CAM_launch_ROB_index;

                next_entry_array[i].data = ldu_CAM_launch_write_data;

                // trigger new data try req
                next_entry_array[i].new_data_try_req = 1'b1;
            end
            // ldu CAM nasty forward
                // subset of stamofu CAM return if comes first
            else if (ldu_CAM_launch_nasty_forward_by_entry[i]) begin
                next_entry_array[i].forward = 1'b0;
                next_entry_array[i].nasty_forward = 1'b1;
                next_entry_array[i].forward_ROB_index = ldu_CAM_launch_ROB_index;
            end
            // dcache miss resp
                // this is only case where take dcache miss resp data
            else if (dcache_miss_resp_valid_by_entry[i] & ~entry_array[i].forward & ~entry_array[i].nasty_forward) begin
                next_entry_array[i].data = dcache_miss_resp_data;

                // trigger new data try req
                next_entry_array[i].new_data_try_req = 1'b1;
            end

            // indep behavior:

            // dcache miss return (indep)
                // only setting of dcache hit is indep
            if (dcache_miss_resp_valid_by_entry[i]) begin
                next_entry_array[i].dcache_hit = 1'b1;
            end

            // ready for data try req
                // check not sending data AND haven't already sent data
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
                        & ~entry_array[i].data_try_req 
                        & ~entry_array[i].data_try_waiting 
                        & ~entry_array[i].data_try_sent
                    )
                    | entry_array[i].new_data_try_req
                )
                & entry_array[i].dtlb_hit
                & ~entry_array[i].aq_blocking
                & (entry_array[i].forward | entry_array[i].dcache_hit)
                & ~entry_array[i].nasty_forward
                & (!entry_array[i].mdp_info[7:6] | entry_array[i].stamofu_CAM_returned)
                & (~entry_array[i].stalling | ~stamofu_incomplete_active | ~entry_array[i].older_stamofu_incomplete_active)
            ) begin
                next_entry_array[i].data_try_req = 1'b1;
            end

            // dtlb miss return (indep)
            if (dtlb_miss_resp_valid_by_entry[i]) begin
                next_entry_array[i].dtlb_hit = 1'b1;
                next_entry_array[i].PA_word[PA_WIDTH-3:PA_WIDTH-2-PPN_WIDTH] = dtlb_miss_resp_PPN;
                next_entry_array[i].is_mem = dtlb_miss_resp_is_mem;
                next_entry_array[i].page_fault = dtlb_miss_resp_page_fault;
                next_entry_array[i].access_fault = dtlb_miss_resp_access_fault;

                // second try req
                next_entry_array[i].second_try_req = 1'b1;
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
                    ~stamofu_incomplete_active
                    | (rel_ROB_index_by_entry[i] < (stamofu_oldest_incomplete_ROB_index - rob_kill_abs_head_index)))
            ) begin
                next_entry_array[i].older_stamofu_incomplete_active = 1'b1;
            end
            if (
                entry_array[i].dtlb_hit
                & entry_array[i].older_stamofu_incomplete_active
                & (
                    ~stamofu_incomplete_active
                    | (rel_ROB_index_by_entry[i] < (stamofu_oldest_incomplete_ROB_index - rob_kill_abs_head_index)))
            ) begin
                next_entry_array[i].older_stamofu_incomplete_active = 1'b0;

                // trigger check data try req
                next_entry_array[i].unblock_data_try_req = 1'b1;
            end

            // past nasty forward (indep)
                // no stamofu active
                // nasty forward index older than oldest stamofu
            if (
                entry_array[i].nasty_forward 
                & entry_array[i].dcache_hit
                    // old dcache hit must be resolved before starting the next
                    // this also prevents data try returns while nasty forward resolving
                    // naturally, perf hit since can't layer both dcache accesses
                        // uncommon case and nasty if try to
                            // hard to make guarantees
                & (
                    ~stamofu_incomplete_active
                    | (entry_array[i].forward_ROB_index - rob_kill_abs_head_index) 
                        < (stamofu_oldest_incomplete_ROB_index - rob_kill_abs_head_index))
            ) begin
                next_entry_array[i].dcache_hit = 1'b0;
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

            // mq commit (indep)
            if (commit_valid_by_entry[i]) begin
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
            if (data_try_req_ack_one_hot_by_entry[i]) begin
                next_entry_array[i].data_try_req = 1'b0;
                next_entry_array[i].data_try_waiting = 1'b1;
            end
            if (ldu_mq_info_grab_data_try_ack_by_entry[i]) begin
                next_entry_array[i].data_try_waiting = 1'b0;
                next_entry_array[i].data_try_sent = 1'b1;
            end
        end
    end

    // ldu CAM
    always_comb begin
        ldu_CAM_launch_forward_by_entry = '0;
        ldu_CAM_launch_nasty_forward_by_entry = '0;
        stalling_count_subtract_by_entry = '0;

        for (int i = 0; i < LDU_MQ_ENTRIES; i++) begin

            // forward if youngest older AND superset AND not amo
            if (
                ldu_CAM_launch_valid
                & entry_array[i].dtlb_hit
                & entry_array[i].stamofu_CAM_returned
                    // might as well get full stamofu CAM info. only forward here if after already got CAM info
                & ldu_CAM_launch_PA_word == entry_array[i].PA_word
                & ~ldu_CAM_launch_is_amo
                // superset
                    // entry byte -> CAM byte
                & &{~entry_array[i].byte_mask | ldu_CAM_launch_byte_mask}
                // older than this
                & (ldu_CAM_launch_ROB_index - rob_kill_abs_head_index 
                    < rel_ROB_index_by_entry[i])
                // no curr OR younger than curr
                & (
                    (~entry_array[i].forward & ~entry_array[i].nasty_forward)
                    | (ldu_CAM_launch_ROB_index - rob_kill_abs_head_index
                        > entry_array[i].forward_ROB_index - rob_kill_abs_head_index)
                )
            ) begin
                ldu_CAM_launch_forward_by_entry[i] = 1'b1;
            end

            // nasty forward if youngest older AND (not superset OR amo)
            if (
                ldu_CAM_launch_valid
                & entry_array[i].dtlb_hit
                & entry_array[i].stamofu_CAM_returned
                    // might as well get full stamofu CAM info. only forward here if after already got CAM info
                & ldu_CAM_launch_PA_word == entry_array[i].PA_word
                & (
                    ldu_CAM_launch_is_amo
                    | ~&{~entry_array[i].byte_mask | ldu_CAM_launch_byte_mask}
                        // strict subset
                            // any valid entry byte has invalid CAM byte
                )
                // older than this
                & (ldu_CAM_launch_ROB_index - rob_kill_abs_head_index 
                    < rel_ROB_index_by_entry[i])
                // no curr OR younger than curr
                & (
                    (~entry_array[i].forward & ~entry_array[i].nasty_forward)
                    | (ldu_CAM_launch_ROB_index - rob_kill_abs_head_index
                        > entry_array[i].forward_ROB_index - rob_kill_abs_head_index)
                )
            ) begin
                ldu_CAM_launch_nasty_forward_by_entry[i] = 1'b1;
            end

            // stall count subtract if older AND mdp info match AND mdp present for CAM AND mdp present for entry
            if (
                ldu_CAM_launch_valid
                & entry_array[i].dtlb_hit
                & entry_array[i].stamofu_CAM_returned
                    // ignore any ldu CAMs which would be double counted by incoming stamofu CAM
                & |ldu_CAM_launch_mdp_info[7:6]
                & |entry_array[i].mdp_info[7:6]
                & ldu_CAM_launch_mdp_info[5:0] == entry_array[i].mdp_info[5:0]
                // older than this
                & (ldu_CAM_launch_ROB_index - rob_kill_abs_head_index 
                    < rel_ROB_index_by_entry[i])
            ) begin
                stalling_count_subtract_by_entry[i] = 1'b1;
            end
        end
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            ldu_CAM_return_forward <= 1'b0;
        end
        else begin
            ldu_CAM_return_forward <= |ldu_CAM_launch_forward_by_entry | |ldu_CAM_launch_nasty_forward_by_entry;
        end
    end

    // misaligned queue info grab
    always_comb begin
        ldu_mq_info_grab_data_try_req = 
            entry_array[ldu_mq_info_grab_mq_index].data_try_req 
            | entry_array[ldu_mq_info_grab_mq_index].data_try_waiting;
        ldu_mq_info_grab_data = {8'h00, entry_array[ldu_mq_info_grab_mq_index].data};
    end

    // store set CAM update
        // can only perform for single CAM forward -> simply choose lowest
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            ssu_CAM_update_valid_by_entry <= '0;

            ssu_CAM_update_stamo_mdp_info <= '0;
            ssu_CAM_update_stamo_ROB_index <= '0;
        end
        else begin
            ssu_CAM_update_valid_by_entry <= ldu_CAM_launch_forward_by_entry | ldu_CAM_launch_nasty_forward_by_entry;
            
            ssu_CAM_update_stamo_mdp_info <= ldu_CAM_launch_mdp_info;
            ssu_CAM_update_stamo_ROB_index <= ldu_CAM_launch_ROB_index;
        end
    end
    pe_lsb # (
        .WIDTH(LDU_MQ_ENTRIES), .USE_ONE_HOT(0), .USE_INDEX(1)
    ) SSU_CAM_PE (
        .req_vec(ssu_CAM_update_valid_by_entry),
        .ack_index(ssu_CAM_update_index)
    );
    always_comb begin

        // may need to latch these:

        ssu_CAM_update_valid = |ssu_CAM_update_valid_by_entry;

        ssu_CAM_update_ld_mdp_info = entry_array[ssu_CAM_update_index].mdp_info;
        ssu_CAM_update_ld_ROB_index = entry_array[ssu_CAM_update_index].ROB_index;
    end

    // enq
    assign enq_perform = ~entry_array[enq_ptr].valid & ldu_mq_enq_valid;

    // enq feedback
    always_comb begin
        ldu_mq_enq_ready = ~entry_array[enq_ptr].valid;
        ldu_mq_enq_index = enq_ptr;
    end

    // deq
    assign deq_perform = entry_array[deq_ptr].valid & entry_array[deq_ptr].committed;

    // ldu commit
    assign ldu_cq_commit_mq_has_forward = 
        entry_array[ldu_cq_commit_mq_index].forward
        | entry_array[ldu_cq_commit_mq_index].previous_nasty_forward;

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
                entry_array[enq_ptr].killed <= 1'b0;
                entry_array[enq_ptr].dtlb_hit <= 1'b0;
                entry_array[enq_ptr].stamofu_CAM_returned <= 1'b0;
                entry_array[enq_ptr].dcache_hit <= 1'b0;
                entry_array[enq_ptr].aq_blocking <= 1'b0;
                entry_array[enq_ptr].older_stamofu_incomplete_active <= 1'b0;
                entry_array[enq_ptr].stalling <= 1'b0;
                // entry_array[enq_ptr].stalling_count <= 
                entry_array[enq_ptr].forward <= 1'b0;
                entry_array[enq_ptr].nasty_forward <= 1'b0;
                entry_array[enq_ptr].previous_nasty_forward <= 1'b0;
                // entry_array[enq_ptr].forward_ROB_index <= 
                entry_array[enq_ptr].committed <= 1'b0;
                entry_array[enq_ptr].second_try_req <= 1'b0;
                entry_array[enq_ptr].unblock_data_try_req <= 1'b0;
                entry_array[enq_ptr].new_data_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_waiting <= 1'b0;
                entry_array[enq_ptr].data_try_sent <= 1'b0;
                entry_array[enq_ptr].page_fault <= 1'b0;
                entry_array[enq_ptr].access_fault <= 1'b0;
                entry_array[enq_ptr].is_mem <= 1'b0;
                // entry_array[enq_ptr].mdp_info <= 
                // entry_array[enq_ptr].ROB_index <= 
                // entry_array[enq_ptr].PA_word <= 
                // entry_array[enq_ptr].byte_mask <= 
                // entry_array[enq_ptr].data <= 
                // entry_array[enq_ptr].cq_index <= 

                enq_ptr <= enq_ptr_plus_1;
            end

            //////////
            // deq: //
            //////////
            if (deq_perform) begin
                entry_array[deq_ptr].valid <= 1'b0;
                entry_array[deq_ptr].killed <= 1'b0;
                entry_array[deq_ptr].dtlb_hit <= 1'b0;
                entry_array[deq_ptr].stamofu_CAM_returned <= 1'b0;
                entry_array[deq_ptr].dcache_hit <= 1'b0;
                entry_array[deq_ptr].aq_blocking <= 1'b0;
                entry_array[deq_ptr].older_stamofu_incomplete_active <= 1'b0;
                entry_array[deq_ptr].stalling <= 1'b0;
                // entry_array[deq_ptr].stalling_count <= 
                entry_array[deq_ptr].forward <= 1'b0;
                entry_array[deq_ptr].nasty_forward <= 1'b0;
                entry_array[deq_ptr].previous_nasty_forward <= 1'b0;
                // entry_array[deq_ptr].forward_ROB_index <= 
                entry_array[deq_ptr].committed <= 1'b0;
                entry_array[deq_ptr].second_try_req <= 1'b0;
                entry_array[deq_ptr].unblock_data_try_req <= 1'b0;
                entry_array[deq_ptr].new_data_try_req <= 1'b0;
                entry_array[deq_ptr].data_try_req <= 1'b0;
                entry_array[deq_ptr].data_try_waiting <= 1'b0;
                entry_array[deq_ptr].data_try_sent <= 1'b0;
                entry_array[deq_ptr].page_fault <= 1'b0;
                entry_array[deq_ptr].access_fault <= 1'b0;
                entry_array[deq_ptr].is_mem <= 1'b0;
                // entry_array[deq_ptr].mdp_info <= 
                // entry_array[deq_ptr].ROB_index <= 
                // entry_array[deq_ptr].PA_word <= 
                // entry_array[deq_ptr].byte_mask <= 
                // entry_array[deq_ptr].data <= 
                // entry_array[deq_ptr].cq_index <= 

                deq_ptr <= deq_ptr_plus_1;
            end
        end
    end

endmodule