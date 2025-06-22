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
    input logic                             ldu_cq_info_ret_valid,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    ldu_cq_info_ret_cq_index,
    input logic                             ldu_cq_info_ret_misaligned,
    input logic                             ldu_cq_info_ret_dtlb_hit,
    input logic                             ldu_cq_info_ret_page_fault,
    input logic                             ldu_cq_info_ret_access_fault,
    input logic                             ldu_cq_info_ret_dcache_hit,
    input logic                             ldu_cq_info_ret_is_mem,
    input logic                             ldu_cq_info_ret_aq_blocking,
    input logic [PA_WIDTH-2-1:0]            ldu_cq_info_ret_PA_word,
    input logic [3:0]                       ldu_cq_info_ret_byte_mask,
    input logic [31:0]                      ldu_cq_info_ret_data,

    // misaligned queue info ret
        // need in order to tie cq entry to mq if misaligned
        // use cq_index ^
    input logic                             ldu_mq_info_ret_valid,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_mq_info_ret_mq_index,

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
    input logic                                 stamofu_CAM_return_nasty_forward,
    input logic                                 stamofu_CAM_return_nasty_wait_ROB_index,
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

    // oldest stamofu advertisement
    input logic                         stamofu_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_oldest_ROB_index,

    // acquire advertisement
    input logic                         stamofu_aq_mem_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_mem_aq_oldest_abs_ROB_index,
    input logic                         stamofu_aq_io_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_io_aq_oldest_abs_ROB_index,

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

    // ----------------------------------------------------------------
    // Signals:

    typedef struct packed {
        logic                               valid;
        logic                               misaligned;
        logic [LOG_LDU_MQ_ENTRIES-1:0]      mq_index;
        logic                               killed;
        logic                               launched;
        logic                               dtlb_hit;
        logic                               dcache_hit;
        logic                               aq_blocking;
        logic                               stalling;
        logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  stall_count;
        logic                               forwarded;
        logic [LOG_ROB_ENTRIES-1:0]         forwarded_ROB_index;
        logic                               nasty_forward;
        logic [LOG_ROB_ENTRIES-1:0]         nasty_forward_wait_upper_ROB_index;
        logic [3:0]                         nasty_forward_wait_lower_ROB_index_one_hot;
        logic                               WB_sent;
        logic                               complete;
        logic                               committed;
        logic                               mdp_update_req;
        logic                               second_try_req;
        logic                               data_try_req;
        logic                               complete_req;
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

    entry_t [LDU_CQ_ENTRIES-1:0] entry_array, next_entry_array;

    logic [LOG_LDU_CQ_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_LDU_CQ_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    // ----------------------------------------------------------------
    // Logic:

    assign enq_ptr_plus_1 = (enq_ptr == LDU_CQ_ENTRIES-1) ? 0 : enq_ptr + 1;
    assign deq_ptr_plus_1 = (deq_ptr == LDU_CQ_ENTRIES-1) ? 0 : deq_ptr + 1;

    // per-entry state machine
    always_comb begin
        next_entry_array = entry_array;

        for (int i = 0; i < LDU_CQ_ENTRIES; i++) begin
            
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
            if (~entry_array[enq_ptr].valid & ldu_cq_enq_valid) begin
                entry_array[enq_ptr].valid <= 1'b1;
                // entry_array[enq_ptr].misaligned
                // entry_array[enq_ptr].mq_index
                entry_array[enq_ptr].killed <= ldu_cq_enq_killed;
                entry_array[enq_ptr].launched <= 1'b0;
                entry_array[enq_ptr].dtlb_hit <= 1'b0;
                entry_array[enq_ptr].dcache_hit <= 1'b0;
                entry_array[enq_ptr].aq_blocking <= 1'b0;
                entry_array[enq_ptr].stalling <= 1'b0;
                // entry_array[enq_ptr].stall_count
                entry_array[enq_ptr].forwarded <= 1'b0;
                // entry_array[enq_ptr].forwarded_ROB_index
                entry_array[enq_ptr].nasty_forward <= 1'b0;
                // entry_array[enq_ptr].nasty_forward_wait_upper_ROB_index
                // entry_array[enq_ptr].nasty_forward_wait_lower_ROB_index_one_hot
                entry_array[enq_ptr].WB_sent <= 1'b0;
                entry_array[enq_ptr].complete <= 1'b0;
                entry_array[enq_ptr].committed <= 1'b0;
                entry_array[enq_ptr].mdp_update_req <= 1'b0;
                entry_array[enq_ptr].second_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_req <= 1'b0;
                entry_array[enq_ptr].complete_req <= 1'b0;
                entry_array[enq_ptr].page_fault <= 1'b0;
                entry_array[enq_ptr].access_fault <= 1'b0;
                entry_array[enq_ptr].op <= ldu_cq_enq_op;
                entry_array[enq_ptr].mdp_info <= ldu_cq_enq_mdp_info;
                entry_array[enq_ptr].dest_PR <= ldu_cq_enq_dest_PR;
                entry_array[enq_ptr].upper_ROB_index <= ldu_cq_enq_ROB_index[LOG_ROB_ENTRIES-1:2];
                case (ldu_cq_enq_ROB_index[1:0])
                    2'h0:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0001;
                    2'h1:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0010;
                    2'h2:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b0100;
                    2'h3:   entry_array[enq_ptr].lower_ROB_index_one_hot <= 4'b1000;
                endcase
                // entry_array[enq_ptr].PA_word
                // entry_array[enq_ptr].byte_mask
                // entry_array[enq_ptr].return_data

                enq_ptr <= enq_ptr_plus_1;
            end

            //////////
            // deq: //
            //////////
            if (entry_array[deq_ptr].valid & entry_array[deq_ptr].committed) begin
                entry_array[enq_ptr].valid <= 1'b0;
                // entry_array[enq_ptr].misaligned
                // entry_array[enq_ptr].mq_index
                entry_array[enq_ptr].killed <= 1'b0;
                entry_array[enq_ptr].launched <= 1'b0;
                entry_array[enq_ptr].dtlb_hit <= 1'b0;
                entry_array[enq_ptr].dcache_hit <= 1'b0;
                entry_array[enq_ptr].aq_blocking <= 1'b0;
                entry_array[enq_ptr].stalling <= 1'b0;
                // entry_array[enq_ptr].stall_count
                entry_array[enq_ptr].forwarded <= 1'b0;
                // entry_array[enq_ptr].forwarded_ROB_index
                entry_array[enq_ptr].nasty_forward <= 1'b0;
                // entry_array[enq_ptr].nasty_forward_wait_upper_ROB_index
                // entry_array[enq_ptr].nasty_forward_wait_lower_ROB_index_one_hot
                entry_array[enq_ptr].WB_sent <= 1'b0;
                entry_array[enq_ptr].complete <= 1'b0;
                entry_array[enq_ptr].committed <= 1'b0;
                entry_array[enq_ptr].mdp_update_req <= 1'b0;
                entry_array[enq_ptr].second_try_req <= 1'b0;
                entry_array[enq_ptr].data_try_req <= 1'b0;
                entry_array[enq_ptr].complete_req <= 1'b0;
                // entry_array[enq_ptr].page_fault
                // entry_array[enq_ptr].access_fault;
                // entry_array[enq_ptr].op
                // entry_array[enq_ptr].mdp_info
                // entry_array[enq_ptr].dest_PR
                // entry_array[enq_ptr].upper_ROB_index
                // entry_array[enq_ptr].lower_ROB_index_one_hot
                // entry_array[enq_ptr].PA_word
                // entry_array[enq_ptr].byte_mask
                // entry_array[enq_ptr].return_data

                deq_ptr <= deq_ptr_plus_1;
            end
        end
    end

endmodule