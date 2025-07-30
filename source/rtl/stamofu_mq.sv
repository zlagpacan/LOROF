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
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_mq_info_ret_bank0_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_mq_info_ret_bank0_ROB_index,
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
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_mq_info_ret_bank1_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_mq_info_ret_bank1_ROB_index,
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

    // ----------------------------------------------------------------
    // Signals:

    typedef struct packed {
        logic valid;
        logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  cq_index;
        logic                               killed;
        logic                               dtlb_hit;
        logic                               committed;
        logic                               ldu_CAM_launch_req;
        logic                               ldu_CAM_launch_sent;
        logic                               ldu_CAM_launch_returned;
        logic                               complete_req;
        logic                               complete;
        logic                               is_mem;
        logic                               page_fault;
        logic                               access_fault;
        logic [MDPT_INFO_WIDTH-1:0]         mdp_info;
        logic [LOG_ROB_ENTRIES-1:0]         ROB_index;
        logic [PA_WIDTH-3:0]                PA_word;
        logic [3:0]                         byte_mask;
        logic [23:0]                        data;
    } entry_t;

    entry_t [STAMOFU_MQ_ENTRIES-1:0] entry_array, next_entry_array;

    logic [LOG_STAMOFU_MQ_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    logic enq_perform;
    logic deq_perform;

    // demux's
    logic [STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_ret_bank0_valid_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0] stamofu_mq_info_ret_bank1_valid_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0] dtlb_miss_resp_valid_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0] ldu_CAM_return_valid_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0] commit_by_entry;

    logic [STAMOFU_MQ_ENTRIES-1:0] wraparound_mask;

    // req pe's
        // not worth masking since so few entries
    logic [STAMOFU_MQ_ENTRIES-1:0]      ldu_CAM_launch_req_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      ldu_CAM_launch_req_ack_one_hot;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  ldu_CAM_launch_req_ack_index;

    logic [STAMOFU_MQ_ENTRIES-1:0]      complete_req_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      complete_req_ack_one_hot;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  complete_req_ack_index;

    logic [STAMOFU_MQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0] rel_ROB_index_by_entry;

    // stamofu CAM pipeline bank 0
    logic                               CAM_stage0_bank0_valid;
    
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage0_bank0_load_rel_age;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_addr_match_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_byte_overlap_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_subset_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_valid_older_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank0_load_is_mdp_match_by_entry;
    
    logic                               CAM_stage1_bank0_valid;

    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_subset_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_mdp_match_by_entry;

    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_unmasked_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_unmasked_one_hot;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank0_load_is_candidate_unmasked_index;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_masked_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank0_load_is_candidate_masked_one_hot;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank0_load_is_candidate_masked_index;
    logic                               CAM_stage1_bank0_found_forward;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank0_load_selected_index;
    logic                               CAM_stage1_bank0_load_is_subset;
    logic                               CAM_stage1_bank0_stall;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank0_stall_count;

    logic                               CAM_stage2_bank0_valid;

    logic                               CAM_stage2_bank0_found_forward;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage2_bank0_load_selected_index;
    logic                               CAM_stage2_bank0_load_is_subset;
    logic                               CAM_stage2_bank0_stall;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage2_bank0_stall_count;

    logic                               CAM_stage2_bank0_forward;
    logic                               CAM_stage2_bank0_nasty_forward;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank0_forward_ROB_index;
    logic [31:0]                        CAM_stage2_bank0_forward_data;

    // stamofu CAM pipeline bank 1
    logic                               CAM_stage0_bank1_valid;
    
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage0_bank1_load_rel_age;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_addr_match_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_byte_overlap_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_subset_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_valid_older_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage0_bank1_load_is_mdp_match_by_entry;
    
    logic                               CAM_stage1_bank1_valid;

    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_subset_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_mdp_match_by_entry;

    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_unmasked_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_unmasked_one_hot;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank1_load_is_candidate_unmasked_index;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_masked_by_entry;
    logic [STAMOFU_MQ_ENTRIES-1:0]      CAM_stage1_bank1_load_is_candidate_masked_one_hot;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank1_load_is_candidate_masked_index;
    logic                               CAM_stage1_bank1_found_forward;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank1_load_selected_index;
    logic                               CAM_stage1_bank1_load_is_subset;
    logic                               CAM_stage1_bank1_stall;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage1_bank1_stall_count;

    logic                               CAM_stage2_bank1_valid;

    logic                               CAM_stage2_bank1_found_forward;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage2_bank1_load_selected_index;
    logic                               CAM_stage2_bank1_load_is_subset;
    logic                               CAM_stage2_bank1_stall;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  CAM_stage2_bank1_stall_count;

    logic                               CAM_stage2_bank1_forward;
    logic                               CAM_stage2_bank1_nasty_forward;
    logic [LOG_ROB_ENTRIES-1:0]         CAM_stage2_bank1_forward_ROB_index;
    logic [31:0]                        CAM_stage2_bank1_forward_data;

    // ----------------------------------------------------------------
    // Logic:

    assign enq_ptr_plus_1 = (enq_ptr == STAMOFU_MQ_ENTRIES-1) ? 0 : enq_ptr + 1;
    assign deq_ptr_plus_1 = (deq_ptr == STAMOFU_MQ_ENTRIES-1) ? 0 : deq_ptr + 1;

    // event demux to entry
    always_comb begin
        stamofu_mq_info_ret_bank0_valid_by_entry = '0;
        stamofu_mq_info_ret_bank1_valid_by_entry = '0;
        dtlb_miss_resp_valid_by_entry = '0;
        ldu_CAM_return_valid_by_entry = '0;
        commit_by_entry = '0;
        
        stamofu_mq_info_ret_bank0_valid_by_entry[stamofu_mq_info_ret_bank0_mq_index] = stamofu_mq_info_ret_bank0_valid;
        stamofu_mq_info_ret_bank1_valid_by_entry[stamofu_mq_info_ret_bank0_mq_index] = stamofu_mq_info_ret_bank1_valid;
        dtlb_miss_resp_valid_by_entry[dtlb_miss_resp_mq_index] = dtlb_miss_resp_valid & dtlb_miss_resp_is_mq;
        ldu_CAM_return_valid_by_entry[ldu_CAM_return_mq_index] = ldu_CAM_return_valid & ldu_CAM_return_is_mq;
        commit_by_entry[stamofu_mq_info_grab_mq_index] = stamofu_mq_info_grab_clear_entry;
    end

    // request PE's
    pe_lsb # (
        .WIDTH(STAMOFU_MQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) LDU_CAM_LAUNCH_PE (
        .req_vec(ldu_CAM_launch_req_by_entry),
        .ack_one_hot(ldu_CAM_launch_req_ack_one_hot),
        .ack_index(ldu_CAM_launch_req_ack_index)
    );
    pe_lsb # (
        .WIDTH(STAMOFU_MQ_ENTRIES), .USE_ONE_HOT(0), .USE_INDEX(1)
    ) COMPLETE_LAUNCH_PE (
        .req_vec(complete_req_by_entry),
        .ack_one_hot(complete_req_ack_one_hot),
        .ack_index(complete_req_ack_index)
    );
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            stamofu_mq_ldu_CAM_launch_valid <= 1'b0;
            stamofu_mq_ldu_CAM_launch_cq_index <= 0;
        end
        else begin
            stamofu_mq_ldu_CAM_launch_valid <= |ldu_CAM_launch_req_by_entry;
            stamofu_mq_ldu_CAM_launch_mq_index <= ldu_CAM_launch_req_ack_index;
        end
    end
    always_comb begin
        stamofu_mq_ldu_CAM_launch_cq_index = entry_array[stamofu_mq_ldu_CAM_launch_mq_index].cq_index;
        stamofu_mq_ldu_CAM_launch_PA_word = entry_array[stamofu_mq_ldu_CAM_launch_mq_index].PA_word;
        stamofu_mq_ldu_CAM_launch_byte_mask = entry_array[stamofu_mq_ldu_CAM_launch_mq_index].byte_mask;
        stamofu_mq_ldu_CAM_launch_write_data = entry_array[stamofu_mq_ldu_CAM_launch_mq_index].data;
        stamofu_mq_ldu_CAM_launch_mdp_info = entry_array[stamofu_mq_ldu_CAM_launch_mq_index].mdp_info;
        stamofu_mq_ldu_CAM_launch_ROB_index = entry_array[stamofu_mq_ldu_CAM_launch_mq_index].ROB_index;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            stamofu_mq_complete_valid <= 1'b0;
            stamofu_mq_complete_cq_index <= 0;
        end
        else begin
            stamofu_mq_complete_valid <= |complete_req_by_entry;
            stamofu_mq_complete_cq_index <= complete_req_ack_index;
        end
    end

    // per-entry state machine
    always_comb begin
        next_entry_array = entry_array;

        for (int i = 0; i < STAMOFU_MQ_ENTRIES; i++) begin
            rel_ROB_index_by_entry[i] = entry_array[i].ROB_index - rob_kill_abs_head_index;

            // stamofu_mq ret bank 0
            if (stamofu_mq_info_ret_bank0_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                next_entry_array[i].cq_index = stamofu_mq_info_ret_bank0_cq_index;
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = stamofu_mq_info_ret_bank0_dtlb_hit;
                // next_entry_array[i].committed = 
                // next_entry_array[i].ldu_CAM_launch_req = 
                // next_entry_array[i].ldu_CAM_launch_sent = 
                // next_entry_array[i].ldu_CAM_launch_returned = 
                // next_entry_array[i].complete_req = 
                // next_entry_array[i].complete = 
                if (
                    stamofu_mq_info_ret_bank0_dtlb_hit
                    & (
                        stamofu_mq_info_ret_bank0_page_fault
                        | stamofu_mq_info_ret_bank0_access_fault)
                ) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                end
                else if (stamofu_mq_info_ret_bank0_dtlb_hit) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b1;
                end
                next_entry_array[i].is_mem = stamofu_mq_info_ret_bank0_is_mem;
                next_entry_array[i].page_fault = stamofu_mq_info_ret_bank0_page_fault;
                next_entry_array[i].access_fault = stamofu_mq_info_ret_bank0_access_fault;
                next_entry_array[i].mdp_info = stamofu_mq_info_ret_bank0_mdp_info;
                next_entry_array[i].ROB_index = stamofu_mq_info_ret_bank0_ROB_index;
                next_entry_array[i].PA_word = stamofu_mq_info_ret_bank0_PA_word;
                next_entry_array[i].byte_mask = stamofu_mq_info_ret_bank0_byte_mask;
                next_entry_array[i].data = stamofu_mq_info_ret_bank0_data;
            end
            // stamofu_mq ret bank 1
            else if (stamofu_mq_info_ret_bank1_valid_by_entry[i]) begin
                // next_entry_array[i].valid = 
                next_entry_array[i].cq_index = stamofu_mq_info_ret_bank1_cq_index;
                // next_entry_array[i].killed = 
                next_entry_array[i].dtlb_hit = stamofu_mq_info_ret_bank1_dtlb_hit;
                // next_entry_array[i].committed = 
                // next_entry_array[i].ldu_CAM_launch_req = 
                // next_entry_array[i].ldu_CAM_launch_sent = 
                // next_entry_array[i].ldu_CAM_launch_returned = 
                // next_entry_array[i].complete_req = 
                // next_entry_array[i].complete = 
                if (
                    stamofu_mq_info_ret_bank1_dtlb_hit
                    & (
                        stamofu_mq_info_ret_bank1_page_fault
                        | stamofu_mq_info_ret_bank1_access_fault)
                ) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                end
                else if (stamofu_mq_info_ret_bank1_dtlb_hit) begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b1;
                end
                next_entry_array[i].is_mem = stamofu_mq_info_ret_bank1_is_mem;
                next_entry_array[i].page_fault = stamofu_mq_info_ret_bank1_page_fault;
                next_entry_array[i].access_fault = stamofu_mq_info_ret_bank1_access_fault;
                next_entry_array[i].mdp_info = stamofu_mq_info_ret_bank1_mdp_info;
                next_entry_array[i].ROB_index = stamofu_mq_info_ret_bank1_ROB_index;
                next_entry_array[i].PA_word = stamofu_mq_info_ret_bank1_PA_word;
                next_entry_array[i].byte_mask = stamofu_mq_info_ret_bank1_byte_mask;
                next_entry_array[i].data = stamofu_mq_info_ret_bank1_data;
            end
            // dtlb miss resp
            else if (dtlb_miss_resp_valid_by_entry[i]) begin
                next_entry_array[i].dtlb_hit = 1'b1;
                // only update PA if not exception so can give VA on exception
                if (~dtlb_miss_resp_page_fault & ~dtlb_miss_resp_access_fault) begin
                    next_entry_array[i].PA_word[PA_WIDTH-3:PA_WIDTH-2-PPN_WIDTH] = dtlb_miss_resp_PPN;
                    next_entry_array[i].ldu_CAM_launch_req = 1'b1;
                end
                else begin
                    next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                end
                next_entry_array[i].is_mem = dtlb_miss_resp_is_mem;
                next_entry_array[i].page_fault = dtlb_miss_resp_page_fault;
                next_entry_array[i].access_fault = dtlb_miss_resp_access_fault;
            end

            // indep behavior:

            // ldu CAM return
            if (ldu_CAM_return_valid_by_entry[i]) begin
                next_entry_array[i].ldu_CAM_launch_returned = 1'b1;
            end

            // ROB complete req (indep)
            if (
                ~entry_array[i].complete
                & ~entry_array[i].complete_req
                & (
                    entry_array[i].ldu_CAM_launch_returned
                    | entry_array[i].page_fault
                    | entry_array[i].access_fault)
            ) begin
                next_entry_array[i].complete_req = 1'b1;
            end

            // commit from cq (indep)
            if (commit_by_entry[i]) begin
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
            if (ldu_CAM_launch_req_ack_one_hot[i]) begin
                next_entry_array[i].ldu_CAM_launch_req = 1'b0;
                next_entry_array[i].ldu_CAM_launch_sent = 1'b1;
            end
            if (complete_req_ack_one_hot[i]) begin
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
    // want youngest older -> greater index -> msb first
    pe_msb # (
        .WIDTH(STAMOFU_CQ_ENTRIES), .USE_ONE_HOT(1), .USE_INDEX(1)
    ) CAM_SELECT_UNMASKED_PE_BANK0 (
        .req_vec(CAM_stage1_bank0_load_is_candidate_unmasked_by_entry),
        .ack_one_hot(CAM_stage1_bank0_load_is_candidate_unmasked_one_hot),
        .ack_index(CAM_stage1_bank0_load_is_candidate_unmasked_index)
    );
    pe_msb # (
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

endmodule