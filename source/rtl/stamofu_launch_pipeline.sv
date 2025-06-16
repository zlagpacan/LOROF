/*
    Filename: stamofu_launch_pipeline.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Launch Pipeline
    Spec: LOROF/spec/design/stamofu_launch_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_launch_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage info
    input logic                                 REQ_valid,
    input logic                                 REQ_is_store,
    input logic                                 REQ_is_amo,
    input logic                                 REQ_is_fence,
    input logic [3:0]                           REQ_op,
    input logic                                 REQ_is_mq,
    input logic                                 REQ_misaligned,
    input logic                                 REQ_misaligned_exception,
    input logic [VPN_WIDTH-1:0]                 REQ_VPN,
    input logic [PO_WIDTH-3:0]                  REQ_PO_word,
    input logic [3:0]                           REQ_byte_mask,
    input logic [31:0]                          REQ_write_data,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    REQ_cq_index,

    // REQ stage feedback
    output logic                                REQ_ack,

    // op enqueue to misaligned queue
    output logic                                stamofu_mq_enq_valid,

    // misaligned queue enqueue feedback
    input logic                                 stamofu_mq_enq_ready,
    input logic [LOG_STAMOFU_MQ_ENTRIES-1:0]    stamofu_mq_enq_index,

    // dtlb req
    output logic                    dtlb_req_valid,
    output logic [VPN_WIDTH-1:0]    dtlb_req_VPN,

    // dtlb req feedback
    input logic                     dtlb_req_ready,

    // dtlb resp
    input logic                     dtlb_resp_hit,
    input logic [PPN_WIDTH-1:0]     dtlb_resp_PPN,
    input logic                     dtlb_resp_is_mem,
    input logic                     dtlb_resp_page_fault,
    input logic                     dtlb_resp_access_fault,

    // dcache req
    output logic                                    dcache_req_valid,
    output logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0]    dcache_req_block_offset,
    output logic [DCACHE_INDEX_WIDTH-1:0]           dcache_req_index,

    // dcache req feedback
    input logic                                     dcache_req_ready,

    // dcache resp
    input logic [1:0]                               dcache_resp_valid_by_way,
    input logic [1:0]                               dcache_resp_exclusive_by_way,
    input logic [1:0][DCACHE_TAG_WIDTH-1:0]         dcache_resp_tag_by_way,
    
    // dcache resp feedback
    output logic                                    dcache_resp_hit_valid,
    output logic                                    dcache_resp_hit_exclusive,
    output logic                                    dcache_resp_hit_way,
    output logic                                    dcache_resp_miss_valid,
    output logic                                    dcache_resp_miss_exclusive,
    output logic [DCACHE_TAG_WIDTH-1:0]             dcache_resp_miss_tag,

    // CAM launch
    output logic                                ldu_CAM_launch_valid,
    output logic [PA_WIDTH-2-1:0]               ldu_CAM_launch_PA_word,
    output logic [3:0]                          ldu_CAM_launch_byte_mask,
    output logic [31:0]                         ldu_CAM_launch_write_data,
    output logic [LOG_ROB_ENTRIES-1:0]          ldu_CAM_launch_ROB_index,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   ldu_CAM_launch_cq_index,
    output logic                                ldu_CAM_launch_is_mq,
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   ldu_CAM_launch_mq_index,

    // central queue info grab
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_cq_info_grab_cq_index,
    input logic                                 stamofu_cq_info_grab_mem_aq,
    input logic                                 stamofu_cq_info_grab_io_aq,
    input logic                                 stamofu_cq_info_grab_mem_rl,
    input logic                                 stamofu_cq_info_grab_io_rl,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_cq_info_grab_ROB_index,

    // central queue info ret
    output logic                                stamofu_cq_info_ret_valid,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_cq_info_ret_cq_index,
    output logic                                stamofu_cq_info_ret_dtlb_hit,
    output logic                                stamofu_cq_info_ret_page_fault,
    output logic                                stamofu_cq_info_ret_access_fault,
    output logic                                stamofu_cq_info_ret_is_mem,
    output logic                                stamofu_cq_info_ret_mem_aq,
    output logic                                stamofu_cq_info_ret_io_aq,
    output logic                                stamofu_cq_info_ret_mem_rl,
    output logic                                stamofu_cq_info_ret_io_rl,
    output logic                                stamofu_cq_info_ret_misaligned,
    output logic                                stamofu_cq_info_ret_misaligned_exception,
    output logic [PA_WIDTH-2-1:0]               stamofu_cq_info_ret_PA_word,
    output logic [3:0]                          stamofu_cq_info_ret_byte_mask,
    output logic [31:0]                         stamofu_cq_info_ret_data,

    // misaligned queue info ret
    output logic                                stamofu_mq_info_ret_valid,
    output logic [LOG_STAMOFU_MQ_ENTRIES-1:0]   stamofu_mq_info_ret_mq_index,
    output logic                                stamofu_mq_info_ret_dtlb_hit,
    output logic                                stamofu_mq_info_ret_page_fault,
    output logic                                stamofu_mq_info_ret_access_fault,
    output logic                                stamofu_mq_info_ret_is_mem,
    output logic [PA_WIDTH-2-1:0]               stamofu_mq_info_ret_PA_word,
    output logic [3:0]                          stamofu_mq_info_ret_byte_mask,
    output logic [31:0]                         stamofu_mq_info_ret_data,

    // aq update
    output logic                        stamofu_aq_update_valid,
    output logic                        stamofu_aq_update_mem_aq,
    output logic                        stamofu_aq_update_io_aq,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_aq_update_ROB_index
);

    // exec_mode, virtual_mode, ASID, MXR, and SUM are all handled by ldu_launch_pipeline

    // send dcache prefetch miss only if told that bank is ready
        // not used by ldu launch nor write buffer and MSHR available

    // transfer SFENCE.VMA virtual address through stamofu_cq_info_ret_PA_word

    // ----------------------------------------------------------------
    // REQ stage signals:

    logic                               REQ_stage_valid;
    logic                               REQ_stage_is_store;
    logic                               REQ_stage_is_amo;
    logic                               REQ_stage_is_fence;
    logic [3:0]                         REQ_stage_op;
    logic                               REQ_stage_is_mq;
    logic                               REQ_stage_misaligned;
    logic                               REQ_stage_misaligned_exception;
    logic [PO_WIDTH-3:0]                REQ_stage_PO_word;
    logic [3:0]                         REQ_stage_byte_mask;
    logic [31:0]                        REQ_stage_write_data;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  REQ_stage_cq_index;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  REQ_stage_mq_index;

    logic                               REQ_stage_exclusive;

    logic                               REQ_stage_prefetch_dcache;

    logic [VPN_WIDTH-1:0]               REQ_stage_VPN;

    // ----------------------------------------------------------------
    // RESP stage signals:

    logic                               RESP_stage_valid;
    logic                               RESP_stage_is_store;
    logic                               RESP_stage_is_amo;
    logic                               RESP_stage_is_fence;
    logic [3:0]                         RESP_stage_op;
    logic                               RESP_stage_is_mq;
    logic                               RESP_stage_misaligned;
    logic                               RESP_stage_misaligned_exception;
    logic [PO_WIDTH-3:0]                RESP_stage_PO_word;
    logic [3:0]                         RESP_stage_byte_mask;
    logic [31:0]                        RESP_stage_write_data;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  RESP_stage_cq_index;
    logic [LOG_STAMOFU_MQ_ENTRIES-1:0]  RESP_stage_mq_index;

    logic                               RESP_stage_exclusive;

    logic                               RESP_stage_prefetch_dcache;

    logic [VPN_WIDTH-1:0]               RESP_stage_VPN;

    logic [PA_WIDTH-3:0]                RESP_stage_PA_word;
    logic [PA_WIDTH-3:0]                RESP_stage_return_PA_word;

    logic                               RESP_stage_dtlb_hit;
    logic [DCACHE_TAG_WIDTH-1:0]        RESP_stage_dcache_tag;
    logic [1:0]                         RESP_stage_dcache_vtm_by_way;
    logic                               RESP_stage_dcache_vtm;

    // ----------------------------------------------------------------
    // REQ stage logic:

    // stall, control, and ack logic
    always_comb begin

        // check for good REQ
            // need dtlb ready (as long as not SFENCE.VMA or misaligned exception), stamofu mq ready if applicable
        if (
            REQ_valid
            & (dtlb_req_ready | REQ_stage_is_fence | REQ_misaligned_exception)
            & (~REQ_is_mq | stamofu_mq_enq_ready)
        ) begin
            REQ_stage_valid = 1'b1;

            REQ_ack = 1'b1;
        end

        // otherwise, REQ stage NOP
        else begin
            REQ_stage_valid = 1'b0;

            REQ_ack = 1'b0;
        end
    end

    // dataflow
    always_comb begin
        // REQ_stage_valid // handled ^
        REQ_stage_is_store = REQ_is_store;
        REQ_stage_is_amo = REQ_is_amo;
        REQ_stage_is_fence = REQ_is_fence;
        REQ_stage_op = REQ_op;
        REQ_stage_is_mq = REQ_is_mq;
        REQ_stage_misaligned = REQ_misaligned;
        REQ_stage_misaligned_exception = REQ_misaligned_exception;
        REQ_stage_PO_word = REQ_PO_word;
        REQ_stage_byte_mask = REQ_byte_mask;
        REQ_stage_write_data = REQ_write_data;
        REQ_stage_cq_index = REQ_cq_index;
        REQ_stage_mq_index = stamofu_mq_enq_index;

        // everything except LR.W requires exclusive
        REQ_stage_exclusive = ~(REQ_stage_is_amo & (REQ_stage_op == 4'b0010));

        REQ_stage_prefetch_dcache = 
            dcache_req_ready 
            & ~REQ_stage_is_fence
            & (~REQ_stage_is_amo | (REQ_stage_op == 4'b0010)) // only prefetch stores, LR.W
            & ~REQ_stage_misaligned_exception;

        // for SFENCE.VMA
        REQ_stage_VPN = REQ_VPN;

        stamofu_mq_enq_valid = REQ_ack & REQ_stage_is_mq;

        dtlb_req_valid = 
            REQ_ack 
            & ~REQ_stage_is_fence
            & ~REQ_stage_misaligned_exception;
        dtlb_req_VPN = REQ_stage_VPN;

        dcache_req_valid = 
            REQ_ack 
            & ~REQ_stage_is_fence
            & (~REQ_stage_is_amo | (REQ_stage_op == 4'b0010)) // only prefetch stores, LR.W
            & ~REQ_stage_misaligned_exception;
        dcache_req_block_offset = {REQ_stage_PO_word[DCACHE_WORD_ADDR_BANK_BIT-1 : 0], 2'b00};
        // bank will be statically determined for instantation
        dcache_req_index = REQ_stage_PO_word[DCACHE_INDEX_WIDTH + DCACHE_WORD_ADDR_BANK_BIT + 1 - 1 : DCACHE_WORD_ADDR_BANK_BIT + 1];
            // doesn't include bank bit
    end

    // ----------------------------------------------------------------
    // RESP stage logic:

    // REQ/RESP stage FF output
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            RESP_stage_valid <= '0;
            RESP_stage_is_store <= '0;
            RESP_stage_is_amo <= '0;
            RESP_stage_is_fence <= '0;
            RESP_stage_op <= '0;
            RESP_stage_is_mq <= '0;
            RESP_stage_misaligned <= '0;
            RESP_stage_misaligned_exception <= '0;
            RESP_stage_PO_word <= '0;
            RESP_stage_byte_mask <= '0;
            RESP_stage_write_data <= '0;
            RESP_stage_cq_index <= '0;
            RESP_stage_mq_index <= '0;
            RESP_stage_exclusive <= 1'b1;
            RESP_stage_prefetch_dcache <= '0;
            RESP_stage_VPN <= '0;
        end
        else begin
            RESP_stage_valid <= REQ_stage_valid;
            RESP_stage_is_store <= REQ_stage_is_store;
            RESP_stage_is_amo <= REQ_stage_is_amo;
            RESP_stage_is_fence <= REQ_stage_is_fence;
            RESP_stage_op <= REQ_stage_op;
            RESP_stage_is_mq <= REQ_stage_is_mq;
            RESP_stage_misaligned <= REQ_stage_misaligned;
            RESP_stage_misaligned_exception <= REQ_stage_misaligned_exception;
            RESP_stage_PO_word <= REQ_stage_PO_word;
            RESP_stage_byte_mask <= REQ_stage_byte_mask;
            RESP_stage_write_data <= REQ_stage_write_data;
            RESP_stage_cq_index <= REQ_stage_cq_index;
            RESP_stage_mq_index <= REQ_stage_mq_index;
            RESP_stage_exclusive <= REQ_stage_exclusive;
            RESP_stage_prefetch_dcache <= REQ_stage_prefetch_dcache;
            RESP_stage_VPN <= REQ_stage_VPN;
        end
    end

    // dataflow
    always_comb begin

        // central queue info grab
        stamofu_cq_info_grab_cq_index = RESP_stage_cq_index;

        // dcache hit and miss logic

        // SFENCE.VMA and exceptions need VPN instead of PPN
        RESP_stage_PA_word = {dtlb_resp_PPN, RESP_stage_PO_word};
        if (RESP_stage_is_fence | (dtlb_resp_page_fault | dtlb_resp_access_fault) | RESP_stage_misaligned_exception) begin
            RESP_stage_return_PA_word = {2'b00, RESP_stage_VPN, RESP_stage_PO_word};
        end else begin
            RESP_stage_return_PA_word = RESP_stage_PA_word;
        end
        RESP_stage_dcache_tag = RESP_stage_PA_word[PA_WIDTH-3:PA_WIDTH-DCACHE_TAG_WIDTH-2];
        RESP_stage_dcache_vtm_by_way[0] = 
            dcache_resp_valid_by_way[0]
            & (dcache_resp_exclusive_by_way[0] | ~RESP_stage_exclusive)
            & (dcache_resp_tag_by_way[0] == RESP_stage_dcache_tag);
        RESP_stage_dcache_vtm_by_way[1] = 
            dcache_resp_valid_by_way[1]
            & (dcache_resp_exclusive_by_way[1] | ~RESP_stage_exclusive)
            & (dcache_resp_tag_by_way[1] == RESP_stage_dcache_tag);
        RESP_stage_dcache_vtm = |RESP_stage_dcache_vtm_by_way;

        dcache_resp_hit_valid = 
            RESP_stage_valid
            & RESP_stage_prefetch_dcache
            & dtlb_resp_hit
            & ~(dtlb_resp_page_fault | dtlb_resp_access_fault)
            & RESP_stage_dcache_vtm;
        dcache_resp_hit_exclusive = RESP_stage_exclusive;
        dcache_resp_hit_way = RESP_stage_dcache_vtm_by_way[1];
        dcache_resp_miss_valid = 
            RESP_stage_valid
            & RESP_stage_prefetch_dcache
            & dtlb_resp_hit
            & ~(dtlb_resp_page_fault | dtlb_resp_access_fault)
            & ~RESP_stage_dcache_vtm;
        dcache_resp_miss_exclusive = RESP_stage_exclusive;
        dcache_resp_miss_tag = RESP_stage_dcache_tag;

        // CAM
        ldu_CAM_launch_valid = 
            RESP_stage_valid
            & ~RESP_stage_is_fence
            & dtlb_resp_hit
            & ~(dtlb_resp_page_fault | dtlb_resp_access_fault)
            & ~RESP_stage_misaligned_exception;
        ldu_CAM_launch_PA_word = RESP_stage_return_PA_word;
        ldu_CAM_launch_byte_mask = RESP_stage_byte_mask;
        ldu_CAM_launch_write_data = RESP_stage_write_data;
        ldu_CAM_launch_ROB_index = stamofu_cq_info_grab_ROB_index;
        ldu_CAM_launch_cq_index = RESP_stage_cq_index;
        ldu_CAM_launch_is_mq = RESP_stage_is_mq;
        ldu_CAM_launch_mq_index = RESP_stage_mq_index;

        // cq ret
        stamofu_cq_info_ret_valid = RESP_stage_valid & ~RESP_stage_is_mq;
        stamofu_cq_info_ret_cq_index = RESP_stage_cq_index;
        stamofu_cq_info_ret_dtlb_hit = dtlb_resp_hit;
        stamofu_cq_info_ret_page_fault = dtlb_resp_page_fault;
        stamofu_cq_info_ret_access_fault = dtlb_resp_access_fault;
        stamofu_cq_info_ret_is_mem = dtlb_resp_is_mem;
        // update aq, rl if amo and know mem vs. io
        if (RESP_stage_is_amo & dtlb_resp_hit) begin
            stamofu_cq_info_ret_mem_aq = stamofu_cq_info_grab_mem_aq & dtlb_resp_is_mem;
            stamofu_cq_info_ret_io_aq = stamofu_cq_info_grab_io_aq & ~dtlb_resp_is_mem;
            stamofu_cq_info_ret_mem_rl = stamofu_cq_info_grab_mem_rl & dtlb_resp_is_mem;
            stamofu_cq_info_ret_io_rl = stamofu_cq_info_grab_io_rl & ~dtlb_resp_is_mem;
        end
        else begin
            stamofu_cq_info_ret_mem_aq = stamofu_cq_info_grab_mem_aq;
            stamofu_cq_info_ret_io_aq = stamofu_cq_info_grab_io_aq;
            stamofu_cq_info_ret_mem_rl = stamofu_cq_info_grab_mem_rl;
            stamofu_cq_info_ret_io_rl = stamofu_cq_info_grab_io_rl;
        end
        stamofu_cq_info_ret_misaligned = RESP_stage_misaligned;
        stamofu_cq_info_ret_misaligned_exception = RESP_stage_misaligned_exception;
        stamofu_cq_info_ret_PA_word = RESP_stage_return_PA_word;
        stamofu_cq_info_ret_byte_mask = RESP_stage_byte_mask;
        stamofu_cq_info_ret_data = RESP_stage_write_data;

        // mq ret
        stamofu_mq_info_ret_valid = RESP_stage_valid & RESP_stage_is_mq;
        stamofu_mq_info_ret_mq_index = RESP_stage_mq_index;
        stamofu_mq_info_ret_dtlb_hit = dtlb_resp_hit;
        stamofu_mq_info_ret_page_fault = dtlb_resp_page_fault;
        stamofu_mq_info_ret_access_fault = dtlb_resp_access_fault;
        stamofu_mq_info_ret_is_mem = dtlb_resp_is_mem;
        stamofu_mq_info_ret_PA_word = RESP_stage_return_PA_word;
        stamofu_mq_info_ret_byte_mask = RESP_stage_byte_mask;
        stamofu_mq_info_ret_data = RESP_stage_write_data;

        // amo's send aq update
        stamofu_aq_update_valid = RESP_stage_valid & RESP_stage_is_amo & dtlb_resp_hit;
        stamofu_aq_update_mem_aq = stamofu_cq_info_grab_mem_aq & dtlb_resp_is_mem;
        stamofu_aq_update_io_aq = stamofu_cq_info_grab_io_aq & ~dtlb_resp_is_mem;
        stamofu_aq_update_ROB_index = stamofu_cq_info_grab_ROB_index;
    end

endmodule