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
    input logic [1:0][DCACHE_TAG_WIDTH-1:0]         dcache_resp_tag_by_way,
    input logic [1:0][31:0]                         dcache_resp_data_by_way,
    
    // dcache resp feedback
    output logic                                    dcache_resp_hit_valid,
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
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_cq_info_grab_ROB_index,

    // central queue info ret
    output logic                                stamofu_cq_info_ret_valid,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_cq_info_ret_cq_index,
    output logic                                stamofu_cq_info_ret_dtlb_hit,
    output logic                                stamofu_cq_info_ret_page_fault,
    output logic                                stamofu_cq_info_ret_access_fault,
    output logic                                stamofu_cq_info_ret_is_mem,
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

    // misprediction notification to ROB
    output logic                        mispred_notif_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  mispred_notif_ROB_index,

    // misprediction notification backpressure from ROB
    input logic                         mispred_notif_ready,

    // exception to ROB
    output logic                        rob_exception_valid,
    output logic                        rob_exception_misaligned,
    output logic                        rob_exception_page_fault,
    output logic                        rob_exception_access_fault,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_exception_ROB_index,

    // exception backpressure from ROB
    input logic                         rob_exception_ready,
);

    // exec_mode, virtual_mode, ASID, MXR, and SUM are all handled by ldu_launch_pipeline

    // send dcache prefetch miss only if told that bank is ready
        // not used by ldu launch nor write buffer and MSHR available

    // ----------------------------------------------------------------
    // Control signals:

    logic stall_RESP;

    logic RESP_first_cycle;
    logic RESP_stage_perform;

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

    logic                               REQ_stage_prefetch_dcache;

    // ----------------------------------------------------------------
    // RESP stage signals:

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

    logic                               RESP_stage_prefetch_dcache;

    logic [LOG_ROB_ENTRIES-1:0]         RESP_stage_ROB_index;

    logic                               RESP_stage_selected_page_fault;
    logic                               RESP_stage_selected_access_fault;
    logic                               RESP_stage_selected_is_mem;
    logic [PPN_WIDTH-1:0]               RESP_stage_selected_PPN;
    logic [PA_WIDTH-3:0]                RESP_stage_selected_PA_word;

    logic                               RESP_stage_dtlb_hit;
    logic [DCACHE_TAG_WIDTH-1:0]        RESP_stage_dcache_tag;
    logic [1:0]                         RESP_stage_dcache_vtm_by_way;
    logic                               RESP_stage_dcache_vtm;

    logic                               RESP_stage_do_exception;
    logic                               RESP_stage_do_cq_ret;
    logic                               RESP_stage_do_mq_ret;

    // saved dtlb resp
    logic                   saved_dtlb_resp_hit;
    logic [PPN_WIDTH-1:0]   saved_dtlb_resp_PPN;
    logic                   saved_dtlb_resp_is_mem;
    logic                   saved_dtlb_resp_page_fault;
    logic                   saved_dtlb_resp_access_fault;

    // saved dcache resp
    logic [1:0]                         saved_dcache_resp_valid_by_way;
    logic [1:0][DCACHE_TAG_WIDTH-1:0]   saved_dcache_resp_tag_by_way;
    logic [1:0][31:0]                   saved_dcache_resp_data_by_way;

    // selected dtlb resp
    logic                   selected_dtlb_resp_hit;
    logic [PPN_WIDTH-1:0]   selected_dtlb_resp_PPN;
    logic                   selected_dtlb_resp_is_mem;
    logic                   selected_dtlb_resp_page_fault;
    logic                   selected_dtlb_resp_access_fault;

    // selected dcache resp
    logic [1:0]                         selected_dcache_resp_valid_by_way;
    logic [1:0][DCACHE_TAG_WIDTH-1:0]   selected_dcache_resp_tag_by_way;
    logic [1:0][31:0]                   selected_dcache_resp_data_by_way;

    // ----------------------------------------------------------------
    // REQ stage logic:

    // stall, control, and ack logic
    always_comb begin


    end

endmodule