/*
    Filename: ldu_launch_pipeline.sv
    Author: zlagpacan
    Description: RTL for Load Unit Launch Pipeline
    Spec: LOROF/spec/design/ldu_launch_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module ldu_launch_pipeline (

    // seq
    input logic CLK,
    input logic nRST,
    
    // first try
    input logic                             first_try_valid,
    input logic                             first_try_is_mq,
    input logic                             first_try_misaligned,
    input logic [VPN_WIDTH-1:0]             first_try_VPN,
    input logic [PO_WIDTH-3:0]              first_try_PO_word,
    input logic [3:0]                       first_try_byte_mask,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    first_try_cq_index,

    // first try feedback
    output logic                            first_try_ack,

    // op enqueue to misaligned queue
    output logic                            ldu_mq_enq_valid,

    // misaligned queue enqueue feedback
    input logic                             ldu_mq_enq_ready,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    ldu_mq_enq_index,

    // ROB info
    input logic [LOG_ROB_ENTRIES-1:0]   rob_abs_head_index,

    // acquire advertisement
    input logic                         stamofu_aq_mem_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_mem_aq_oldest_abs_ROB_index,
    input logic                         stamofu_aq_io_aq_active,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_io_aq_oldest_abs_ROB_index,
    
    // second try bank 0
    input logic                             second_try_bank0_valid,
    input logic                             second_try_bank0_is_mq,
    input logic                             second_try_bank0_misaligned,
    input logic [PPN_WIDTH-1:0]             second_try_bank0_PPN,
    input logic [PO_WIDTH-3:0]              second_try_bank0_PO_word,
    input logic [3:0]                       second_try_bank0_byte_mask,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    second_try_bank0_cq_index,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    second_try_bank0_mq_index,

    // second try bank 0 feedback
    output logic                            second_try_bank0_ack,
    
    // second try bank 1
    input logic                             second_try_bank1_valid,
    input logic                             second_try_bank1_is_mq,
    input logic                             second_try_bank1_misaligned,
    input logic [PPN_WIDTH-1:0]             second_try_bank1_PPN,
    input logic [PO_WIDTH-3:0]              second_try_bank1_PO_word,
    input logic [3:0]                       second_try_bank1_byte_mask,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    second_try_bank1_cq_index,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    second_try_bank1_mq_index,

    // second try bank 1 feedback
    output logic                            second_try_bank1_ack,
    
    // data try
    input logic                         data_try_valid,
    input logic                         data_try_page_fault,
    input logic                         data_try_access_fault,
    input logic                         data_try_restart,
    input logic [31:0]                  data_try_data,
    input logic [LOG_PR_COUNT-1:0]      data_try_PR,
    input logic [LOG_ROB_ENTRIES-1:0]   data_try_ROB_index,

    // data try feedback
    output logic                        data_try_ack,

    // dtlb req bank 0
    output logic                    dtlb_req_bank0_valid,
    output logic [1:0]              dtlb_req_bank0_exec_mode,
    output logic                    dtlb_req_bank0_virtual_mode,
    output logic                    dtlb_req_bank0_MXR,
    output logic                    dtlb_req_bank0_SUM,
    output logic [VPN_WIDTH-1:0]    dtlb_req_bank0_VPN,
    output logic [ASID_WIDTH-1:0]   dtlb_req_bank0_ASID,

    // dtlb req bank 0 feedback
    input logic                     dtlb_req_bank0_ready,

    // dtlb resp bank 0
    input logic                     dtlb_resp_bank0_hit,
    input logic [PPN_WIDTH-1:0]     dtlb_resp_bank0_PPN,
    input logic                     dtlb_resp_bank0_is_mem,
    input logic                     dtlb_resp_bank0_page_fault,
    input logic                     dtlb_resp_bank0_access_fault,

    // dtlb req bank 1
    output logic                    dtlb_req_bank1_valid,
    output logic [1:0]              dtlb_req_bank1_exec_mode,
    output logic                    dtlb_req_bank1_virtual_mode,
    output logic                    dtlb_req_bank1_MXR,
    output logic                    dtlb_req_bank1_SUM,
    output logic [VPN_WIDTH-1:0]    dtlb_req_bank1_VPN,
    output logic [ASID_WIDTH-1:0]   dtlb_req_bank1_ASID,

    // dtlb req bank 1 feedback
    input logic                     dtlb_req_bank1_ready,

    // dtlb resp bank 1
    input logic                     dtlb_resp_bank1_hit,
    input logic [PPN_WIDTH-1:0]     dtlb_resp_bank1_PPN,
    input logic                     dtlb_resp_bank1_is_mem,
    input logic                     dtlb_resp_bank1_page_fault,
    input logic                     dtlb_resp_bank1_access_fault,

    // dcache req bank 0
    output logic                                    dcache_req_bank0_valid,
    output logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0]    dcache_req_bank0_block_offset,
    output logic [DCACHE_INDEX_WIDTH-1:0]           dcache_req_bank0_index,

    // dcache req bank 0 feedback
    input logic                                     dcache_req_bank0_ready,

    // dcache resp bank 0
    input logic [1:0]                               dcache_resp_bank0_valid_by_way,
    input logic [1:0][DCACHE_TAG_WIDTH-1:0]         dcache_resp_bank0_tag_by_way,
    input logic [1:0][31:0]                         dcache_resp_bank0_data_by_way,
    
    // dcache resp bank 0 feedback
    output logic                                    dcache_resp_bank0_hit_valid,
    output logic                                    dcache_resp_bank0_hit_way,
    output logic                                    dcache_resp_bank0_miss_valid,
    output logic [DCACHE_TAG_WIDTH-1:0]             dcache_resp_bank0_miss_tag,

    // dcache req bank 1
    output logic                                    dcache_req_bank1_valid,
    output logic [DCACHE_BLOCK_OFFSET_WIDTH-1:0]    dcache_req_bank1_block_offset,
    output logic [DCACHE_INDEX_WIDTH-1:0]           dcache_req_bank1_index,

    // dcache req bank 1 feedback
    input logic                                     dcache_req_bank1_ready,

    // dcache resp bank 1
    input logic [1:0]                               dcache_resp_bank1_valid_by_way,
    input logic [1:0][DCACHE_TAG_WIDTH-1:0]         dcache_resp_bank1_tag_by_way,
    input logic [1:0][31:0]                         dcache_resp_bank1_data_by_way,
    
    // dcache resp bank 1 feedback
    output logic                                    dcache_resp_bank1_hit_valid,
    output logic                                    dcache_resp_bank1_hit_way,
    output logic                                    dcache_resp_bank1_miss_valid,
    output logic [DCACHE_TAG_WIDTH-1:0]             dcache_resp_bank1_miss_tag,

    // bank 0 writeback data to PRF
    output logic                        WB_bank0_valid,
    output logic [31:0]                 WB_bank0_data,
    output logic [LOG_PR_COUNT-1:0]     WB_bank0_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_bank0_ROB_index,

    // bank 1 writeback data to PRF
    output logic                        WB_bank1_valid,
    output logic [31:0]                 WB_bank1_data,
    output logic [LOG_PR_COUNT-1:0]     WB_bank1_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_bank1_ROB_index,

    // CAM bank 0 launch
    output logic                            stamofu_CAM_bank0_valid,
    output logic [PA_WIDTH-2-1:0]           stamofu_CAM_bank0_PA_word,
    output logic [3:0]                      stamofu_CAM_bank0_byte_mask,
    output logic [LOG_ROB_ENTRIES-1:0]      stamofu_CAM_bank0_ROB_index,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   stamofu_CAM_bank0_cq_index,
    output logic                            stamofu_CAM_bank0_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   stamofu_CAM_bank0_mq_index,

    // CAM bank 1 launch
    output logic                            stamofu_CAM_bank1_valid,
    output logic [PA_WIDTH-2-1:0]           stamofu_CAM_bank1_PA_word,
    output logic [3:0]                      stamofu_CAM_bank1_byte_mask,
    output logic [LOG_ROB_ENTRIES-1:0]      stamofu_CAM_bank1_ROB_index,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   stamofu_CAM_bank1_cq_index,
    output logic                            stamofu_CAM_bank1_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   stamofu_CAM_bank1_mq_index,

    // central queue info grab bank 0
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_grab_bank0_cq_index,
    input logic [3:0]                       ldu_cq_info_grab_bank0_op,
    input logic [LOG_PR_COUNT-1:0]          ldu_cq_info_grab_bank0_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       ldu_cq_info_grab_bank0_ROB_index,
    input logic [PPN_WIDTH-1:0]             ldu_cq_info_grab_bank0_PA_word,

    // misaligned queue info grab bank 0
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_grab_bank0_mq_index,
    input logic [PPN_WIDTH-1:0]             ldu_mq_info_grab_bank0_PA_word,

    // central queue info grab bank 1
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_grab_bank1_cq_index,
    input logic [3:0]                       ldu_cq_info_grab_bank1_op,
    input logic [LOG_PR_COUNT-1:0]          ldu_cq_info_grab_bank1_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       ldu_cq_info_grab_bank1_ROB_index,
    input logic [PPN_WIDTH-1:0]             ldu_cq_info_grab_bank1_PA_word,

    // misaligned queue info grab bank 1
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_grab_bank1_mq_index,
    input logic [PPN_WIDTH-1:0]             ldu_mq_info_grab_bank1_PA_word,

    // central queue info ret bank 0
    output logic                            ldu_cq_info_ret_bank0_valid,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_ret_bank0_cq_index,
    output logic                            ldu_cq_info_ret_bank0_dtlb_hit,
    output logic                            ldu_cq_info_ret_bank0_dcache_hit,
    output logic                            ldu_cq_info_ret_bank0_is_mem,
    output logic                            ldu_cq_info_ret_bank0_aq_blocking,
    output logic [31:0]                     ldu_cq_info_ret_bank0_data,

    // misaligned queue info ret bank 0
    output logic                            ldu_mq_info_ret_bank0_valid,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_ret_bank0_mq_index,
    output logic                            ldu_mq_info_ret_bank0_dtlb_hit,
    output logic                            ldu_mq_info_ret_bank0_dcache_hit,
    output logic                            ldu_mq_info_ret_bank0_is_mem,
    output logic                            ldu_mq_info_ret_bank0_aq_blocking,
    output logic [31:0]                     ldu_mq_info_ret_bank0_data,

    // central queue info ret bank 1
    output logic                            ldu_cq_info_ret_bank1_valid,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_ret_bank1_cq_index,
    output logic                            ldu_cq_info_ret_bank1_dtlb_hit,
    output logic                            ldu_cq_info_ret_bank1_dcache_hit,
    output logic                            ldu_cq_info_ret_bank1_is_mem,
    output logic                            ldu_cq_info_ret_bank1_aq_blocking,
    output logic [31:0]                     ldu_cq_info_ret_bank1_data,

    // misaligned queue info ret bank 1
    output logic                            ldu_mq_info_ret_bank1_valid,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_ret_bank1_mq_index,
    output logic                            ldu_mq_info_ret_bank1_dtlb_hit,
    output logic                            ldu_mq_info_ret_bank1_dcache_hit,
    output logic                            ldu_mq_info_ret_bank1_is_mem,
    output logic                            ldu_mq_info_ret_bank1_aq_blocking,
    output logic [31:0]                     ldu_mq_info_ret_bank1_data,

    // misprediction notification to ROB bank 0
    output logic                        mispred_notif_bank0_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  mispred_notif_bank0_ROB_index,

    // misprediction notification backpressure from ROB bank 0
    input logic                         mispred_notif_bank0_ready,

    // misprediction notification to ROB bank 1
    output logic                        mispred_notif_bank1_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  mispred_notif_bank1_ROB_index,

    // misprediction notification backpressure from ROB bank 1
    input logic                         mispred_notif_bank1_ready,

    // exception to ROB bank 0
    output logic                        rob_exception_bank0_valid,
    output logic                        rob_exception_bank0_page_fault,
    output logic                        rob_exception_bank0_access_fault,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_exception_bank0_ROB_index,

    // exception backpressure from ROB bank 0
    input logic                         rob_exception_bank0_ready,

    // exception to ROB bank 1
    output logic                        rob_exception_bank1_valid,
    output logic                        rob_exception_bank1_page_fault,
    output logic                        rob_exception_bank1_access_fault,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_exception_bank1_ROB_index,

    // exception backpressure from ROB bank 1
    input logic                         rob_exception_bank1_ready,

    // restart from ROB
    input logic         rob_restart_valid,
    input logic [1:0]   rob_restart_exec_mode,
    input logic         rob_restart_virtual_mode,
    input logic         rob_restart_MXR,
    input logic         rob_restart_SUM
);

    // ----------------------------------------------------------------
    // Control signals:

    logic stall_REQ_bank0;
    logic stall_REQ_bank1;
    logic stall_RESP_bank0;
    logic stall_RESP_bank1;
    logic stall_RET_bank0;
    logic stall_RET_bank1;

    // ----------------------------------------------------------------
    // REQ stage signals:

    logic first_try_bank0_valid;
    logic first_try_bank1_valid;

    logic                           REQ_stage_bank0_valid;
    logic                           REQ_stage_bank0_is_mq;
    logic                           REQ_stage_bank0_misaligned;
    logic [VPN_WIDTH-1:0]           REQ_stage_bank0_VPN;
    logic [PPN_WIDTH-1:0]           REQ_stage_bank0_PPN;
    logic [PO_WIDTH-3:0]            REQ_stage_bank0_PO_word;
    logic [3:0]                     REQ_stage_bank0_byte_mask;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  REQ_stage_bank0_cq_index;
    logic [LOG_LDU_MQ_ENTRIES-1:0]  REQ_stage_bank0_mq_index;
    logic                           REQ_stage_bank0_do_dtlb_req;
    logic                           REQ_stage_bank0_do_dcache_req;
    logic                           REQ_stage_bank0_do_WB;
    logic                           REQ_stage_bank0_do_CAM;
    logic                           REQ_stage_bank0_do_restart;
    logic                           REQ_stage_bank0_do_page_fault;
    logic                           REQ_stage_bank0_do_access_fault;

    // ----------------------------------------------------------------
    // REQ stage logic:

    // first try bank demux
    assign first_try_bank0_valid = 
        first_try_valid
        & first_try_PO_word[DCACHE_WORD_ADDR_BANK_BIT] == 1'b0;

    assign first_try_bank1_valid = 
        first_try_valid
        & first_try_PO_word[DCACHE_WORD_ADDR_BANK_BIT] == 1'b1;

    // bank 0
    always_comb begin

        // check first try
        if (~stall_REQ) begin

        end

        // otherwise, check second try
        else if () begin

        end

        // otherwise, check data
        else if () begin
            
        end
        
        // otherwise, NOP
        else begin

        end
    end

endmodule