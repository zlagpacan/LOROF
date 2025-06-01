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

module ldu_launch_pipeline #(
    parameter INIT_ASID = 9'h0,
    parameter INIT_EXEC_MODE = M_MODE,
    parameter INIT_VIRTUAL_MODE = 1'b0,
    parameter INIT_MXR = 1'b0,
    parameter INIT_SUM = 1'b0
) (

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
    
    // second try
    input logic                             second_try_valid,
    input logic                             second_try_is_mq,
    input logic                             second_try_misaligned,
    input logic [VPN_WIDTH-1:0]             second_try_VPN,
    input logic [PO_WIDTH-3:0]              second_try_PO_word,
    input logic [3:0]                       second_try_byte_mask,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    second_try_cq_index,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    second_try_mq_index,

    // second try feedback
    output logic                            second_try_ack,
    
    // data try
    input logic                             data_try_valid,
    input logic                             data_try_restart,
    input logic [31:0]                      data_try_data,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    data_try_cq_index,

    // data try feedback
    output logic                            data_try_ack,

    // dtlb req
    output logic                    dtlb_req_valid,
    output logic [1:0]              dtlb_req_exec_mode,
    output logic                    dtlb_req_virtual_mode,
    output logic [ASID_WIDTH-1:0]   dtlb_req_ASID,
    output logic                    dtlb_req_MXR,
    output logic                    dtlb_req_SUM,
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
    output logic [DCACHE_TAG_WIDTH-1:0]             dcache_resp_miss_tag,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // CAM launch
    output logic                            stamofu_CAM_launch_valid,
    output logic [PA_WIDTH-2-1:0]           stamofu_CAM_launch_PA_word,
    output logic [3:0]                      stamofu_CAM_launch_byte_mask,
    output logic [LOG_ROB_ENTRIES-1:0]      stamofu_CAM_launch_ROB_index,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   stamofu_CAM_launch_cq_index,
    output logic                            stamofu_CAM_launch_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   stamofu_CAM_launch_mq_index,

    // central queue info grab
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_grab_cq_index,
    input logic [3:0]                       ldu_cq_info_grab_op,
    input logic [LOG_PR_COUNT-1:0]          ldu_cq_info_grab_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       ldu_cq_info_grab_ROB_index,
    input logic [PPN_WIDTH-1:0]             ldu_cq_info_grab_PA_word,

    // misaligned queue info grab
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_grab_mq_index,
    input logic [PPN_WIDTH-1:0]             ldu_mq_info_grab_PA_word,

    // central queue info ret
    output logic                            ldu_cq_info_ret_valid,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_ret_cq_index,
    output logic                            ldu_cq_info_ret_dtlb_hit,
    output logic                            ldu_cq_info_ret_dcache_hit,
    output logic                            ldu_cq_info_ret_is_mem,
    output logic                            ldu_cq_info_ret_aq_blocking,
    output logic [31:0]                     ldu_cq_info_ret_data,

    // misaligned queue info ret
    output logic                            ldu_mq_info_ret_valid,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_ret_mq_index,
    output logic                            ldu_mq_info_ret_dtlb_hit,
    output logic                            ldu_mq_info_ret_dcache_hit,
    output logic                            ldu_mq_info_ret_is_mem,
    output logic                            ldu_mq_info_ret_aq_blocking,
    output logic [31:0]                     ldu_mq_info_ret_data,

    // misprediction notification to ROB
    output logic                        mispred_notif_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  mispred_notif_ROB_index,

    // misprediction notification backpressure from ROB
    input logic                         mispred_notif_ready,

    // exception to ROB
    output logic                        rob_exception_valid,
    output logic                        rob_exception_page_fault,
    output logic                        rob_exception_access_fault,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_exception_ROB_index,

    // exception backpressure from ROB
    input logic                         rob_exception_ready,

    // restart from ROB
    input logic         rob_restart_valid,
    input logic [8:0]   rob_restart_ASID,
    input logic [1:0]   rob_restart_exec_mode,
    input logic         rob_restart_virtual_mode,
    input logic         rob_restart_MXR,
    input logic         rob_restart_SUM
);
    // assuming dtlb and dcache resp's are frozen if no new valid is given
        // acts following BRAM clocked reg read behavior
        // equivalently, only latch req -> resp if valid

    // ----------------------------------------------------------------
    // Control signals:

    logic stall_REQ;
    logic stall_RESP;
    logic stall_RET;

    // ----------------------------------------------------------------
    // REQ stage signals:

    logic                           REQ_stage_valid;
    logic                           REQ_stage_is_first;
    logic                           REQ_stage_is_second;
    logic                           REQ_stage_is_data;
    logic                           REQ_stage_is_mq;
    logic                           REQ_stage_misaligned;
    logic                           REQ_stage_do_restart;
    logic [PPN_WIDTH-1:0]           REQ_stage_PN; // VPN if first try, PPN if second try
    logic [PO_WIDTH-3:0]            REQ_stage_PO_word;
    logic [3:0]                     REQ_stage_byte_mask;
    logic [31:0]                    REQ_stage_data;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  REQ_stage_cq_index;
    logic [LOG_LDU_MQ_ENTRIES-1:0]  REQ_stage_mq_index;

    // ----------------------------------------------------------------
    // RESP stage signals:

    logic                           RESP_stage_valid;
    logic                           RESP_stage_is_first;
    logic                           RESP_stage_is_second;
    logic                           RESP_stage_is_data;
    logic                           RESP_stage_is_mq;
    logic                           RESP_stage_misaligned;
    logic                           RESP_stage_do_restart;
    logic [PPN_WIDTH-1:0]           RESP_stage_PN; // VPN if first try, PPN if second try
    logic [PO_WIDTH-3:0]            RESP_stage_PO_word;
    logic [3:0]                     RESP_stage_byte_mask;
    logic [31:0]                    RESP_stage_data;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  RESP_stage_cq_index;
    logic [LOG_LDU_MQ_ENTRIES-1:0]  RESP_stage_mq_index;

    // ----------------------------------------------------------------
    // REQ stage logic:

    // rob-restart determined state
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            dtlb_req_exec_mode <= INIT_EXEC_MODE;
            dtlb_req_virtual_mode <= INIT_VIRTUAL_MODE;
            dtlb_req_ASID <= INIT_ASID;
            dtlb_req_MXR <= INIT_MXR;
            dtlb_req_SUM <= INIT_SUM;
        end
        else begin
            if (rob_restart_valid) begin
                dtlb_req_exec_mode <= rob_restart_exec_mode;
                dtlb_req_virtual_mode <= rob_restart_virtual_mode;
                dtlb_req_ASID <= rob_restart_ASID;
                dtlb_req_MXR <= rob_restart_MXR;
                dtlb_req_SUM <= rob_restart_SUM;
            end
        end
    end

    // stall, control, and ack logic
    always_comb begin

        // check first try
        if (first_try_valid) begin

            // need no propagated stall, dtlb req, dcache req, and ldu mq enq if applicable
            if (
                ~(valid_RESP & stall_RESP)
                & dtlb_req_ready 
                & dcache_req_ready
                & (~first_try_is_mq | ldu_mq_enq_ready)
            ) begin
                stall_REQ = 1'b0;

                REQ_stage_valid = 1'b1;

                first_try_ack = 1'b1;
                second_try_ack = 1'b0;
                data_try_ack = 1'b0;
            end
            else begin
                stall_REQ = 1'b1;

                REQ_stage_valid = 1'b0;

                first_try_ack = 1'b0;
                second_try_ack = 1'b0;
                data_try_ack = 1'b0;
            end
        end

        // otherwise, check second try
        else if (second_try_valid) begin

            // need no propagated stall and dcache req
            if (
                ~(valid_RESP & stall_RESP)
                & dcache_req_ready
            ) begin
                stall_REQ = 1'b0;

                REQ_stage_valid = 1'b1;

                first_try_ack = 1'b0;
                second_try_ack = 1'b1;
                data_try_ack = 1'b0;
            end
            else begin
                stall_REQ = 1'b1;

                REQ_stage_valid = 1'b0;

                first_try_ack = 1'b0;
                second_try_ack = 1'b0;
                data_try_ack = 1'b0;
            end
        end

        // otherwise, check data
        else if (data_try_valid) begin

            // need no propagated stall
            if (
                ~(valid_RESP & stall_RESP)
            ) begin
                stall_REQ = 1'b0;

                REQ_stage_valid = 1'b1;

                first_try_ack = 1'b0;
                second_try_ack = 1'b0;
                data_try_ack = 1'b1;
            end
            else begin
                stall_REQ = 1'b1;

                REQ_stage_valid = 1'b0;

                first_try_ack = 1'b0;
                second_try_ack = 1'b0;
                data_try_ack = 1'b0;
            end
        end
        
        // otherwise, NOP
        else begin
            stall_REQ = 1'b0;

            REQ_stage_valid = 1'b0;

            first_try_ack = 1'b0;
            second_try_ack = 1'b0;
            data_try_ack = 1'b0;
        end
    end

    // dataflow
    always_comb begin
        // REQ_stage_valid // handled ^
        REQ_stage_is_first = first_try_valid;
        REQ_stage_is_second = ~first_try_valid & second_try_valid;
        REQ_stage_is_data = ~first_try_valid & ~second_try_valid & data_try_valid;
        REQ_stage_is_mq = first_try_valid ? first_try_is_mq : second_try_is_mq;
        REQ_stage_misaligned = first_try_valid ? first_try_misaligned : second_try_misaligned;
        REQ_stage_do_restart = ~(first_try_valid | second_try_valid) & data_try_restart;
        REQ_stage_PN = first_try_valid ? {2'b00, first_try_VPN} : second_try_PPN;
        REQ_stage_PO_word = first_try_valid ? first_try_PO_word : second_try_PO_word;
        REQ_stage_byte_mask = first_try_valid ? first_try_byte_mask : second_try_byte_mask;
        REQ_stage_data = data_try_data;
        REQ_stage_cq_index = first_try_valid ? first_try_cq_index : second_try_valid ? second_try_cq_index : data_try_cq_index;
        REQ_stage_mq_index = first_try_valid ? ldu_mq_enq_index : second_try_cq_index;

        ldu_mq_enq_valid = first_try_valid & first_try_is_mq & REQ_stage_valid;

        dtlb_req_valid = first_try_valid & REQ_stage_valid;
        dtlb_req_VPN = first_try_VPN;

        dcache_req_valid = (first_try_valid | second_try_valid) & REQ_stage_valid;
        dcache_req_block_offset = {REQ_stage_PO_word[DCACHE_WORD_ADDR_BANK_BIT-1 : 0], 2'b00};
        // bank will be statically determined for instantiation
        dcache_req_index = REQ_stage_PO_word[DCACHE_INDEX_WIDTH + DCACHE_WORD_ADDR_BANK_BIT - 1 : DCACHE_WORD_ADDR_BANK_BIT];
    end

    // ----------------------------------------------------------------
    // RESP stage logic:

    // stall, control, and ack logic
    always_comb begin

        // check valid RESP
        if (valid_RESP) begin

        end

        // otherwise, NOP
        else begin
            stall_RESP = 1'b0;

            RESP_stage_valid = 1'b0;
        end
    end

endmodule