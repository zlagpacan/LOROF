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
    input logic                             second_try_page_fault,
    input logic                             second_try_access_fault,
    input logic                             second_try_is_mem,
    input logic [PPN_WIDTH-1:0]             second_try_PPN,
    input logic [PO_WIDTH-3:0]              second_try_PO_word,
    input logic [3:0]                       second_try_byte_mask,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    second_try_cq_index,
    input logic [LOG_LDU_MQ_ENTRIES-1:0]    second_try_mq_index,

    // second try feedback
    output logic                            second_try_ack,
    
    // data try
    input logic                             data_try_valid,
    input logic                             data_try_do_mispred,
    input logic [31:0]                      data_try_data,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    data_try_cq_index,

    // data try feedback
    output logic                            data_try_ack,

    // dtlb req
    output logic                            dtlb_req_valid,
    output logic [1:0]                      dtlb_req_exec_mode,
    output logic                            dtlb_req_virtual_mode,
    output logic [ASID_WIDTH-1:0]           dtlb_req_ASID,
    output logic                            dtlb_req_MXR,
    output logic                            dtlb_req_SUM,
    output logic [VPN_WIDTH-1:0]            dtlb_req_VPN,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   dtlb_req_cq_index,
    output logic                            dtlb_req_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   dtlb_req_mq_index,

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
    output logic [LOG_LDU_CQ_ENTRIES-1:0]           dcache_req_cq_index,
    output logic                                    dcache_req_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]           dcache_req_mq_index,

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

    // writeback backpressure from PRF
    input logic                         WB_ready,

    // CAM launch
    output logic                            stamofu_CAM_launch_valid,
    output logic [PA_WIDTH-2-1:0]           stamofu_CAM_launch_PA_word,
    output logic [3:0]                      stamofu_CAM_launch_byte_mask,
    output logic [LOG_ROB_ENTRIES-1:0]      stamofu_CAM_launch_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]      stamofu_CAM_launch_mdp_info,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   stamofu_CAM_launch_cq_index,
    output logic                            stamofu_CAM_launch_is_mq,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   stamofu_CAM_launch_mq_index,

    // central queue info grab
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   ldu_cq_info_grab_cq_index,
    input logic [3:0]                       ldu_cq_info_grab_op,
    input logic [MDPT_INFO_WIDTH-1:0]       ldu_cq_info_grab_mdp_info,
    input logic [LOG_PR_COUNT-1:0]          ldu_cq_info_grab_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       ldu_cq_info_grab_ROB_index,

    // central queue info ret
    output logic                            ldu_cq_info_ret_valid,
    output logic                            ldu_cq_info_ret_WB_sent,
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
    output logic                            ldu_mq_info_ret_valid,
    output logic                            ldu_mq_info_ret_WB_sent,
    output logic [LOG_LDU_MQ_ENTRIES-1:0]   ldu_mq_info_ret_mq_index,
    output logic                            ldu_mq_info_ret_dtlb_hit,
    output logic                            ldu_mq_info_ret_page_fault,
    output logic                            ldu_mq_info_ret_access_fault,
    output logic                            ldu_mq_info_ret_dcache_hit,
    output logic                            ldu_mq_info_ret_is_mem,
    output logic                            ldu_mq_info_ret_aq_blocking,
    output logic [PA_WIDTH-2-1:0]           ldu_mq_info_ret_PA_word,
    output logic [3:0]                      ldu_mq_info_ret_byte_mask,
    output logic [31:0]                     ldu_mq_info_ret_data,

    // misprediction notification to ROB
    output logic                        mispred_notif_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  mispred_notif_ROB_index,

    // misprediction notification backpressure from ROB
    input logic                         mispred_notif_ready,

    // exception to ROB
    output logic                        rob_exception_valid,
    output logic [VA_WIDTH-1:0]         rob_exception_VA,
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

    // ----------------------------------------------------------------
    // Control signals:

    logic stall_RESP;
    logic stall_RET;

    logic RESP_first_cycle;
    logic RET_stage_perform;

    // ----------------------------------------------------------------
    // REQ stage signals:

    logic                           REQ_stage_valid;
    logic                           REQ_stage_is_first;
    logic                           REQ_stage_is_second;
    logic                           REQ_stage_is_data;
    logic                           REQ_stage_is_mq;
    logic                           REQ_stage_misaligned;
    logic                           REQ_stage_given_page_fault;
    logic                           REQ_stage_given_access_fault;
    logic                           REQ_stage_given_is_mem;
    logic                           REQ_stage_do_mispred;
    logic [PPN_WIDTH-1:0]           REQ_stage_given_PPN;
    logic [PO_WIDTH-3:0]            REQ_stage_PO_word;
    logic [3:0]                     REQ_stage_byte_mask;
    logic [31:0]                    REQ_stage_given_data;
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
    logic                           RESP_stage_given_page_fault;
    logic                           RESP_stage_given_access_fault;
    logic                           RESP_stage_given_is_mem;
    logic [PPN_WIDTH-1:0]           RESP_stage_given_PPN;
    logic [PO_WIDTH-3:0]            RESP_stage_PO_word;
    logic [3:0]                     RESP_stage_byte_mask;
    logic [31:0]                    RESP_stage_given_data;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  RESP_stage_cq_index;
    logic [LOG_LDU_MQ_ENTRIES-1:0]  RESP_stage_mq_index;
    
    logic [3:0]                     RESP_stage_op;
    logic [MDPT_INFO_WIDTH-1:0]     RESP_stage_mdp_info;
    logic [LOG_PR_COUNT-1:0]        RESP_stage_dest_PR;
    logic [LOG_ROB_ENTRIES-1:0]     RESP_stage_ROB_index;

    logic                           RESP_stage_mdp_present;

    logic                           RESP_stage_selected_page_fault;
    logic                           RESP_stage_selected_access_fault;
    logic                           RESP_stage_selected_is_mem;
    logic [PPN_WIDTH-1:0]           RESP_stage_selected_PPN;
    logic [PA_WIDTH-3:0]            RESP_stage_selected_PA_word;
    logic [31:0]                    RESP_stage_selected_data;

    logic                           RESP_stage_aq_blocking;

    logic                           RESP_stage_dtlb_hit;
    logic [DCACHE_TAG_WIDTH-1:0]    RESP_stage_dcache_tag;
    logic [1:0]                     RESP_stage_dcache_vtm_by_way;
    logic                           RESP_stage_dcache_vtm;
    logic                           RESP_stage_dcache_hit;

    logic                           RESP_stage_do_WB;
    logic                           RESP_stage_do_CAM;
    logic                           RESP_stage_do_exception;
    logic                           RESP_stage_do_mispred;
    logic                           RESP_stage_do_cq_ret;
    logic                           RESP_stage_do_mq_ret;

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
    // RET stage signals:

    logic                           RET_stage_valid;
    logic                           RET_stage_is_first;
    logic                           RET_stage_is_second;
    logic                           RET_stage_is_data;
    logic                           RET_stage_is_mq;
    logic                           RET_stage_misaligned;
    logic [3:0]                     RET_stage_op;
    logic [MDPT_INFO_WIDTH-1:0]     RET_stage_mdp_info;
    logic [LOG_PR_COUNT-1:0]        RET_stage_dest_PR;
    logic [LOG_ROB_ENTRIES-1:0]     RET_stage_ROB_index;
    logic                           RET_stage_page_fault;
    logic                           RET_stage_access_fault;
    logic                           RET_stage_dtlb_hit;
    logic                           RET_stage_dcache_hit;
    logic                           RET_stage_is_mem;
    logic [PA_WIDTH-3:0]            RET_stage_PA_word;
    logic                           RET_stage_aq_blocking;
    logic [3:0]                     RET_stage_byte_mask;
    logic [31:0]                    RET_stage_data;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  RET_stage_cq_index;
    logic [LOG_LDU_MQ_ENTRIES-1:0]  RET_stage_mq_index;
    
    logic                           RET_stage_do_WB;
    logic                           RET_stage_do_CAM;
    logic                           RET_stage_do_exception;
    logic                           RET_stage_do_mispred;
    logic                           RET_stage_do_cq_ret;
    logic                           RET_stage_do_mq_ret;

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
            // need no propagated stall, dtlb req, dcache req, and ldu mq enq if applicable
        if (
            first_try_valid
            & ~stall_RESP
            & dtlb_req_ready 
            & dcache_req_ready
            & (~first_try_is_mq | ldu_mq_enq_ready)
        ) begin
            REQ_stage_valid = 1'b1;

            first_try_ack = 1'b1;
            second_try_ack = 1'b0;
            data_try_ack = 1'b0;
        end

        // otherwise, check second try
            // need no propagated stall and dcache req
        else if (
            second_try_valid
            & ~stall_RESP
            & dcache_req_ready
        ) begin
            REQ_stage_valid = 1'b1;

            first_try_ack = 1'b0;
            second_try_ack = 1'b1;
            data_try_ack = 1'b0;
        end

        // otherwise, check data
        else if (
            data_try_valid
            & ~stall_RESP
        ) begin
            REQ_stage_valid = 1'b1;

            first_try_ack = 1'b0;
            second_try_ack = 1'b0;
            data_try_ack = 1'b1;
        end

        // otherwise, REQ stage NOP
        else begin
            REQ_stage_valid = 1'b0;

            first_try_ack = 1'b0;
            second_try_ack = 1'b0;
            data_try_ack = 1'b0;
        end
    end

    // dataflow
    always_comb begin
        // REQ_stage_valid // handled ^
        REQ_stage_is_first = first_try_ack;
        REQ_stage_is_second = second_try_ack;
        REQ_stage_is_data = data_try_ack;
        REQ_stage_is_mq = first_try_ack ? first_try_is_mq : second_try_is_mq;
        REQ_stage_misaligned = first_try_ack ? first_try_misaligned : second_try_misaligned;
        REQ_stage_given_page_fault = second_try_page_fault;
        REQ_stage_given_access_fault = second_try_access_fault;
        REQ_stage_given_is_mem = second_try_is_mem;
        REQ_stage_do_mispred = data_try_ack & data_try_do_mispred;
        REQ_stage_given_PPN = first_try_ack ? {2'b00, first_try_VPN} : second_try_PPN;
        REQ_stage_PO_word = first_try_ack ? first_try_PO_word : second_try_PO_word;
        REQ_stage_byte_mask = first_try_ack ? first_try_byte_mask : second_try_byte_mask;
        REQ_stage_given_data = data_try_data;
        REQ_stage_cq_index = first_try_ack ? first_try_cq_index : second_try_ack ? second_try_cq_index : data_try_cq_index;
        REQ_stage_mq_index = first_try_ack ? ldu_mq_enq_index : second_try_mq_index;

        ldu_mq_enq_valid = first_try_ack & first_try_is_mq;

        dtlb_req_valid = first_try_ack;
        dtlb_req_VPN = first_try_VPN;
        dtlb_req_cq_index = first_try_cq_index;
        dtlb_req_is_mq = first_try_is_mq;
        dtlb_req_mq_index = ldu_mq_enq_index;

        dcache_req_valid = (first_try_ack | second_try_ack);
        dcache_req_block_offset = {REQ_stage_PO_word[DCACHE_WORD_ADDR_BANK_BIT-1 : 0], 2'b00};
        // bank will be statically determined for instantiation
        dcache_req_index = REQ_stage_PO_word[DCACHE_INDEX_WIDTH + DCACHE_WORD_ADDR_BANK_BIT + 1 - 1 : DCACHE_WORD_ADDR_BANK_BIT + 1];
            // doesn't include bank bit
        dcache_req_cq_index = first_try_ack ? first_try_cq_index : second_try_cq_index;
        dcache_req_is_mq = first_try_ack ? first_try_is_mq : second_try_is_mq;
        dcache_req_mq_index = first_try_ack ? ldu_mq_enq_index : second_try_mq_index;
    end

    // ----------------------------------------------------------------
    // RESP stage logic:

    // REQ/RESP stage FF output
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            RESP_stage_valid <= '0;
            RESP_stage_is_first <= '0;
            RESP_stage_is_second <= '0;
            RESP_stage_is_data <= '0;
            RESP_stage_is_mq <= '0;
            RESP_stage_misaligned <= '0;
            RESP_stage_given_page_fault <= '0;
            RESP_stage_given_access_fault <= '0;
            RESP_stage_given_is_mem <= '0;
            RESP_stage_do_mispred <= '0;
            RESP_stage_given_PPN <= '0;
            RESP_stage_PO_word <= '0;
            RESP_stage_byte_mask <= '0;
            RESP_stage_given_data <= '0;
            RESP_stage_cq_index <= '0;
            RESP_stage_mq_index <= '0;
        end
        else if (~stall_RESP) begin
            RESP_stage_valid <= REQ_stage_valid;
            RESP_stage_is_first <= REQ_stage_is_first;
            RESP_stage_is_second <= REQ_stage_is_second;
            RESP_stage_is_data <= REQ_stage_is_data;
            RESP_stage_is_mq <= REQ_stage_is_mq;
            RESP_stage_misaligned <= REQ_stage_misaligned;
            RESP_stage_given_page_fault <= REQ_stage_given_page_fault;
            RESP_stage_given_access_fault <= REQ_stage_given_access_fault;
            RESP_stage_given_is_mem <= REQ_stage_given_is_mem;
            RESP_stage_do_mispred <= REQ_stage_do_mispred;
            RESP_stage_given_PPN <= REQ_stage_given_PPN;
            RESP_stage_PO_word <= REQ_stage_PO_word;
            RESP_stage_byte_mask <= REQ_stage_byte_mask;
            RESP_stage_given_data <= REQ_stage_given_data;
            RESP_stage_cq_index <= REQ_stage_cq_index;
            RESP_stage_mq_index <= REQ_stage_mq_index;
        end
    end

    // stall, control, and ack logic
    always_comb begin

        // check valid RESP
        if (RESP_stage_valid) begin

            // check RESP good to pass through
                // need no propagated stall
            if (~stall_RET) begin
                stall_RESP = 1'b0;
            end

            // otherwise, stall
            else begin
                stall_RESP = 1'b1;
            end
        end

        // otherwise, NOP
        else begin
            stall_RESP = 1'b0;
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            RESP_first_cycle <= 1'b1;
        end
        else begin
            RESP_first_cycle <= ~stall_RET;
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            saved_dtlb_resp_hit <= 1'b0;
            saved_dtlb_resp_PPN <= 22'h0;
            saved_dtlb_resp_is_mem <= 1'b0;
            saved_dtlb_resp_page_fault <= 1'b0;
            saved_dtlb_resp_access_fault <= 1'b0;

            saved_dcache_resp_valid_by_way <= 2'b00;
            saved_dcache_resp_tag_by_way <= '0;
            saved_dcache_resp_data_by_way <= {32'h0, 32'h0};
        end
        else if (RESP_first_cycle) begin
            saved_dtlb_resp_hit <= dtlb_resp_hit;
            saved_dtlb_resp_PPN <= dtlb_resp_PPN;
            saved_dtlb_resp_is_mem <= dtlb_resp_is_mem;
            saved_dtlb_resp_page_fault <= dtlb_resp_page_fault;
            saved_dtlb_resp_access_fault <= dtlb_resp_access_fault;

            saved_dcache_resp_valid_by_way <= dcache_resp_valid_by_way;
            saved_dcache_resp_tag_by_way <= dcache_resp_tag_by_way;
            saved_dcache_resp_data_by_way <= dcache_resp_data_by_way;
        end
    end

    // dataflow
    always_comb begin

        // central queue info grab
        ldu_cq_info_grab_cq_index = RESP_stage_cq_index;
        RESP_stage_op = ldu_cq_info_grab_op;
        RESP_stage_mdp_info = ldu_cq_info_grab_mdp_info;
        RESP_stage_dest_PR = ldu_cq_info_grab_dest_PR;
        RESP_stage_ROB_index = ldu_cq_info_grab_ROB_index;
        
        RESP_stage_mdp_present = ldu_cq_info_grab_mdp_info[7:6] != 2'b00;

        // choose saved vs current resp's
        if (RESP_first_cycle) begin
            selected_dtlb_resp_hit = dtlb_resp_hit;
            selected_dtlb_resp_PPN = dtlb_resp_PPN;
            selected_dtlb_resp_is_mem = dtlb_resp_is_mem;
            selected_dtlb_resp_page_fault = dtlb_resp_page_fault;
            selected_dtlb_resp_access_fault = dtlb_resp_access_fault;

            selected_dcache_resp_valid_by_way = dcache_resp_valid_by_way;
            selected_dcache_resp_tag_by_way = dcache_resp_tag_by_way;
            selected_dcache_resp_data_by_way = dcache_resp_data_by_way;
        end
        else begin
            selected_dtlb_resp_hit = saved_dtlb_resp_hit;
            selected_dtlb_resp_PPN = saved_dtlb_resp_PPN;
            selected_dtlb_resp_is_mem = saved_dtlb_resp_is_mem;
            selected_dtlb_resp_page_fault = saved_dtlb_resp_page_fault;
            selected_dtlb_resp_access_fault = saved_dtlb_resp_access_fault;

            selected_dcache_resp_valid_by_way = saved_dcache_resp_valid_by_way;
            selected_dcache_resp_tag_by_way = saved_dcache_resp_tag_by_way;
            selected_dcache_resp_data_by_way = saved_dcache_resp_data_by_way;
        end

        // select dtlb info
        RESP_stage_selected_page_fault = RESP_stage_is_first ? selected_dtlb_resp_page_fault : RESP_stage_given_page_fault;
        RESP_stage_selected_access_fault = RESP_stage_is_first ? selected_dtlb_resp_access_fault : RESP_stage_given_access_fault;
        RESP_stage_selected_is_mem = RESP_stage_is_first ? selected_dtlb_resp_is_mem : RESP_stage_given_is_mem;
        RESP_stage_selected_PPN = (RESP_stage_is_first & ~RESP_stage_selected_page_fault & ~RESP_stage_selected_access_fault) ? selected_dtlb_resp_PPN : RESP_stage_given_PPN;
            // first try exceptions need VPN in PPN slot 
        RESP_stage_selected_PA_word = {RESP_stage_selected_PPN, RESP_stage_PO_word};

        // check for blocking acquire
        RESP_stage_aq_blocking = RESP_stage_selected_is_mem ?
            stamofu_aq_mem_aq_active & 
                (RESP_stage_ROB_index - rob_abs_head_index) 
                > (stamofu_aq_mem_aq_oldest_abs_ROB_index - rob_abs_head_index)
            : stamofu_aq_io_aq_active & 
                (RESP_stage_ROB_index - rob_abs_head_index) 
                > (stamofu_aq_io_aq_oldest_abs_ROB_index - rob_abs_head_index);

        // dtlb and dcache hit and miss logic
        RESP_stage_dtlb_hit = RESP_stage_is_second | RESP_stage_is_first & selected_dtlb_resp_hit;
        RESP_stage_dcache_tag = RESP_stage_selected_PA_word[PA_WIDTH-3:PA_WIDTH-DCACHE_TAG_WIDTH-2];
        RESP_stage_dcache_vtm_by_way[0] = selected_dcache_resp_valid_by_way[0] & (selected_dcache_resp_tag_by_way[0] == RESP_stage_dcache_tag);
        RESP_stage_dcache_vtm_by_way[1] = selected_dcache_resp_valid_by_way[1] & (selected_dcache_resp_tag_by_way[1] == RESP_stage_dcache_tag);
        RESP_stage_dcache_vtm = |RESP_stage_dcache_vtm_by_way;
        RESP_stage_dcache_hit = 
            RESP_stage_dtlb_hit 
            & ~RESP_stage_aq_blocking // don't tell that hit yet
            & ~(RESP_stage_selected_page_fault | RESP_stage_selected_access_fault)
            & RESP_stage_dcache_vtm;

        dcache_resp_hit_valid = 
            RESP_stage_valid
            & RESP_first_cycle
            & RESP_stage_dtlb_hit
            // & ~RESP_stage_aq_blocking // still want to prefetch
            & ~(RESP_stage_selected_page_fault | RESP_stage_selected_access_fault)
            & RESP_stage_dcache_vtm;
        dcache_resp_hit_way = RESP_stage_dcache_vtm_by_way[1];
        dcache_resp_miss_valid = 
            RESP_stage_valid
            & RESP_first_cycle
            & RESP_stage_dtlb_hit
            // & ~RESP_stage_aq_blocking // still want to prefetch
            & ~(RESP_stage_selected_page_fault | RESP_stage_selected_access_fault)
            & ~RESP_stage_dcache_vtm;
        dcache_resp_miss_tag = RESP_stage_dcache_tag;

        RESP_stage_selected_data = 
            RESP_stage_is_data ? RESP_stage_given_data 
            : RESP_stage_dcache_vtm_by_way[1] ? selected_dcache_resp_data_by_way[1] : selected_dcache_resp_data_by_way[0];

        // action determination
        RESP_stage_do_WB = 
            RESP_stage_is_data 
            | (
                RESP_stage_dtlb_hit
                & ~RESP_stage_aq_blocking 
                & RESP_stage_dcache_vtm 
                & ~RESP_stage_mdp_present 
                & ~RESP_stage_misaligned);
        RESP_stage_do_CAM = 
            RESP_stage_dtlb_hit 
            & ~RESP_stage_aq_blocking
            & ~(RESP_stage_selected_page_fault | RESP_stage_selected_access_fault);
        RESP_stage_do_exception = 
            RESP_stage_dtlb_hit 
            & (RESP_stage_selected_page_fault | RESP_stage_selected_access_fault);
        // RESP_stage_do_mispred handled in FF logic ^
        RESP_stage_do_cq_ret = ~RESP_stage_is_mq & ~RESP_stage_is_data;
        RESP_stage_do_mq_ret = RESP_stage_is_mq & ~RESP_stage_is_data;
    end

    // ----------------------------------------------------------------
    // RESP stage logic:

    // REQ/RESP stage FF output
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            RET_stage_valid <= '0;
            RET_stage_is_first <= '0;
            RET_stage_is_second <= '0;
            RET_stage_is_data <= '0;
            RET_stage_is_mq <= '0;
            RET_stage_misaligned <= '0;
            RET_stage_op <= '0;
            RET_stage_mdp_info <= '0;
            RET_stage_dest_PR <= '0;
            RET_stage_ROB_index <= '0;
            RET_stage_page_fault <= '0;
            RET_stage_access_fault <= '0;
            RET_stage_dtlb_hit <= '0;
            RET_stage_dcache_hit <= '0;
            RET_stage_is_mem <= '0;
            RET_stage_PA_word <= '0;
            RET_stage_aq_blocking <= '0;
            RET_stage_byte_mask <= '0;
            RET_stage_data <= '0;
            RET_stage_cq_index <= '0;
            RET_stage_mq_index <= '0;
            RET_stage_do_WB <= '0;
            RET_stage_do_CAM <= '0;
            RET_stage_do_exception <= '0;
            RET_stage_do_mispred <= '0;
            RET_stage_do_cq_ret <= '0;
            RET_stage_do_mq_ret <= '0;
        end
        else if (~stall_RESP) begin
            RET_stage_valid <= RESP_stage_valid;
            RET_stage_is_first <= RESP_stage_is_first;
            RET_stage_is_second <= RESP_stage_is_second;
            RET_stage_is_data <= RESP_stage_is_data;
            RET_stage_is_mq <= RESP_stage_is_mq;
            RET_stage_misaligned <= RESP_stage_misaligned;
            RET_stage_op <= RESP_stage_op;
            RET_stage_mdp_info <= RESP_stage_mdp_info;
            RET_stage_dest_PR <= RESP_stage_dest_PR;
            RET_stage_ROB_index <= RESP_stage_ROB_index;
            RET_stage_page_fault <= RESP_stage_selected_page_fault;
            RET_stage_access_fault <= RESP_stage_selected_access_fault;
            RET_stage_dtlb_hit <= RESP_stage_dtlb_hit;
            RET_stage_dcache_hit <= RESP_stage_dcache_hit;
            RET_stage_is_mem <= RESP_stage_selected_is_mem;
            RET_stage_PA_word <= RESP_stage_selected_PA_word;
            RET_stage_aq_blocking <= RESP_stage_aq_blocking;
            RET_stage_byte_mask <= RESP_stage_byte_mask;
            RET_stage_data <= RESP_stage_selected_data;
            RET_stage_cq_index <= RESP_stage_cq_index;
            RET_stage_mq_index <= RESP_stage_mq_index;
            RET_stage_do_WB <= RESP_stage_do_WB;
            RET_stage_do_CAM <= RESP_stage_do_CAM;
            RET_stage_do_exception <= RESP_stage_do_exception;
            RET_stage_do_mispred <= RESP_stage_do_mispred;
            RET_stage_do_cq_ret <= RESP_stage_do_cq_ret;
            RET_stage_do_mq_ret <= RESP_stage_do_mq_ret;
        end
    end

    // stall and control logic
    always_comb begin

        // check valid RET
        if (RET_stage_valid) begin

            // check any conditions for stall
                // do's not satisfied
            if (
                RET_stage_do_WB & ~WB_ready
                // CAM always ready
                | RET_stage_do_exception & ~rob_exception_ready
                | RET_stage_do_mispred & ~mispred_notif_ready
                // cq ret always ready
                // mq ret always ready
            ) begin
                RET_stage_perform = 1'b0;
                stall_RET = 1'b1;
            end

            // otherwise, good to perform RET
            else begin
                RET_stage_perform = 1'b1;
                stall_RET = 1'b0;
            end
        end

        // otherwise, NOP
        else begin
            RET_stage_perform = 1'b0;
            stall_RET = 1'b0;
        end
    end

    // dataflow
    always_comb begin

        // WB
        WB_valid = RET_stage_do_WB & RET_stage_perform;
        WB_PR = RET_stage_dest_PR;
        WB_ROB_index = RET_stage_ROB_index;

        // WB data
            // need to mux around return data bits for non-word-alignment
        if (RET_stage_is_data) begin
            // take data as-is
                // muxing around was already performed as needed
            WB_data = RET_stage_data;
        end
        else begin
            // op-wise and byte-mask-wise muxing
            // can assume not misaligned at this point
            // sign extension:
                // signed & msb -> ~op[2] & msb

            // LW
            if (RET_stage_op[1]) begin

                // guaranteed 4'b1111 -> bits [31:0]
                WB_data = RET_stage_data;
            end

            // LH, LHU
            else if (RET_stage_op[0]) begin

                // 4'b1100 -> bits [31:16]
                if (~RET_stage_byte_mask[1]) begin
                    WB_data = {{16{~RET_stage_op[2] & RET_stage_data[31]}}, RET_stage_data[31:16]};
                end

                // 4'b0110 -> bits [23:8]
                else if (~RET_stage_byte_mask[0]) begin
                    WB_data = {{16{~RET_stage_op[2] & RET_stage_data[23]}}, RET_stage_data[23:8]};
                end

                // 4'b0011 -> bits [15:0]
                else begin
                    WB_data = {{16{~RET_stage_op[2] & RET_stage_data[15]}}, RET_stage_data[15:0]};
                end
            end

            // LB, LBU
            else begin

                // 4'b1000 -> bits [31:24]
                if (RET_stage_byte_mask[3]) begin
                    WB_data = {{24{~RET_stage_op[2] & RET_stage_data[31]}}, RET_stage_data[31:24]};
                end

                // 4'b0100 -> bits [23:16]
                else if (RET_stage_byte_mask[2]) begin
                    WB_data = {{24{~RET_stage_op[2] & RET_stage_data[23]}}, RET_stage_data[23:16]};
                end

                // 4'b0010 -> bits [15:8]
                else if (RET_stage_byte_mask[1]) begin
                    WB_data = {{24{~RET_stage_op[2] & RET_stage_data[15]}}, RET_stage_data[15:8]};
                end

                // 4'b0001 -> bits [15:8]
                else begin
                    WB_data = {{24{~RET_stage_op[2] & RET_stage_data[7]}}, RET_stage_data[7:0]};
                end
            end
        end

        // CAM
        stamofu_CAM_launch_valid = RET_stage_do_CAM & RET_stage_perform;
        stamofu_CAM_launch_PA_word = RET_stage_PA_word;
        stamofu_CAM_launch_byte_mask = RET_stage_byte_mask;
        stamofu_CAM_launch_ROB_index = RET_stage_ROB_index;
        stamofu_CAM_launch_mdp_info = RET_stage_mdp_info;
        stamofu_CAM_launch_cq_index = RET_stage_cq_index;
        stamofu_CAM_launch_is_mq = RET_stage_is_mq;
        stamofu_CAM_launch_mq_index = RET_stage_mq_index;

        // exception
        rob_exception_valid = RET_stage_do_exception & RET_stage_perform;
        rob_exception_page_fault = RET_stage_page_fault;
        rob_exception_access_fault = RET_stage_access_fault;
        rob_exception_ROB_index = RET_stage_ROB_index;

        rob_exception_VA[31:2] = RET_stage_PA_word[29:0];
        casez (RET_stage_byte_mask)
            4'b0000:    rob_exception_VA[1:0] = 2'h0;
            4'b???1:    rob_exception_VA[1:0] = 2'h0;
            4'b??10:    rob_exception_VA[1:0] = 2'h1;
            4'b?100:    rob_exception_VA[1:0] = 2'h2;
            4'b1000:    rob_exception_VA[1:0] = 2'h3;
        endcase

        // mispred
        mispred_notif_valid = RET_stage_do_mispred & RET_stage_perform;
        mispred_notif_ROB_index = RET_stage_ROB_index;

        // cq ret
        ldu_cq_info_ret_valid = RET_stage_do_cq_ret & RET_stage_perform;
        ldu_cq_info_ret_WB_sent = RET_stage_do_WB;
        ldu_cq_info_ret_cq_index = RET_stage_cq_index;
        ldu_cq_info_ret_misaligned = RET_stage_misaligned;
        ldu_cq_info_ret_dtlb_hit = RET_stage_dtlb_hit;
        ldu_cq_info_ret_page_fault = RET_stage_page_fault;
        ldu_cq_info_ret_access_fault = RET_stage_access_fault;
        ldu_cq_info_ret_dcache_hit = RET_stage_dcache_hit;
        ldu_cq_info_ret_is_mem = RET_stage_is_mem;
        ldu_cq_info_ret_aq_blocking = RET_stage_aq_blocking;
        ldu_cq_info_ret_PA_word = RET_stage_PA_word;
        ldu_cq_info_ret_byte_mask = RET_stage_byte_mask;
        ldu_cq_info_ret_data = RET_stage_data;

        // mq ret
        ldu_mq_info_ret_valid = RET_stage_do_mq_ret & RET_stage_perform;
        ldu_mq_info_ret_WB_sent = RET_stage_do_WB;
        ldu_mq_info_ret_mq_index = RET_stage_mq_index;
        ldu_mq_info_ret_dtlb_hit = RET_stage_dtlb_hit;
        ldu_mq_info_ret_page_fault = RET_stage_page_fault;
        ldu_mq_info_ret_access_fault = RET_stage_access_fault;
        ldu_mq_info_ret_dcache_hit = RET_stage_dcache_hit;
        ldu_mq_info_ret_is_mem = RET_stage_is_mem;
        ldu_mq_info_ret_aq_blocking = RET_stage_aq_blocking;
        ldu_mq_info_ret_PA_word = RET_stage_PA_word;
        ldu_mq_info_ret_byte_mask = RET_stage_byte_mask;
        ldu_mq_info_ret_data = RET_stage_data;
    end

endmodule