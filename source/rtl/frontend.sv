/*
    Filename: frontend.sv
    Author: zlagpacan
    Description: RTL for Front End
    Spec: LOROF/spec/design/frontend.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module frontend #(
    parameter INIT_PC = 32'h80000000  
) (

    // seq
    input logic CLK,
    input logic nRST,

    // itlb req
    output logic                    itlb_req_valid,
    output logic [VPN_WIDTH-1:0]    itlb_vpn,
    output logic [ASID_WIDTH-1:0]   itlb_ASID,

    // itlb resp
    input logic                     itlb_resp_valid,
    input logic [PPN_WIDTH-1:0]     itlb_ppn,

    // icache req
    output logic                                        icache_req_valid,
    output logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]  icache_req_block_offset,
    output logic [ICACHE_INDEX_WIDTH-1:0]               icache_req_index,

    // icache resp
    input logic                                 icache_resp_valid_way0,
    input logic [ICACHE_TAG_WIDTH-1:0]          icache_resp_tag_way0,
    input logic [ICACHE_FETCH_WIDTH-1:0][7:0]   icache_resp_instr_16B_way0,
    input logic                                 icache_resp_valid_way1,
    input logic [ICACHE_TAG_WIDTH-1:0]          icache_resp_tag_way1,
    input logic [ICACHE_FETCH_WIDTH-1:0][7:0]   icache_resp_instr_16B_way1,

    // icache resp feedback
    output logic                            icache_resp_notif_valid,
    output logic                            icache_resp_notif_miss,
    output logic [ICACHE_ASSOC-1:0]         icache_resp_notif_way,
    output logic [ICACHE_TAG_WIDTH-1:0]     icache_resp_notif_tag,

    // op dispatch by way
    output logic                                    dispatch_rob_valid,

    output logic [3:0]                              dispatch_attempt_alu_reg_mdu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_alu_imm_ldu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_bru_iq_by_way,
    output logic [3:0]                              dispatch_attempt_stamofu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_sys_iq_by_way,

    output logic [3:0]                              dispatch_valid_alu_reg_by_way,
    output logic [3:0]                              dispatch_valid_mdu_by_way,
    output logic [3:0]                              dispatch_valid_alu_imm_by_way,
    output logic [3:0]                              dispatch_valid_ldu_by_way,
    output logic [3:0]                              dispatch_valid_bru_by_way,
    output logic [3:0]                              dispatch_valid_store_by_way,
    output logic [3:0]                              dispatch_valid_amo_by_way,
    output logic [3:0]                              dispatch_valid_fence_by_way,
    output logic [3:0]                              dispatch_valid_sys_by_way,
    output logic [3:0]                              dispatch_valid_illegal_op_by_way,

    output logic [3:0][3:0]                         dispatch_op_by_way,
    output logic [3:0]                              dispatch_is_reg_write_by_way,
    output logic [3:0][BTB_PRED_INFO_WIDTH-1:0]     dispatch_pred_info_by_way,
    output logic [3:0][MDPT_INFO_WIDTH-1:0]         dispatch_mdp_info_by_way,
    output logic                                    dispatch_wait_write_buffer,

    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_A_PR_by_way,
    output logic [3:0]                              dispatch_A_ready_by_way,
    output logic [3:0]                              dispatch_A_unneeded_or_is_zero_by_way,
    output logic [3:0]                              dispatch_A_is_ret_ra_by_way,

    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_B_PR_by_way,
    output logic [3:0]                              dispatch_B_ready_by_way,
    output logic [3:0]                              dispatch_B_unneeded_or_is_zero_by_way,

    output logic [3:0][LOG_AR_COUNT-1:0]            dispatch_dest_AR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_old_PR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_new_PR_by_way,

    output logic [19:0]                             dispatch_imm20_by_way,

    // op dispatch feedback
    input logic         dispatch_rob_ack,

    input logic [3:0]   dispatch_attempt_alu_reg_mdu_iq_by_way,
    input logic [3:0]   dispatch_attempt_alu_imm_ldu_iq_by_way,
    input logic [3:0]   dispatch_attempt_bru_iq_by_way,
    input logic [3:0]   dispatch_attempt_stamofu_iq_by_way,
    input logic [3:0]   dispatch_attempt_sys_iq_by_way,

    // update
    input logic                             update_valid,
    input logic [31:0]                      update_start_full_PC,
    input logic [ASID_WIDTH-1:0]            update_ASID,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   update_pred_info,
    input logic                             update_pred_lru,
    input logic [31:0]                      update_target_full_PC,

    // update feedback
    output logic update_ready,

    // mdpt update
    input logic                         dep_update_valid,
    input logic [31:0]                  dep_update_start_full_PC,
    input logic [ASID_WIDTH-1:0]        dep_update_ASID,
    input logic [MDPT_INFO_WIDTH-1:0]   dep_update_mdp_info

    // restart
    input logic restart_valid,
    input logic [31:0] restart_PC,

    // mode
    input logic mode_virtual
);

    // ----------------------------------------------------------------
    // Signals:

    // Fetch Req Stage:

    // state
    logic [31:0]            fetch_PC;
    logic [ASID_WIDTH-1:0]  fetch_ASID;

    // 

endmodule