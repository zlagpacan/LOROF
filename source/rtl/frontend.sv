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
    parameter INIT_PC = 32'h0
) (

    // seq
    input logic CLK,
    input logic nRST,

    // itlb req
    output logic                    itlb_req_valid,
    output logic                    itlb_req_virtual_mode,
    output logic [VPN_WIDTH-1:0]    itlb_req_vpn,
    output logic [ASID_WIDTH-1:0]   itlb_req_ASID,

    // itlb resp
    input logic                     itlb_resp_valid,
    input logic [PPN_WIDTH-1:0]     itlb_resp_ppn,
    input logic                     itlb_resp_page_fault,
    input logic                     itlb_resp_access_fault,

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

    // op dispatch by way:

    // 4-way ROB entry valid
    output logic                                    dispatch_rob_valid,

    // general instr info
    output logic [3:0]                              dispatch_valid_by_way,
    output logic [3:0]                              dispatch_uncompressed_by_way,
    output logic [31:0]                             dispatch_PC_by_way,
    output logic [3:0]                              dispatch_is_rename_by_way,
    output logic [3:0][BTB_PRED_INFO_WIDTH-1:0]     dispatch_pred_info_by_way,
    output logic [3:0][MDPT_INFO_WIDTH-1:0]         dispatch_mdp_info_by_way,
    output logic                                    dispatch_wait_write_buffer,
    output logic [3:0][3:0]                         dispatch_op_by_way,
    output logic [19:0]                             dispatch_imm20_by_way,

    // instr fetch + decode exceptions
    output logic [3:0]                              dispatch_page_fault_by_way,
    output logic [3:0]                              dispatch_access_fault_by_way,
    output logic [3:0]                              dispatch_illegal_instr_by_way,
    output logic [31:0]                             dispatch_excepting_illegal_instr,

    // instr IQ attempts
    output logic [3:0]                              dispatch_attempt_alu_reg_mdu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_alu_imm_ldu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_bru_iq_by_way,
    output logic [3:0]                              dispatch_attempt_stamofu_iq_by_way,
    output logic [3:0]                              dispatch_attempt_sys_iq_by_way,

    // instr FU valids
    output logic [3:0]                              dispatch_valid_alu_reg_by_way,
    output logic [3:0]                              dispatch_valid_mdu_by_way,
    output logic [3:0]                              dispatch_valid_alu_imm_by_way,
    output logic [3:0]                              dispatch_valid_ldu_by_way,
    output logic [3:0]                              dispatch_valid_bru_by_way,
    output logic [3:0]                              dispatch_valid_store_by_way,
    output logic [3:0]                              dispatch_valid_amo_by_way,
    output logic [3:0]                              dispatch_valid_fence_by_way,
    output logic [3:0]                              dispatch_valid_sys_by_way,

    // operand A
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_A_PR_by_way,
    output logic [3:0]                              dispatch_A_ready_by_way,
    output logic [3:0]                              dispatch_A_unneeded_or_is_zero_by_way,
    output logic [3:0]                              dispatch_A_is_ret_ra_by_way,

    // operand B
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_B_PR_by_way,
    output logic [3:0]                              dispatch_B_ready_by_way,
    output logic [3:0]                              dispatch_B_unneeded_or_is_zero_by_way,

    // dest operand
    output logic [3:0][LOG_AR_COUNT-1:0]            dispatch_dest_AR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_old_PR_by_way,
    output logic [3:0][LOG_PR_COUNT-1:0]            dispatch_dest_new_PR_by_way,
    output logic [3:0]                              dispatch_dest_is_zero_by_way,
    output logic [3:0]                              dispatch_dest_is_link_ra,

    // op dispatch feedback:

    // 4-way ROB entry open
    input logic         dispatch_rob_ready,

    // instr IQ acks
    input logic [3:0]   dispatch_ack_alu_reg_mdu_iq_by_way,
    input logic [3:0]   dispatch_ack_alu_imm_ldu_iq_by_way,
    input logic [3:0]   dispatch_ack_bru_iq_by_way,
    input logic [3:0]   dispatch_ack_stamofu_iq_by_way,
    input logic [3:0]   dispatch_ack_sys_iq_by_way,

    // stamofu fence feedback
    input logic stamofu_stall_mem_read,
    input logic stamofu_stall_mem_write,

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
    input logic                         mdpt_update_valid,
    input logic [31:0]                  mdpt_update_start_full_PC,
    input logic [ASID_WIDTH-1:0]        mdpt_update_ASID,
    input logic [MDPT_INFO_WIDTH-1:0]   mdpt_update_mdp_info,

    // restart
    input logic         restart_valid,
    input logic [31:0]  restart_PC,
    input logic [8:0]   restart_ASID,
    input logic [1:0]   restart_exec_mode,
    input logic         restart_virtual_mode,
    input logic         restart_trap_sfence,
    input logic         restart_trap_wfi,
    input logic         restart_trap_sret
);

    // ----------------------------------------------------------------
    // Signals:

    // Fetch Req Stage:

    // state
    logic [31:0]            fetch_PC, next_fetch_PC;
    logic [ASID_WIDTH-1:0]  fetch_ASID, next_fetch_ASID;

    // interruptable access PC
    logic [31:0] access_PC;

    // save restart state
        // keep local copy
            // use version of value when intended to be used
            // limit fanout

    // wait for restart state from decoder

endmodule