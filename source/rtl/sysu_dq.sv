/*
    Filename: sysu_dq.sv
    Author: zlagpacan
    Description: RTL for System Unit Dispatch Queue
    Spec: LOROF/spec/design/sysu_dq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module sysu_dq #(
    parameter SYSU_DQ_ENTRIES = 4
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
    input logic [3:0]                       dispatch_attempt_by_way,
    input logic [3:0]                       dispatch_valid_by_way,
    input logic [3:0][3:0]                  dispatch_op_by_way,
    input logic [3:0][11:0]                 dispatch_imm12_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_A_PR_by_way,
    input logic [3:0]                       dispatch_A_ready_by_way,
    input logic [3:0]                       dispatch_A_is_zero_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_B_PR_by_way,
    input logic [3:0]                       dispatch_B_ready_by_way,
    input logic [3:0]                       dispatch_B_is_zero_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_dest_PR_by_way,
    input logic [3:0][LOG_ROB_ENTRIES-1:0]  dispatch_ROB_index_by_way,

    // op dispatch feedback
    output logic [3:0]                      dispatch_ack_by_way,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // op launch to sysu
    output logic                        sysu_launch_valid,
    output logic                        sysu_launch_killed,
    output logic [3:0]                  sysu_launch_op,
    output logic [11:0]                 sysu_launch_imm12,
    output logic [LOG_PR_COUNT-1:0]     sysu_launch_A_PR,
    output logic                        sysu_launch_A_is_zero,
    output logic [LOG_PR_COUNT-1:0]     sysu_launch_B_PR,
    output logic                        sysu_launch_B_is_zero,
    output logic [LOG_PR_COUNT-1:0]     sysu_launch_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  sysu_launch_ROB_index,

    // sysu launch feedback
    input logic                         sysu_launch_ready,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

    // instr support
        // C.EBREAK, ECALL, EBREAK, SRET, WFI, MRET
        // CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI

    // don't need A/B_unneeded from decode as can simply check op bits
        // need A: op[0] | op[1]
        // need B: ~op[2] & (op[0] | op[1])

    // ----------------------------------------------------------------
    // Signals:

    // DQ entries
    logic [SYSU_DQ_ENTRIES-1:0]                         valid_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         killed_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][3:0]                    op_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][11:0]                   imm12_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       A_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         A_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         A_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       B_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         B_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         B_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dest_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]    ROB_index_by_entry;

    // new ready check
    logic [STAMOFU_DQ_ENTRIES-1:0] new_A_ready_by_entry;
    logic [STAMOFU_DQ_ENTRIES-1:0] new_B_ready_by_entry;

    // new kill check
    logic [STAMOFU_DQ_ENTRIES-1:0] new_killed_by_entry;

    // incoming dispatch crossbar by entry
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_attempt_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_valid_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][3:0]                    dispatch_op_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][11:0]                   dispatch_imm12_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dispatch_A_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_A_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_A_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dispatch_B_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_B_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_B_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dispatch_dest_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]    dispatch_ROB_index_by_entry;

    // incoming dispatch req masks for each of 4 possible dispatch ways
    logic [3:0][SYSU_DQ_ENTRIES-1:0] dispatch_open_mask_by_way;
    logic [3:0][SYSU_DQ_ENTRIES-1:0] dispatch_pe_one_hot_by_way;
    logic [3:0][SYSU_DQ_ENTRIES-1:0] dispatch_one_hot_by_way;

    // launching
    logic killed_at_0;
    logic A_ready_at_0;
    logic B_ready_at_0;
    logic launching;

    // ----------------------------------------------------------------
    // Launch Logic:

    assign killed_at_0 = killed_by_entry[0] | new_killed_by_entry[0];

    assign A_ready_at_0 = 

    assign launching = 
        valid_by_entry[0]
        & sysu_launch_ready
        & A_ready_at_0
        & B_ready_at_0;

endmodule