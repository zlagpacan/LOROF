/*
    Filename: mdu_pipeline.sv
    Author: zlagpacan
    Description: RTL for ALU Reg-Reg + Mul-Div Unit Issue Queue
    Spec: LOROF/spec/design/mdu_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module mdu_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // MDU pipeline issue
    input logic                             mdu_issue_valid,
    input logic [3:0]                       mdu_issue_op,
    input logic                             mdu_issue_A_forward,
    input logic                             mdu_issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    mdu_issue_A_PR,
    input logic                             mdu_issue_B_forward,
    input logic                             mdu_issue_B_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    mdu_issue_B_PR,
    input logic [LOG_PR_COUNT-1:0]          mdu_issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       mdu_issue_ROB_index,

    // MDU pipeline feedback to IQ
    input logic                             mdu_issue_ready,

    // MDU reg read req to PRF
    input logic [LOG_PR_COUNT-1:0]  PRF_mdu_req_A_PR,
    input logic [LOG_PR_COUNT-1:0]  PRF_mdu_req_B_PR,

    // reg read info and data from PRF
    input logic                                     A_reg_read_ack,
    input logic                                     A_reg_read_port,
    input logic                                     B_reg_read_ack,
    input logic                                     B_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0]     reg_read_data_by_bank_by_port,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // writeback feedback from
    input logic WB_ready
);
    // ----------------------------------------------------------------
    // Control Signals:

    logic stall_WB;
    logic stall_OC;

    logic new_div;
    logic result_cache_hit;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                           valid_OC;
    logic [3:0]                     op_OC;
    logic                           A_saved_OC;
    logic                           A_forward_OC;
    logic                           A_is_zero_OC;
    logic [LOG_PR_COUNT-1:0]        A_PR_OC;
    logic                           B_saved_OC;
    logic                           B_forward_OC;
    logic                           B_is_zero_OC;
    logic [LOG_PR_COUNT-1:0]        B_PR_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

    logic [31:0] A_saved_data_OC;
    logic [31:0] B_saved_data_OC;

    logic launch_ready_OC;

    logic                           next_WB_valid;
    logic [3:0]                     next_WB_op;
    logic [31:0]                    next_WB_A;
    logic [31:0]                    next_WB_B;
    logic [LOG_PR_COUNT-1:0]        next_WB_PR;
    logic [LOG_ROB_ENTRIES-1:0]     next_WB_ROB_index;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    logic [3:0]     WB_op;
    logic [31:0]    WB_A;
    logic [31:0]    WB_B;