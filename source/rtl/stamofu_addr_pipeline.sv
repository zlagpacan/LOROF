/*
    Filename: stamofu_addr_pipeline.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Address Pipeline
    Spec: LOROF/spec/design/stamofu_addr_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_addr_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // op issue from IQ
    input logic                                 issue_valid,
    input logic                                 issue_is_store,
    input logic                                 issue_is_amo,
    input logic                                 issue_is_fence,
    input logic [3:0]                           issue_op,
    input logic [11:0]                          issue_imm12,
    input logic                                 issue_A_forward,
    input logic                                 issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank,
    input logic                                 issue_B_forward,
    input logic                                 issue_B_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_B_bank,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    issue_cq_index,

    // output feedback to IQ
    output logic                                issue_ready,

    // reg read info and data from PRF
    input logic                                     A_reg_read_ack,
    input logic                                     A_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0]     reg_read_data_by_bank_by_port,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,

    // REQ stage info

    // REQ stage feedback
    input logic                             REQ_ack
);

endmodule