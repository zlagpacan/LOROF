/*
    Filename: bru_pipeline.sv
    Author: zlagpacan
    Description: RTL for Branch Resolution Unit Pipeline
    Spec: LOROF/spec/design/bru_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // BRU op issue to BRU IQ
    input logic                            issue_valid,
    input logic [3:0]                      issue_op,
    input logic [31:0]                     issue_PC,
    input logic [31:0]                     issue_speculated_next_PC,
    input logic [31:0]                     issue_imm,
    input logic                            issue_A_unneeded,
    input logic                            issue_A_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]   issue_A_bank,
    input logic                            issue_B_unneeded,
    input logic                            issue_B_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]   issue_B_bank,
    input logic [LOG_PR_COUNT-1:0]         issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]      issue_ROB_index,

    // output feedback to BRU IQ
    output logic issue_ready,

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

    // writeback backpressure from PRF
    input logic WB_ready,

    // restart info to ROB
    output logic                        restart_info_valid,
    output logic                        restart_info_mispredict,
    output logic [LOG_ROB_ENTRIES-1:0]  restart_info_ROB_index,
    output logic [31:0]                 restart_info_PC,

    // restart req backpressure from ROB
    input logic restart_ready
);



endmodule