/*
    Filename: bru_iq.sv
    Author: zlagpacan
    Description: RTL for Branch Resolution Unit Issue Queue
    Spec: LOROF/spec/design/bru_iq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_iq (

    // seq
    input logic CLK,
    input logic nRST,

    // BRU op dispatch by entry
    input logic [3:0]                       dispatch_valid_by_entry,
    input logic [3:0][3:0]                  dispatch_op_by_entry,
    input logic [3:0][31:0]                 dispatch_PC_by_entry,
    input logic [3:0][31:0]                 dispatch_speculated_next_PC_by_entry,
    input logic [3:0][31:0]                 dispatch_imm_by_entry,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_A_PR_by_entry,
    input logic [3:0]                       dispatch_A_unneeded_by_entry,
    input logic [3:0]                       dispatch_A_ready_by_entry,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_B_PR_by_entry,
    input logic [3:0]                       dispatch_B_unneeded_by_entry,
    input logic [3:0]                       dispatch_B_ready_by_entry,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_dest_PR_by_entry,
    input logic [3:0][LOG_ROB_ENTRIES-1:0]  dispatch_ROB_index_by_entry,

    // BRU op dispatch feedback by entry
    output logic [3:0] dispatch_open_by_entry,

    // BRU pipeline feedback
    input logic pipeline_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // BRU op issue to BRU pipeline
    output logic                            issue_valid,
    output logic [3:0]                      issue_op,
    output logic [31:0]                     issue_PC,
    output logic [31:0]                     issue_speculated_next_PC,
    output logic [31:0]                     issue_imm,
    output logic                            issue_A_unneeded,
    output logic                            issue_A_forward,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_A_bank,
    output logic                            issue_B_unneeded,
    output logic                            issue_B_forward,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_B_bank,
    output logic [LOG_PR_COUNT-1:0]         issue_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]      issue_ROB_index,

    // reg read req to PRF
    output logic                        PRF_req_A_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_A_PR,
    output logic                        PRF_req_B_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_B_PR
);



endmodule