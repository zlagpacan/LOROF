/*
    Filename: ldu_addr_pipeline.sv
    Author: zlagpacan
    Description: RTL for Load Unit Address Pipeline
    Spec: LOROF/spec/design/ldu_addr_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ldu_addr_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // op issue from IQ
    output logic                            issue_valid,
    output logic [3:0]                      issue_op,
    output logic [11:0]                     issue_imm12,
    output logic                            issue_A_forward,
    output logic                            issue_A_is_zero,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_A_bank,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   issue_cq_index,

    // output feedback to IQ
    output logic                            issue_ready,

    // reg read info and data from PRF
    input logic                                     A_reg_read_ack,
    input logic                                     A_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0]     reg_read_data_by_bank_by_port,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,
    
    // REQ stage info
    output logic    REQ_valid,
    output logic    REQ_misaligned,
    output logic    REQ_cq_index,
    output logic    REQ_PA_word,
    output logic    REQ_byte_mask,

    // REQ stage feedback
    input logic     REQ_ack

);

endmodule