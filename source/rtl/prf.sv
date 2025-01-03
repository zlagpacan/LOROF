/*
    Filename: prf.sv
    Author: zlagpacan
    Description: RTL for Physical Register File
    Spec: LOROF/spec/design/prf.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf (

    // seq
    input logic CLK,
    input logic nRST,

    // reg read req by read requester
    input logic [PRF_RR_COUNT-1:0]                      reg_read_req_valid_by_rr,
    input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]    reg_read_req_PR_by_rr,

    // reg read info by read requestor
    output logic [PRF_RR_COUNT-1:0]     reg_read_ack_by_rr,
    output logic [PRF_RR_COUNT-1:0]     reg_read_port_by_rr,

    // reg read data by bank
    output logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port,

    // writeback data by write requestor
    input logic [PRF_WR_COUNT-1:0]                          WB_valid_by_wr,
    input logic [PRF_WR_COUNT-1:0][31:0]                    WB_data_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]        WB_PR_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]     WB_ROB_index_by_wr,

    // writeback backpressure by write requestor
    output logic WB_ready_by_wr

    // writeback bus by bank
    output logic [PRF_BANK_COUNT-1:0]                                       WB_bus_valid_by_bank,
    output logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]  WB_bus_upper_PR_by_bank
);

    // ----------------------------------------------------------------
    // Signals:

    // Reg File RAM Array
    logic [PRF_BANK_COUNT-1:0][PR_COUNT/PRF_BANK_COUNT-1:0][31:0] PRF_by_bank;

    // Read Req Signals
    logic [PRF_RR_COUNT-1:0]                unacked_reg_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT]  unacked_reg_read_req_PR_by_rr;
    logic [PRF_RR_COUNT-1:0]                compressed_reg_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0]                compressed_reg_read_req_PR_by_rr;
    logic [PRF_RR_COUNT-1:0]                last_reg_read_mask;

    // Write Req Signals

endmodule