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

    // raw reg read req by read requester
    input logic [13:0]                      raw_req_valid_by_rr,
    input logic [13:0][LOG_PR_COUNT-1:0]    raw_req_PR_by_rr,

    // reg read ack's by read requestor
    output logic [13:0] reg_read_valid_by_rr,

    // reg read data by bank
    output logic [PRF_BANK_COUNT-1:0][31:0] reg_read_data_by_bank_out,

    // writeback data to PRF by writer
    input logic [13:0] WB_valid_array,
    input logic [13:0][31:0] WB_data_array,
    input logic [13:0][]

    // writeback bus
    output logic [PRF_BANK_COUNT-1:0]                                       WB_bus_valid_by_bank,
    output logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]  WB_bus_upper_PR_by_bank
);



endmodule