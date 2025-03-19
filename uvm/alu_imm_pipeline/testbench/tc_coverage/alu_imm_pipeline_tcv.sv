/*
  Module        : alu_imm_pipeline
  UMV Component : Test Case Tracking
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_TCV_SV
`define ALU_IMM_PIPELINE_TCV_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- SVA Checks --- //
module alu_imm_pipeline_tcv (
    input logic                                 CLK,
    input logic                                 nRST,
    input logic                                 issue_valid,
    input logic [3:0]                           issue_op,
    input logic [11:0]                          issue_imm12,
    input logic                                 issue_A_forward,
    input logic                                 issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank,
    input logic [LOG_PR_COUNT-1:0]              issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           issue_ROB_index,
    input logic                                 A_reg_read_ack,
    input logic                                 A_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port,
    input logic [PRF_BANK_COUNT-1:0][31:0]      forward_data_by_bank,
    input logic                                 WB_ready,
    input logic                                 issue_ready,
    input logic                                 WB_valid,
    input logic [31:0]                          WB_data,
    input logic [LOG_PR_COUNT-1:0]              WB_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           WB_ROB_index
);

    // --- Test Case Coverage : tc_reset --- //
    sequence DUT_reset;
      @(posedge CLK) ~(nRST);
    endsequence
        
    property DUT_RESET_EVENT;
      @(posedge CLK) (DUT_reset);
    endproperty
    cov_tc_reset: cover property (DUT_RESET_EVENT);
        
    // --- Test Case Coverage : tc_wb_stall --- //
    sequence WB_stall;
      @(posedge CLK) ~(WB_ready);
    endsequence
        
    property WB_STALL_EVENT;
      @(posedge CLK) disable iff (~nRST)
      (WB_stall);
    endproperty
    cov_tc_wb_stall: cover property (WB_STALL_EVENT);

endmodule

`endif