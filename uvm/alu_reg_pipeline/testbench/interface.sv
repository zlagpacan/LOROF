/*
  Module        : alu_reg_pipeline
  UMV Component : interface
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_INTERFACE_SV
`define ALU_REG_PIPELINE_INTERFACE_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Interface --- //
interface alu_reg_pipeline_if (input logic CLK);

  // --- Reset --- //
  logic nRST;

  // --- Inputs --- //
  logic                                 issue_valid;
  logic [3:0]                           issue_op;
  logic                                 issue_A_forward;
  logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank;
  logic                                 issue_A_is_zero,
  logic                                 issue_B_forward;
  logic [LOG_PRF_BANK_COUNT-1:0]        issue_B_bank;
  logic [LOG_PR_COUNT-1:0]              issue_dest_PR;
  logic [LOG_ROB_ENTRIES-1:0]           issue_ROB_index;
  logic                                 A_reg_read_ack;
  logic                                 A_reg_read_port;
  logic                                 B_reg_read_ack;
  logic                                 B_reg_read_port;
  logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port;
  logic [PRF_BANK_COUNT-1:0][31:0]      forward_data_by_bank;
  logic                                 WB_ready;
  
  // --- Outputs --- //
  logic                                 issue_ready;
  logic                                 WB_valid;
  logic [31:0]                          WB_data;
  logic [LOG_PR_COUNT-1:0]              WB_PR;
  logic [LOG_ROB_ENTRIES-1:0]           WB_ROB_index;

endinterface : alu_reg_pipeline_if

`endif