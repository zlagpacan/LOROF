/*
  Module        : alu_pipeline
  UMV Component : interface
  Author        : 
*/

`ifndef ALU_PIPELINE_INTERFACE_SV
`define ALU_PIPELINE_INTERFACE_SV

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Interface --- //
interface alu_pipeline_if (input logic CLK);

  // --- Reset --- //
  logic nRST;

  // --- Inputs --- //
  logic                            valid_in;
  logic [3:0]                      op_in;
  logic                            is_imm_in;
  logic [31:0]                     imm_in;
  logic                            A_unneeded_in;
  logic                            A_forward_in;
  logic [LOG_PRF_BANK_COUNT-1:0]   A_bank_in;
  logic                            B_forward_in;
  logic [LOG_PRF_BANK_COUNT-1:0]   B_bank_in;
  logic [LOG_PR_COUNT-1:0]         dest_PR_in;
  logic                            A_reg_read_valid_in;
  logic                            B_reg_read_valid_in;
  logic [LOG_ROB_ENTRIES-1:0]      ROB_index_in;
  logic [PRF_BANK_COUNT-1:0][31:0] reg_read_data_by_bank_in;
  logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank_in;
  
  // --- Outputs --- //
  logic                            ready_out;
  logic                            WB_valid_out;
  logic [31:0]                     WB_data_out;
  logic [LOG_PR_COUNT-1:0]         WB_PR_out;
  logic [LOG_ROB_ENTRIES-1:0]      WB_ROB_index_out;
  
endinterface : alu_pipeline_if

`endif