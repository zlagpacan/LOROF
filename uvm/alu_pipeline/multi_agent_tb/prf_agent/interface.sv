/*
  Module        : alu_pipeline_prf
  UMV Component : interface
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_PRF_INTERFACE_SV
`define ALU_PIPELINE_PRF_INTERFACE_SV

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Interface --- //
interface alu_pipeline_prf_if (input logic CLK);

  // --- Inputs --- //
  logic                            A_reg_read_valid_in;
  logic                            B_reg_read_valid_in;
  logic [LOG_ROB_ENTRIES-1:0]      ROB_index_in;
  logic [PRF_BANK_COUNT-1:0][31:0] reg_read_data_by_bank_in;
  logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank_in;
  
  // --- Outputs --- //
  logic                            WB_valid_out;
  logic [31:0]                     WB_data_out;
  logic [LOG_PR_COUNT-1:0]         WB_PR_out;
  logic [LOG_ROB_ENTRIES-1:0]      WB_ROB_index_out;
  
endinterface : alu_pipeline_prf_if

`endif