/*
  Module        : alu_pipeline_iq
  UMV Component : interface
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_IQ_INTERFACE_SV
`define ALU_PIPELINE_IQ_INTERFACE_SV

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Interface --- //
interface alu_pipeline_iq_if (input logic CLK);

  // --- Reset --- //
  logic nRST;

  // --- Inputs --- //
  logic                          valid_in;
  logic [3:0]                    op_in;
  logic                          is_imm_in;
  logic [31:0]                   imm_in;
  logic                          A_unneeded_in;
  logic                          A_forward_in;
  logic [LOG_PRF_BANK_COUNT-1:0] A_bank_in;
  logic                          B_forward_in;
  logic [LOG_PRF_BANK_COUNT-1:0] B_bank_in;
  logic [LOG_PR_COUNT-1:0]       dest_PR_in;
  
  // --- Outputs --- //
  logic                          ready_out;
  
endinterface : alu_pipeline_iq_if

`endif