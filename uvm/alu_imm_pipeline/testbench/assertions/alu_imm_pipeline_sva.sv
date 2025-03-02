/*
  Module        : alu_imm_pipeline
  UMV Component : System Verilog Assertions
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_SVA_SV
`define ALU_IMM_PIPELINE_SVA_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- SVA Checks --- //
module alu_imm_pipeline_sva (
    input logic                                 CLK,
    input logic                                 nRST
);

   // --- Test Case Coverage --- //
  sequence DUT_reset;
    @(posedge CLK) ~nRST;
  endsequence
  
  property DUT_RESET_EVENT;
    @(posedge CLK) (DUT_reset);
  endproperty
  c_ALURP_0: cover property (DUT_RESET_EVENT);

endmodule

`endif