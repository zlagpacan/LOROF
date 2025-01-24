/*
  Module        : alu
  UMV Component : interface
  Author        : Adam Keith
*/

`ifndef ALU_INTERFACE_SV
`define ALU_INTERFACE_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Interface --- //
interface alu_if (input logic CLK);

  // --- Inputs --- //
  logic [3:0]  op;
  logic [31:0] A;
  logic [31:0] B;
  
  // --- Outputs --- //
  logic [31:0] out;
  
endinterface : alu_if

`endif