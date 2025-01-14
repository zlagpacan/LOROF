/*
  Module        : alu
  UMV Component : interface
  Author        : Adam Keith
*/

`ifndef ALU_INTERFACE_SV
`define ALU_INTERFACE_SV

// --- Packages --- //
`include "alu_pkg.svh"
import alu_pkg::*;
    
// --- Includes --- //

// --- Interface --- //
interface alu_if (input logic clk);

  // --- Reset --- //
  logic n_rst;

  // --- Inputs --- //
  logic [3:0]          opcode;
  logic [(DATA_W-1):0] a;
  logic [(DATA_W-1):0] b;
  
  // --- Outputs --- //
  logic [(DATA_W-1):0] out;
  logic                negative;
  logic                overflow;
  logic                zero;
  
endinterface : alu_if

`endif