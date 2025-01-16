/*
  Module        : alu
  UMV Component : interface
  Author        : 
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
  logic [(DATA_W-1):0] a;
  logic [(DATA_W-1):0] b;
  logic [1:0]          opcode;
  
  // --- Outputs --- //
  logic                negative;
  logic [(DATA_W-1):0] out;
  logic                overflow;
  logic                zero;
  
endinterface : alu_if

`endif