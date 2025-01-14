/*
  Module        : alu
  UMV Component : sequence_item
  Author        : 
*/

`ifndef ALU_SEQ_ITEM_SV
`define ALU_SEQ_ITEM_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "alu_pkg.svh"
import alu_pkg::*;
    
// --- Includes --- //

// --- Transaction --- //
class alu_sequence_item extends uvm_sequence_item;
  `uvm_object_utils(alu_sequence_item)

  // --- Control Signals --- //
  rand logic n_rst;

  // --- Randomized Inputs --- //
  randc logic [3:0]             opcode;
  randc logic [(DATA_W-1):0] a;
  randc logic [(DATA_W-1):0] b;
  
  // --- Outputs --- //
  logic [(DATA_W-1):0] out;
  
  // --- Constraints --- //

  // NOTE: would have param constraints here in real tb

  // --- Constructor --- //
  function new(string name = "alu_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_sequence_item

`endif