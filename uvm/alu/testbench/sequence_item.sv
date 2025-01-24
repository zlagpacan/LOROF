/*
  Module        : alu
  UMV Component : sequence_item
  Author        : Adam Keith
*/

`ifndef ALU_SEQ_ITEM_SV
`define ALU_SEQ_ITEM_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Transaction --- //
class alu_sequence_item extends uvm_sequence_item;
  `uvm_object_utils(alu_sequence_item)

  // --- Randomized Inputs --- //
  randc logic [3:0]  op;
  randc logic [31:0] A;
  randc logic [31:0] B;
  
  // --- Outputs --- //
  logic [31:0] out;
  
  // --- Constructor --- //
  function new(string name = "alu_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_sequence_item

`endif