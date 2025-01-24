/*
  Module        : alu
  UMV Component : alu sequence
  Author        : Adam Keith
*/

`ifndef ALU_SEQ_SV
`define ALU_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- ALU Sequence --- //
class alu_sequence extends uvm_sequence;
  `uvm_object_utils(alu_sequence)
  
  alu_sequence_item alu_pkt;
  
  // --- Constructor --- //
  function new(string name= "alu_sequence");
    super.new(name);
    `uvm_info("ALU_SEQ", "Inside Constructor", UVM_HIGH)
  endfunction
  
  // --- Body Task --- //
  task body();
    `uvm_info("ALU_SEQ", "Inside body task", UVM_HIGH)
    
    // --- Randomize With Reset --- //
    alu_pkt = alu_sequence_item::type_id::create("alu_pkt");
    start_item(alu_pkt);
    alu_pkt.randomize();
    finish_item(alu_pkt);
        
  endtask : body
  
endclass : alu_sequence

`endif