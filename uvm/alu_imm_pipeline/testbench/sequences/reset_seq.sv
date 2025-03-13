/*
  Module        : alu_reg_pipeline
  UMV Component : reset sequence
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_RST_SEQ_SV
`define ALU_IMM_PIPELINE_RST_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Reset Sequence --- //
class reset_sequence extends uvm_sequence;
  `uvm_object_utils(reset_sequence)
  
  alu_imm_pipeline_sequence_item reset_pkt;
  
  // --- Constructor --- //
  function new(string name= "reset_sequence");
    super.new(name);
    `uvm_info("RESET_SEQ", "Inside Constructor", UVM_HIGH)
  endfunction
  
  // --- Body Task --- //
  task body();
    `uvm_info("RESET_SEQ", "Inside body task", UVM_HIGH)
    
    // --- Randomize With Reset --- //
    reset_pkt = alu_imm_pipeline_sequence_item::type_id::create("reset_pkt");
    start_item(reset_pkt);
    reset_pkt.randomize() with {nRST==0;};
    finish_item(reset_pkt);
        
  endtask : body
  
endclass : reset_sequence
