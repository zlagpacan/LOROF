/*
  Module        : alu_imm_pipeline
  UMV Component : Ideal (1 OP per cycle) sequence
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_IDEAL_SEQ_SV
`define ALU_IMM_PIPELINE_IDEAL_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Ideal Sequence --- //
class ideal_sequence extends uvm_sequence;
  `uvm_object_utils(ideal_sequence)
  
  alu_imm_pipeline_sequence_item ideal_tx;
  
  // --- Constructor --- //
  function new(string name= "ideal_sequence");
    super.new(name);
    `uvm_info("IDEAL_SEQ", "Inside Constructor", UVM_HIGH)
  endfunction
  
  // --- Body Task --- //
  task body();
    `uvm_info("IDEAL_SEQ", "Inside body task", UVM_HIGH)
    
    // --- Randomize --- //
    ideal_tx = alu_imm_pipeline_sequence_item::type_id::create("ideal_tx");
    start_item(ideal_tx);
    ideal_tx.randomize() with{
      WB_ready        == 1'b1;
    };
    finish_item(ideal_tx);
        
  endtask : body
  
endclass : ideal_sequence

`endif