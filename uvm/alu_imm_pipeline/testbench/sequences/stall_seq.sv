/*
  Module        : alu_imm_pipeline
  UMV Component : Stall sequences
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_STALL_SEQ_SV
`define ALU_IMM_PIPELINE_STALL_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- WB Stall Sequence --- //
class wb_stall_sequence extends uvm_sequence;
  `uvm_object_utils(wb_stall_sequence)
  
  alu_imm_pipeline_sequence_item wb_stall_tx;
  
  // --- Constructor --- //
  function new(string name= "wb_stall_sequence");
    super.new(name);
    `uvm_info("WB_STALL_SEQ", "Inside Constructor", UVM_HIGH)
  endfunction
  
  // --- Body Task --- //
  task body();
    `uvm_info("WB_STALL_SEQ", "Inside body task", UVM_HIGH)
    
    // --- Randomize --- //
    wb_stall_tx = alu_imm_pipeline_sequence_item::type_id::create("wb_stall_tx");
    start_item(wb_stall_tx);
    wb_stall_tx.randomize() with {
        WB_ready dist {0:/30, 1:/70};
    };
    finish_item(wb_stall_tx);
        
  endtask : body
  
endclass : wb_stall_sequence

`endif