/*
  Module        : alu_pipeline
  UMV Component : scoreboard
  Author        : 
*/

`ifndef ALU_PIPELINE_SCOREBOARD_SV
`define ALU_PIPELINE_SCOREBOARD_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Scoreboard --- //
class alu_pipeline_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(alu_pipeline_scoreboard)

  // --- Scoreboard Components --- //
  uvm_analysis_imp #(alu_pipeline_sequence_item, alu_pipeline_scoreboard) scoreboard_port;
  alu_pipeline_sequence_item transactions[$];

  // --- Constructor --- //
  function new(string name = "alu_pipeline_scoreboard", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SCB_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new

  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SCB_CLASS", "Build Phase", UVM_HIGH)
   
    // --- Scoreboard Port --- //
    scoreboard_port = new("scoreboard_port", this);
    
  endfunction : build_phase

  // --- Write Transaction --- //
  function void write(alu_pipeline_sequence_item item);
    transactions.push_back(item);
  endfunction : write 

  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCB_CLASS", "Run Phase", UVM_HIGH)
   
    // --- Transaction Stack --- //
    forever begin
      alu_pipeline_sequence_item curr_tx;
      wait((transactions.size() != 0));
      curr_tx = transactions.pop_front();
      compare(curr_tx);
    end
    
  endtask : run_phase

  // --- Compare --- //
  task compare(alu_pipeline_sequence_item curr_tx);

  // User fills in 

  endtask : compare

endclass : alu_pipeline_scoreboard

`endif