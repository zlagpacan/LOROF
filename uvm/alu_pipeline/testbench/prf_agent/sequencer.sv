/*
  Module        : alu_pipeline_prf
  UMV Component : sequencer
  Author        : 
*/

`ifndef ALU_PIPELINE_PRF_SEQUENCER_SV
`define ALU_PIPELINE_PRF_SEQUENCER_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"

class alu_pipeline_prf_sequencer extends uvm_sequencer #(alu_pipeline_prf_sequence_item);
  `uvm_component_utils(alu_pipeline_prf_sequencer)
  
  // --- Constructor --- //
  function new(string name = "alu_pipeline_prf_sequencer", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SEQUENCER_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SEQUENCER_CLASS", "Build Phase", UVM_HIGH)
  endfunction : build_phase
  
  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("SEQUENCER_CLASS", "Connect Phase", UVM_HIGH)
  endfunction : connect_phase
  
endclass : alu_pipeline_prf_sequencer

`endif