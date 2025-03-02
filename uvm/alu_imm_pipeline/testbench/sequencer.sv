/*
  Module        : alu_imm_pipeline
  UMV Component : sequencer
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_SEQUENCER_SV
`define ALU_IMM_PIPELINE_SEQUENCER_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"

class alu_imm_pipeline_sequencer extends uvm_sequencer #(alu_imm_pipeline_sequence_item);
  `uvm_component_utils(alu_imm_pipeline_sequencer)
  
  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_sequencer", uvm_component parent);
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
  
endclass : alu_imm_pipeline_sequencer

`endif