/*
    Module   : alu_pipeline
    Filename : sequencer.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_SEQUENCER_SV
`define ALU_PIPELINE_SEQUENCER_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "core_types_pkg.vh"
`include "sequence_item.sv"
import core_types_pkg::*;

// --- ALU Pipeline Sequencer --- //
class alu_pipeline_sequencer extends uvm_sequencer #(alu_pipeline_seq_item);
  `uvm_component_utils(alu_pipeline_sequencer)

  // --- Constructor --- //
  function new(string name = "alu_pipeline_sequencer", uvm_component parent);
    super.new(name, parent);
    `uvm_info("ALU_PIPELINE_SEQR_CLASS", "Constructor", UVM_HIGH)
  endfunction: new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("ALU_PIPELINE_SEQR_CLASS", "Build Phase", UVM_HIGH)
  endfunction: build_phase
  
  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("ALU_PIPELINE_SEQR_CLASS", "Connect Phase", UVM_HIGH)
  endfunction: connect_phase

endclass : alu_pipeline_sequencer

`endif