/*
  Module        : alu_imm_pipeline
  UMV Component : agent
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_AGENT_SV
`define ALU_IMM_PIPELINE_AGENT_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "sequencer.sv"
`include "driver.sv"
`include "monitor.sv"
`include "interface.sv"

// --- Agent --- //
class alu_imm_pipeline_agent extends uvm_agent;
  `uvm_component_utils(alu_imm_pipeline_agent)

  // --- Agent Components --- //
  alu_imm_pipeline_driver    drv;
  alu_imm_pipeline_monitor   mon;
  alu_imm_pipeline_sequencer seqr;
  
  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_agent", uvm_component parent);
    super.new(name, parent);
    `uvm_info("AGENT_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("AGENT_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Build Components --- //
    drv  = alu_imm_pipeline_driver::type_id::create("drv", this);
    mon  = alu_imm_pipeline_monitor::type_id::create("mon", this);
    seqr = alu_imm_pipeline_sequencer::type_id::create("seqr", this);
    
  endfunction : build_phase
  
  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("AGENT_CLASS", "Connect Phase", UVM_HIGH)
    
    // --- Sequencer -> Driver --- //
    drv.seq_item_port.connect(seqr.seq_item_export);
    
  endfunction : connect_phase
  
endclass : alu_imm_pipeline_agent

`endif