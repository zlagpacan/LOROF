/*
  Module        : alu
  UMV Component : environment
  Author        : Adam Keith
*/

`ifndef ALU_ENV_SV
`define ALU_ENV_SV

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

// --- Environment --- //
class alu_env extends uvm_env;
  `uvm_component_utils(alu_env)
  
  // --- Env Components --- //
  alu_agent agnt;
  alu_scoreboard scb;

  // --- Constructor --- //
  function new(string name = "alu_env", uvm_component parent);
    super.new(name, parent);
    `uvm_info("ENV_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("ENV_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Build Agent + Scoreboard --- //
    agnt = alu_agent::type_id::create("agnt", this);
    scb  = alu_scoreboard::type_id::create("scb", this);
    
  endfunction : build_phase
  
  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("ENV_CLASS", "Connect Phase", UVM_HIGH)
    
    // --- Monitor -> Scoreboard --- //
    agnt.mon.monitor_port.connect(scb.scoreboard_port);
    
  endfunction : connect_phase
  
endclass : alu_env

`endif