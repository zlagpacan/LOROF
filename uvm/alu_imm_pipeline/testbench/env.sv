/*
  Module        : alu_imm_pipeline
  UMV Component : environment
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_ENV_SV
`define ALU_IMM_PIPELINE_ENV_SV

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
`include "agent.sv"
`include "scoreboard.sv"
`include "predictor.sv"
`include "coverage.sv"

// --- Environment --- //
class alu_imm_pipeline_env extends uvm_env;
  `uvm_component_utils(alu_imm_pipeline_env)
  
  // --- Env Components --- //
  alu_imm_pipeline_agent      agnt;
  alu_imm_pipeline_scoreboard scb;
  alu_imm_pipeline_predictor  pred;
  alu_imm_pipeline_coverage   coverage_tracker;

  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_env", uvm_component parent);
    super.new(name, parent);
    `uvm_info("ENV_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("ENV_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Build Agent + Scoreboard --- //
    agnt     = alu_imm_pipeline_agent::type_id::create("agnt", this);
    scb      = alu_imm_pipeline_scoreboard::type_id::create("scb", this);
    pred     = alu_imm_pipeline_predictor::type_id::create("pred",this);
    coverage = alu_imm_pipeline_coverage::type_id::create("coverage",this);
    
  endfunction : build_phase
  
  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("ENV_CLASS", "Connect Phase", UVM_HIGH)
    
    // --- Monitor -> Scoreboard --- //
    agnt.mon.monitor_port.connect(scb.actual_export);

    // --- Monitor -> Predictor --- //
    agnt.mon.predictor_port.connect(pred.analysis_export);

    // --- Predictor -> Scoreboard --- //
    pred.pred_ap.connect(scb.expected_export);

    // --- Monitor -> Coverage Tracker --- //
    agnt.mon.coverage_port.connect(coverage.coverage_port);
    
  endfunction : connect_phase
  
endclass : alu_imm_pipeline_env

`endif