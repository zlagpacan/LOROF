/*
  Module        : alu_pipeline_iq
  UMV Component : monitor
  Author        : 
*/

`ifndef ALU_PIPELINE_IQ_MONITOR_SV
`define ALU_PIPELINE_IQ_MONITOR_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Monitor --- //
class alu_pipeline_iq_monitor extends uvm_monitor;
  `uvm_component_utils(alu_pipeline_iq_monitor)
  
  // --- Monitor Components --- //
  virtual alu_pipeline_iq_if vif;
  alu_pipeline_iq_sequence_item item;
  
  uvm_analysis_port #(alu_pipeline_iq_sequence_item) monitor_port;
  
  // --- Constructor --- //
  function new(string name = "alu_pipeline_iq_monitor", uvm_component parent);
    super.new(name, parent);
    `uvm_info("MONITOR_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("MONITOR_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Build Monitor Port --- //
    monitor_port = new("monitor_port", this);
    
    // --- Virtual Interface Failure --- //
    if(!(uvm_config_db #(virtual alu_pipeline_iq_if)::get(this, "*", "vif", vif))) begin
      `uvm_error("MONITOR_CLASS", "Failed to get virtual interface")
    end
    
  endfunction : build_phase
  
  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("MONITOR_CLASS", "Connect Phase", UVM_HIGH)
    
  endfunction : connect_phase
  
  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("MONITOR_CLASS", "Run Phase", UVM_HIGH)
    
    // --- Capture DUT Interface --- //
    forever begin
      item = alu_pipeline_iq_sequence_item::type_id::create("item");
      
      wait(vif.nRST);

      // --- Input Sample --- //
      item.nRST          = vif.nRST;

      @(posedge vif.CLK);
      item.valid_in      = vif.valid_in;
      item.op_in         = vif.op_in;
      item.is_imm_in     = vif.is_imm_in;
      item.imm_in        = vif.imm_in;
      item.A_unneeded_in = vif.A_unneeded_in;
      item.A_forward_in  = vif.A_forward_in;
      item.A_bank_in     = vif.A_bank_in;
      item.B_forward_in  = vif.B_forward_in;
      item.B_bank_in     = vif.B_bank_in;
      item.dest_PR_in    = vif.dest_PR_in;
      
      // --- Output Sample --- //
      @(posedge vif.CLK);
      item.ready_out     = vif.ready_out;
      
      // --- Send to Scoreboard --- //
      `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", item.convert2str()), UVM_LOW)
      monitor_port.write(item);
      
    end
        
  endtask : run_phase
  
endclass : alu_pipeline_iq_monitor

`endif