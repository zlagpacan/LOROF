/*
  Module        : alu
  UMV Component : monitor
  Author        : 
*/

`ifndef ALU_MONITOR_SV
`define ALU_MONITOR_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "alu_pkg.svh"
import alu_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Monitor --- //
class alu_monitor extends uvm_monitor;
  `uvm_component_utils(alu_monitor)
  
  // --- Monitor Components --- //
  virtual alu_if vif;
  alu_sequence_item item;
  
  uvm_analysis_port #(alu_sequence_item) monitor_port;
  
  // --- Constructor --- //
  function new(string name = "alu_monitor", uvm_component parent);
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
    if(!(uvm_config_db #(virtual alu_if)::get(this, "*", "vif", vif))) begin
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
      item = alu_sequence_item::type_id::create("item");
      
      wait(vif.n_rst);

      // --- Input Sample --- //
      item.n_rst    = vif.n_rst;

      @(posedge vif.clk);
      item.a        = vif.a;
      item.b        = vif.b;
      item.opcode   = vif.opcode;
      
      // --- Output Sample --- //
      @(posedge vif.clk);
      item.negative = vif.negative;
      item.out      = vif.out;
      item.overflow = vif.overflow;
      item.zero     = vif.zero;
      
      // --- Send to Scoreboard --- //
      `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", item.convert2str()), UVM_LOW)
      monitor_port.write(item);
      
    end
        
  endtask : run_phase
  
endclass : alu_monitor

`endif