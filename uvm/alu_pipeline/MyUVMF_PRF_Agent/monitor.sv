/*
  Module        : alu_pipeline_prf
  UMV Component : monitor
  Author        : 
*/

`ifndef ALU_PIPELINE_PRF_MONITOR_SV
`define ALU_PIPELINE_PRF_MONITOR_SV

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
class alu_pipeline_prf_monitor extends uvm_monitor;
  `uvm_component_utils(alu_pipeline_prf_monitor)
  
  // --- Monitor Components --- //
  virtual alu_pipeline_prf_if vif;
  alu_pipeline_prf_sequence_item item;
  
  uvm_analysis_port #(alu_pipeline_prf_sequence_item) monitor_port;
  
  // --- Constructor --- //
  function new(string name = "alu_pipeline_prf_monitor", uvm_component parent);
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
    if(!(uvm_config_db #(virtual alu_pipeline_prf_if)::get(this, "*", "vif", vif))) begin
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
      item = alu_pipeline_prf_sequence_item::type_id::create("item");
      
      wait(vif.nRST);

      // --- Input Sample --- //
      item.nRST                     = vif.nRST;

      @(posedge vif.CLK);
      item.A_reg_read_valid_in      = vif.A_reg_read_valid_in;
      item.B_reg_read_valid_in      = vif.B_reg_read_valid_in;
      item.ROB_index_in             = vif.ROB_index_in;
      item.reg_read_data_by_bank_in = vif.reg_read_data_by_bank_in;
      item.forward_data_by_bank_in  = vif.forward_data_by_bank_in;
      
      // --- Output Sample --- //
      @(posedge vif.CLK);
      item.WB_valid_out             = vif.WB_valid_out;
      item.WB_data_out              = vif.WB_data_out;
      item.WB_PR_out                = vif.WB_PR_out;
      item.WB_ROB_index_out         = vif.WB_ROB_index_out;
      
      // --- Send to Scoreboard --- //
      `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", item.convert2str()), UVM_LOW)
      monitor_port.write(item);
      
    end
        
  endtask : run_phase
  
endclass : alu_pipeline_prf_monitor

`endif