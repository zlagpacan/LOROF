/*
  Module        : alu_imm_pipeline
  UMV Component : monitor
  Author        : 
*/

`ifndef ALU_IMM_PIPELINE_MONITOR_SV
`define ALU_IMM_PIPELINE_MONITOR_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Monitor --- //
class alu_imm_pipeline_monitor extends uvm_monitor;
  `uvm_component_utils(alu_imm_pipeline_monitor)
  
  // --- Monitor Components --- //
  virtual alu_imm_pipeline_if vif;
  alu_imm_pipeline_sequence_item item;
  
  uvm_analysis_port #(alu_imm_pipeline_sequence_item) monitor_port;
  
  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_monitor", uvm_component parent);
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
    if(!(uvm_config_db #(virtual alu_imm_pipeline_if)::get(this, "*", "vif", vif))) begin
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
      item = alu_imm_pipeline_sequence_item::type_id::create("item");
      
      wait(vif.nRST);

      // --- Input Sample --- //
      item.nRST                          = vif.nRST;

      @(posedge vif.CLK);
      item.issue_valid                   = vif.issue_valid;
      item.issue_op                      = vif.issue_op;
      item.issue_imm12                   = vif.issue_imm12;
      item.issue_A_forward               = vif.issue_A_forward;
      item.issue_A_is_zero               = vif.issue_A_is_zero;
      item.issue_A_bank                  = vif.issue_A_bank;
      item.issue_dest_PR                 = vif.issue_dest_PR;
      item.issue_ROB_index               = vif.issue_ROB_index;
      item.A_reg_read_ack                = vif.A_reg_read_ack;
      item.A_reg_read_port               = vif.A_reg_read_port;
      item.reg_read_data_by_bank_by_port = vif.reg_read_data_by_bank_by_port;
      item.forward_data_by_bank          = vif.forward_data_by_bank;
      item.WB_ready                      = vif.WB_ready;
      
      // --- Output Sample --- //
      @(posedge vif.CLK);
      item.issue_ready                   = vif.issue_ready;
      item.WB_valid                      = vif.WB_valid;
      item.WB_data                       = vif.WB_data;
      item.WB_PR                         = vif.WB_PR;
      item.WB_ROB_index                  = vif.WB_ROB_index;
      
      // --- Send to Scoreboard --- //
      `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", item.convert2str()), UVM_LOW)
      monitor_port.write(item);
      
    end
        
  endtask : run_phase
  
endclass : alu_imm_pipeline_monitor

`endif