/*
  Module        : alu_reg_pipeline
  UMV Component : driver
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_DRIVER_SV
`define ALU_REG_PIPELINE_DRIVER_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Driver --- //
class alu_reg_pipeline_driver extends uvm_driver#(alu_reg_pipeline_sequence_item);
  `uvm_component_utils(alu_reg_pipeline_driver)
  
  // --- Virtual Interface + Sequence Item --- //
  virtual alu_reg_pipeline_if vif;
  alu_reg_pipeline_sequence_item item;
  
  // --- Constructor --- //
  function new(string name = "alu_reg_pipeline_driver", uvm_component parent);
    super.new(name, parent);
    `uvm_info("DRIVER_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("DRIVER_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Virtual Interface Failure --- //
    if(!(uvm_config_db #(virtual alu_reg_pipeline_if)::get(this, "*", "vif", vif))) begin
      `uvm_error("DRIVER_CLASS", "Failed to get virtual interface")
    end
    
  endfunction : build_phase
  
  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("DRIVER_CLASS", "Inside Run Phase", UVM_HIGH)
    
    // --- Sequence Item Queue --- //
    forever begin
      item = alu_reg_pipeline_sequence_item::type_id::create("item"); 
      seq_item_port.get_next_item(item);
      drive(item);
      seq_item_port.item_done();
    end
  endtask : run_phase
  
  // --- Drive Virtual Interface --- //
  task drive(alu_reg_pipeline_sequence_item item);

    @(posedge vif.CLK);
    vif.nRST                          <= item.nRST;
    vif.issue_valid                   <= item.issue_valid;
    vif.issue_op                      <= item.issue_op;
    vif.issue_A_forward               <= item.issue_A_forward;
    vif.issue_A_bank                  <= item.issue_A_bank;
    vif.issue_A_is_zero               <= item.issue_A_is_zero;
    vif.issue_B_forward               <= item.issue_B_forward;
    vif.issue_B_bank                  <= item.issue_B_bank;
    vif.issue_dest_PR                 <= item.issue_dest_PR;
    vif.issue_ROB_index               <= item.issue_ROB_index;
    vif.A_reg_read_ack                <= item.A_reg_read_ack;
    vif.A_reg_read_port               <= item.A_reg_read_port;
    vif.B_reg_read_ack                <= item.B_reg_read_ack;
    vif.B_reg_read_port               <= item.B_reg_read_port;
    vif.reg_read_data_by_bank_by_port <= item.reg_read_data_by_bank_by_port;
    vif.forward_data_by_bank          <= item.forward_data_by_bank;
    vif.WB_ready                      <= item.WB_ready;
    
  endtask : drive
  
endclass : alu_reg_pipeline_driver

`endif