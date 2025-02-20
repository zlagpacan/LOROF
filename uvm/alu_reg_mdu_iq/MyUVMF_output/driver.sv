/*
  Module        : alu_reg_mdu_iq
  UMV Component : driver
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_DRIVER_SV
`define ALU_REG_MDU_IQ_DRIVER_SV

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
class alu_reg_mdu_iq_driver extends uvm_driver#(alu_reg_mdu_iq_sequence_item);
  `uvm_component_utils(alu_reg_mdu_iq_driver)
  
  // --- Virtual Interface + Sequence Item --- //
  virtual alu_reg_mdu_iq_if vif;
  alu_reg_mdu_iq_sequence_item item;
  
  // --- Constructor --- //
  function new(string name = "alu_reg_mdu_iq_driver", uvm_component parent);
    super.new(name, parent);
    `uvm_info("DRIVER_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("DRIVER_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Virtual Interface Failure --- //
    if(!(uvm_config_db #(virtual alu_reg_mdu_iq_if)::get(this, "*", "vif", vif))) begin
      `uvm_error("DRIVER_CLASS", "Failed to get virtual interface")
    end
    
  endfunction : build_phase
  
  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("DRIVER_CLASS", "Inside Run Phase", UVM_HIGH)
    
    // --- Sequence Item Queue --- //
    forever begin
      item = alu_reg_mdu_iq_sequence_item::type_id::create("item"); 
      seq_item_port.get_next_item(item);
      drive(item);
      seq_item_port.item_done();
    end
  endtask : run_phase
  
  // --- Drive Virtual Interface --- //
  task drive(alu_reg_mdu_iq_sequence_item item);

    @(posedge vif.CLK);
    vif.nRST                          <= item.nRST;
    vif.dispatch_attempt_by_way       <= item.dispatch_attempt_by_way;
    vif.dispatch_valid_alu_reg_by_way <= item.dispatch_valid_alu_reg_by_way;
    vif.dispatch_valid_mdu_by_way     <= item.dispatch_valid_mdu_by_way;
    vif.dispatch_op_by_way            <= item.dispatch_op_by_way;
    vif.dispatch_A_PR_by_way          <= item.dispatch_A_PR_by_way;
    vif.dispatch_A_ready_by_way       <= item.dispatch_A_ready_by_way;
    vif.dispatch_B_PR_by_way          <= item.dispatch_B_PR_by_way;
    vif.dispatch_B_ready_by_way       <= item.dispatch_B_ready_by_way;
    vif.dispatch_dest_PR_by_way       <= item.dispatch_dest_PR_by_way;
    vif.dispatch_ROB_index_by_way     <= item.dispatch_ROB_index_by_way;
    vif.alu_reg_pipeline_ready        <= item.alu_reg_pipeline_ready;
    vif.mdu_pipeline_ready            <= item.mdu_pipeline_ready;
    vif.WB_bus_valid_by_bank          <= item.WB_bus_valid_by_bank;
    vif.WB_bus_upper_PR_by_bank       <= item.WB_bus_upper_PR_by_bank;
    
  endtask : drive
  
endclass : alu_reg_mdu_iq_driver

`endif