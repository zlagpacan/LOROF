/*
  Module        : alu_pipeline
  UMV Component : driver
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_DRIVER_SV
`define ALU_PIPELINE_DRIVER_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Driver --- //
class alu_pipeline_driver extends uvm_driver#(alu_pipeline_sequence_item);
  `uvm_component_utils(alu_pipeline_driver)
  
  // --- Virtual Interface + Sequence Item --- //
  virtual alu_pipeline_if vif;
  alu_pipeline_sequence_item item;
  
  // --- Constructor --- //
  function new(string name = "alu_pipeline_driver", uvm_component parent);
    super.new(name, parent);
    `uvm_info("DRIVER_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("DRIVER_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Virtual Interface Failure --- //
    if(!(uvm_config_db #(virtual alu_pipeline_if)::get(this, "*", "vif", vif))) begin
      `uvm_error("DRIVER_CLASS", "Failed to get virtual interface")
    end
    
  endfunction : build_phase
  
  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("DRIVER_CLASS", "Inside Run Phase", UVM_HIGH)
    
    // --- Sequence Item Queue --- //
    forever begin
      item = alu_pipeline_sequence_item::type_id::create("item"); 
      seq_item_port.get_next_item(item);
      drive(item);
      seq_item_port.item_done();
    end
  endtask : run_phase
  
  // --- Drive Virtual Interface --- //
  task drive(alu_pipeline_sequence_item item);

    @(posedge vif.CLK);
    vif.nRST                     <= item.nRST;
    vif.valid_in                 <= item.valid_in;
    vif.op_in                    <= item.op_in;
    vif.is_imm_in                <= item.is_imm_in;
    vif.imm_in                   <= item.imm_in;
    vif.A_unneeded_in            <= item.A_unneeded_in;
    vif.A_forward_in             <= item.A_forward_in;
    vif.A_bank_in                <= item.A_bank_in;
    vif.B_forward_in             <= item.B_forward_in;
    vif.B_bank_in                <= item.B_bank_in;
    vif.dest_PR_in               <= item.dest_PR_in;
    vif.A_reg_read_valid_in      <= item.A_reg_read_valid_in;
    vif.B_reg_read_valid_in      <= item.B_reg_read_valid_in;
    vif.ROB_index_in             <= item.ROB_index_in;
    vif.reg_read_data_by_bank_in <= item.reg_read_data_by_bank_in;
    vif.forward_data_by_bank_in  <= item.forward_data_by_bank_in;
    
  endtask : drive
  
endclass : alu_pipeline_driver

`endif