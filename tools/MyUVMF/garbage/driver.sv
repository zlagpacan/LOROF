/*
  Module        : alu
  UMV Component : driver
  Author        : 
*/

`ifndef ALU_DRIVER_SV
`define ALU_DRIVER_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "alu_pkg.svh"
import alu_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Driver --- //
class alu_driver extends uvm_driver#(alu_sequence_item);
  `uvm_component_utils(alu_driver)
  
  // --- Virtual Interface + Sequence Item --- //
  virtual alu_if vif;
  alu_sequence_item item;
  
  // --- Constructor --- //
  function new(string name = "alu_driver", uvm_component parent);
    super.new(name, parent);
    `uvm_info("DRIVER_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("DRIVER_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Virtual Interface Failure --- //
    if(!(uvm_config_db #(virtual alu_if)::get(this, "*", "vif", vif))) begin
      `uvm_error("DRIVER_CLASS", "Failed to get virtual interface")
    end
    
  endfunction : build_phase
  
  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("DRIVER_CLASS", "Inside Run Phase", UVM_HIGH)
    
    // --- Sequence Item Queue --- //
    forever begin
      item = alu_sequence_item::type_id::create("item"); 
      seq_item_port.get_next_item(item);
      drive(item);
      seq_item_port.item_done();
    end
  endtask : run_phase
  
  // --- Drive Virtual Interface --- //
  task drive(alu_sequence_item item);

    @(posedge vif.clk);
    vif.n_rst  <= item.n_rst;
    vif.a      <= item.a;
    vif.b      <= item.b;
    vif.opcode <= item.opcode;
    
  endtask : drive
  
endclass : alu_driver

`endif