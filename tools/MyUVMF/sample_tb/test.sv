/*
  Module        : alu
  UMV Component : test
  Author        : Adam Keith
*/

`ifndef ALU_TEST_SV
`define ALU_TEST_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "alu_pkg.svh"
import alu_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Test --- //
class alu_test extends uvm_test;
  `uvm_component_utils(alu_test)

  // --- Test Components --- //
  alu_env env;
  
  // --- //
  parameter CLK_PERIOD = 4;
  alu_sequence test_seq;
  alu_sequence reset_seq;
  // --- //

  // --- Constructor --- //
  function new(string name = "alu_test", uvm_component parent);
    super.new(name, parent);
    `uvm_info("TEST_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST_CLASS", "Build Phase", UVM_HIGH)

    // --- Build Environment --- //
    env = alu_env::type_id::create("env", this);

  endfunction : build_phase

  // --- Test Procedure --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("TEST_CLASS", "Run Phase", UVM_HIGH)

    phase.raise_objection(this);

    // --- Test Procedure --- //
    // User fills in 
    
    `uvm_info("TEST_CLASS", "Asserting reset", UVM_HIGH)
    env.agnt.drv.vif.n_rst <= 0;
    repeat(2) @(posedge env.agnt.drv.vif.clk);
    env.agnt.drv.vif.n_rst <= 1;
    `uvm_info("TEST_CLASS", "Deasserting reset", UVM_HIGH)
    
    // Reset Transactions - would be more robust if tb wasn't a demo

    repeat(10 * CLK_PERIOD) begin
      // --- Test Sequence --- //
      test_seq = alu_sequence::type_id::create("test_seq");
      test_seq.start(env.agnt.seqr);
      #(1 * CLK_PERIOD);
    end    
    
    phase.drop_objection(this);

  endtask : run_phase

endclass : alu_test

`endif