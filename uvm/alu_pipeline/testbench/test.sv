/*
  Module        : alu_pipeline
  UMV Component : test
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_TEST_SV
`define ALU_PIPELINE_TEST_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "sequences/reset_seq.sv"
`include "interface.sv"

// --- Test --- //
class alu_pipeline_test extends uvm_test;
  `uvm_component_utils(alu_pipeline_test)

  // --- Test Components --- //
  alu_pipeline_env env;
  reset_sequence reset_seq;
  garbage_sequence garbage_seq;

  // --- Clocking --- //
  parameter CLK_PERIOD = 4;

  // --- Constructor --- //
  function new(string name = "alu_pipeline_test", uvm_component parent);
    super.new(name, parent);
    `uvm_info("TEST_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST_CLASS", "Build Phase", UVM_HIGH)

    // --- Build Environment --- //
    env = alu_pipeline_env::type_id::create("env", this);

  endfunction : build_phase

  // --- Test Procedure --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("TEST_CLASS", "Run Phase", UVM_HIGH)

    phase.raise_objection(this);

      // --- ALU Pipeline Test Procedure --- //

      /* 
        Test Case Tag: ALP0
        Test Case Name : Power-on-Reset
      */
      
      // TODO: change to posedge clk - stability - need to OOP it
      repeat (6 * CLK_PERIOD) begin
        garbage_seq = garbage_sequence::type_id::create("garbage_seq");
        garbage_seq.start(env.agnt.seqr);
        #(CLK_PERIOD);
      end

      reset_seq = reset_sequence::type_id::create("reset_seq");
      reset_seq.start(env.agnt.seqr);
      #(CLK_PERIOD);

      repeat (4 * CLK_PERIOD) begin
        garbage_seq = garbage_sequence::type_id::create("garbage_seq");
        garbage_seq.start(env.agnt.seqr);
        #(CLK_PERIOD);
      end

    phase.drop_objection(this);

  endtask : run_phase

endclass : alu_pipeline_test

`endif