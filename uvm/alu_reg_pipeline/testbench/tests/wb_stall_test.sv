/*
  Module        : alu_reg_pipeline
  UMV Component : wb stall test
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_WB_TEST_SV
`define ALU_REG_PIPELINE_WB_TEST_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "../sequence_item.sv"
`include "../interface.sv"
`include "../env.sv"
`include "../sequences/reset_seq.sv"
`include "../sequences/stall_seq.sv"
`include "../sequences/ideal_seq.sv"

// --- Test --- //
class wb_stall_test extends uvm_test;
  `uvm_component_utils(wb_stall_test)

  // --- Test Components --- //
  alu_reg_pipeline_env env;

  // --- Test Sequences --- //
  reset_sequence         reset_seq;
  garbage_sequence       garbage_seq;
  ideal_sequence         ideal_seq;
  ideal_WB_flag_sequence ideal_WB_flag_seq;
  wb_stall_sequence      wb_stall_seq;
  iss_stall_sequence     iss_stall_seq;

  parameter CLK_PERIOD = 4;

  // --- Constructor --- //
  function new(string name = "wb_stall_test", uvm_component parent);
    super.new(name, parent);
    `uvm_info("TEST_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST_CLASS", "Build Phase", UVM_HIGH)

    // --- Build Environment --- //
    env = alu_reg_pipeline_env::type_id::create("env", this);

  endfunction : build_phase

  // --- Test Procedure --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("TEST_CLASS", "Run Phase", UVM_HIGH)

    phase.raise_objection(this);

      // Prime for next test case
      reset_seq = reset_sequence::type_id::create("reset_seq");
      reset_seq.start(env.agnt.seqr);
      #(CLK_PERIOD);
      // `uvm_info("ALU_REG_TX", $sformatf("Sequence item content: %s", reset_seq.sprint()), UVM_MEDIUM)

      /* 
        Test Case Tag: ALURP_1
        Test Case Name : Writeback Stall
      */
      repeat (60) begin
          wb_stall_seq = wb_stall_sequence::type_id::create("wb_stall_seq");
          wb_stall_seq.start(env.agnt.seqr);
      end

    phase.drop_objection(this);

  endtask : run_phase

endclass : wb_stall_test

`endif