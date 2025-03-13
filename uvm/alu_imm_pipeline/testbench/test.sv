/*
  Module        : alu_imm_pipeline
  UMV Component : test
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_TEST_SV
`define ALU_IMM_PIPELINE_TEST_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"
`include "env.sv"
`include "sequences/reset_seq.sv"
`include "sequences/stall_seq.sv"
`include "sequences/ideal_seq.sv"


// --- Test --- //
class alu_imm_pipeline_test extends uvm_test;
  `uvm_component_utils(alu_imm_pipeline_test)

  // --- Test Components --- //
  alu_imm_pipeline_env env;

  // --- Test Sequences --- //
  reset_sequence    reset_seq;
  garbage_sequence  garbage_seq;
  wb_stall_sequence wb_stall_seq;
  ideal_sequence    ideal_seq;

  // --- Debug --- //
  string tc_name = "";

  parameter CLK_PERIOD = 4;

  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_test", uvm_component parent);
    super.new(name, parent);
    `uvm_info("TEST_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST_CLASS", "Build Phase", UVM_HIGH)

    // --- Build Environment --- //
    env = alu_imm_pipeline_env::type_id::create("env", this);

  endfunction : build_phase

  function void set_test_case_name(string name);
    tc_name = name;
    `uvm_info("TEST_CLASS", $sformatf("Test case name set to: %s", tc_name), UVM_LOW)
  endfunction

  // --- Test Procedure --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("TEST_CLASS", "Run  Phase", UVM_HIGH)

    phase.raise_objection(this);

      // $add_waveform("/uvm_root/uvm_test_top/tc_name");

      // --- ALU Imm Pipeline Test Procedure --- //

      /*********************************** 
        Test Case Tag  : tc_reset
        Test Case Name : Reset Values
      ************************************/
      tc_name = "tc_reset";
      env.scb.set_test_case_name(tc_name);

      repeat (4) begin
        garbage_seq = garbage_sequence::type_id::create("garbage_seq");
        garbage_seq.start(env.agnt.seqr);
      end

      #(0.5 * CLK_PERIOD);
      reset_seq = reset_sequence::type_id::create("reset_seq");
      reset_seq.start(env.agnt.seqr);
      #(0.5 * CLK_PERIOD);

      repeat (4) begin
        ideal_seq = ideal_sequence::type_id::create("ideal_sequence");
        ideal_seq.start(env.agnt.seqr);
      end

      /*********************************** 
        Test Case Tag  : tc_wb_stall
        Test Case Name : Writeback Stall
      ************************************/
      tc_name = "tc_wb_stall";
      env.scb.set_test_case_name(tc_name);

      repeat (60) begin
        wb_stall_seq = wb_stall_sequence::type_id::create("wb_stall_seq");
        wb_stall_seq.start(env.agnt.seqr);
      end

      /*********************************** 
        Test Case Tag  : tc_standard_wb
        Test Case Name : Standard Writeback
      ************************************/
      tc_name = "tc_standard_wb";
      env.scb.set_test_case_name(tc_name);

      repeat (30) begin
        ideal_seq = ideal_sequence::type_id::create("ideal_seq");
        ideal_seq.start(env.agnt.seqr);
      end

    
    phase.drop_objection(this);

  endtask : run_phase

endclass : alu_imm_pipeline_test

`endif