/*
  Module        : alu_reg_mdu_iq
  UMV Component : test
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_TEST_SV
`define ALU_REG_MDU_IQ_TEST_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"
`include "sequences/reset_seq.sv"
`include "sequences/standard_seq.sv"

// --- Test --- //
class alu_reg_mdu_iq_test extends uvm_test;
  `uvm_component_utils(alu_reg_mdu_iq_test)

  // --- Test Components --- //
  alu_reg_mdu_iq_env env;
  reset_sequence reset_seq;
  garbage_sequence garb_seq;
  standard_sequence std_seq;

  // --- Constructor --- //
  function new(string name = "alu_reg_mdu_iq_test", uvm_component parent);
    super.new(name, parent);
    `uvm_info("TEST_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST_CLASS", "Build Phase", UVM_HIGH)

    // --- Build Sequence --- //
    reset_seq = reset_sequence::type_id::create("reset_seq");
    garb_seq = garbage_sequence::type_id::create("garb_seq");
    std_seq = standard_sequence::type_id::create("std_seq");

    // --- Build Environment --- //
    env = alu_reg_mdu_iq_env::type_id::create("env", this);

  endfunction : build_phase

  // --- Test Procedure --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("TEST_CLASS", "Run Phase", UVM_HIGH)

    phase.raise_objection(this);

      // --- Test Procedure --- //
      // User fills in 

      // TEST 1 RESET
    // TODO some X's in waves is that normal ASK ZACH
    // `uvm_info("ALU_md_IQ reset", "", UVM_MEDIUM)
    // repeat(20) begin
    //   repeat(5) begin
    //     garb_seq.start(env.agnt.seqr);
    //   end
    //   reset_seq.start(env.agnt.seqr);
    // end
      
    repeat(4) std_seq.start(env.agnt.seqr);
    // std_seq.start(env.agnt.seqr);
    #10ns;
    
    phase.drop_objection(this);

  endtask : run_phase

endclass : alu_reg_mdu_iq_test

`endif