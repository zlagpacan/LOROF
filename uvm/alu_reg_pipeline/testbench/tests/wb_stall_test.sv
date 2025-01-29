/*
  Module        : alu_reg_pipeline
  UMV Component : test - writeback stall
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_WB_STALL_TEST_SV
`define ALU_REG_PIPELINE_WB_STALL_TEST_SV

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
`include "sequences/wb_stall_seq.sv"

// --- Test --- //
class alu_reg_pipeline_wb_stall_test extends uvm_test;
  `uvm_component_utils(alu_reg_pipeline_wb_stall_test)

  // --- Test Components --- //
  alu_reg_pipeline_env env;
  wb_stall_sequence wb_stall_seq;
//   wb_ready_sequence wb_ready_seq;

  parameter CLK_PERIOD = 4;

  // --- Constructor --- //
  function new(string name = "alu_reg_pipeline_wb_stall_test", uvm_component parent);
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

        // --- ALU Reg Pipeline Test Procedure --- //
        /* 
          Test Case Tag: ALURP_1
          Test Case Name : Writeback Stall
        */
        repeat (40) begin
            wb_stall_seq = wb_stall_sequence::type_id::create("wb_stall_seq");
            wb_stall_seq.start(env.agnt.seqr);
        end

    phase.drop_objection(this);

  endtask : run_phase

endclass : alu_reg_pipeline_wb_stall_test

`endif