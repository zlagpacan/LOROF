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
`include "sequences/mdu_seq.sv"

// --- Test --- //
class alu_reg_mdu_iq_test extends uvm_test;
  `uvm_component_utils(alu_reg_mdu_iq_test)

  // --- Test Components --- //
  alu_reg_mdu_iq_env env;
  reset_sequence reset_seq;
  garbage_sequence garb_seq;
  standard_sequence std_seq;

  // Reg pipeline sequences 
  simp_reg_seq simp_reg;
  simp_reg_seq2 simp_reg2;
  simp_a_b_nr simp_a_b_nr_seq;
  reg_normal_op_no_wb reg_norop_n_wb;
  reg_normal_pipe_nr reg_pipe_nr;


  // Mdu Pipeline sequences
  simp_mdu_seq simp_mdu;
  simp_mdu_seq2 simp_mdu2;
  simp_mdu_a_b_nr simp_mdu_a_b_nr_seq;
  mdu_normal_op_no_wb mdu_norop_n_wb;
  mdu_normal_pipe_nr mdu_pipe_nr;

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
    `uvm_info("ALU_md_IQ reset", "", UVM_MEDIUM)
    // repeat(20) begin
    //   repeat(5) begin
    //     garb_seq.start(env.agnt.seqr);
    //   end
    //   reset_seq.start(env.agnt.seqr);
    // end
      

    // // Test 2 Simple dispatch to reg pipeline
    `uvm_info("ALU_md_IQ Reg_IQ one, both operands ready", "", UVM_MEDIUM)
    // simp_reg = simp_reg_seq::type_id::create("simp_reg");
    // repeat(10) simp_reg.start(env.agnt.seqr); 


    // // Test 3 Dispatch from 2 ways
    `uvm_info("ALU_md_IQ Reg IQ two, both operands ready", "", UVM_MEDIUM)
    // simp_reg2 = simp_reg_seq2::type_id::create("simp_reg2");
    // repeat(10) simp_reg2.start(env.agnt.seqr); 

    // // Test case 4 all operands not ready no dispatch should occur 
    `uvm_info("ALU_md_IQ operands not ready no issue", "", UVM_MEDIUM)
    // reset_seq.start(env.agnt.seqr); // reset to clear the queue
    // simp_a_b_nr_seq = simp_a_b_nr::type_id::create("simp_a_b_nr");
    // repeat(10) simp_a_b_nr_seq.start(env.agnt.seqr); 

    // Test case 5 regular operation but with no WB
    `uvm_info("ALU_md_IQ normal opereration no WB", "", UVM_MEDIUM)
    // reset_seq.start(env.agnt.seqr); // reset to clear the queue
    // reg_norop_n_wb = reg_normal_op_no_wb::type_id::create("reg_norop_n_wb");
    // repeat(30) reg_norop_n_wb.start(env.agnt.seqr); 

    // Test case 6 reg pipe not ready 
    `uvm_info("ALU_md_IQ pipeline not ready", "", UVM_MEDIUM)
    // reg_pipe_nr = reg_normal_pipe_nr::type_id::create("reg_pipe_nr");
    // repeat(10) reg_pipe_nr.start(env.agnt.seqr); 
    

    // Test case 7 Simple dispatch to mdu pipeline
    `uvm_info("ALU_md_IQ MUL DIV one, both operands ready", "", UVM_MEDIUM)
    // simp_mdu = simp_mdu_seq::type_id::create("simp_mdu");
    // repeat(10) simp_mdu.start(env.agnt.seqr); 

     
    // Test case 8 Dispatching 2 random mdu ways
    `uvm_info("ALU_md_IQ MUL DIV two, both operands ready", "", UVM_MEDIUM)
    // simp_mdu2 = simp_mdu_seq2::type_id::create("simp_mdu2");
    // repeat(10) simp_mdu2.start(env.agnt.seqr); 

    // Test case 9 mdu a and b not ready 
    `uvm_info("ALU_md_IQ MUL DIV two, both operands ready", "", UVM_MEDIUM)
    // simp_mdu_a_b_nr_seq = simp_mdu_a_b_nr::type_id::create("simp_mdu_a_b_nr_seq");
    // repeat(10) simp_mdu_a_b_nr_seq.start(env.agnt.seqr); 

    // Test case 10 regular mdu operation
    `uvm_info("ALU_md_IQ MUL DIV normal opereration", "", UVM_MEDIUM)
    // reset_seq.start(env.agnt.seqr); // reset to clear the queue
    // mdu_norop_n_wb = mdu_normal_op_no_wb::type_id::create("mdu_norop_n_wb");
    // repeat(30) mdu_norop_n_wb.start(env.agnt.seqr); 

    // Test case 11 mdu pipe not ready
    `uvm_info("MUL IQ pipeline not ready", "", UVM_MEDIUM)
    mdu_pipe_nr = mdu_normal_pipe_nr::type_id::create("mdu_pipe_nr");
    repeat(10) mdu_pipe_nr.start(env.agnt.seqr); 

    
    // repeat(120) std_seq.start(env.agnt.seqr);
    // std_seq.start(env.agnt.seqr);
    #10ns;
    
    phase.drop_objection(this);

  endtask : run_phase

endclass : alu_reg_mdu_iq_test

`endif