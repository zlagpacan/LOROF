/*
  Module        : alu_reg_pipeline
  UMV Component : Ideal (1 OP per cycle) sequence
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_IDEAL_SEQ_SV
`define ALU_REG_PIPELINE_IDEAL_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Ideal Sequence --- //
class ideal_sequence extends uvm_sequence;
  `uvm_object_utils(ideal_sequence)
  
  alu_reg_pipeline_sequence_item ideal_tx;
  
  // --- Constructor --- //
  function new(string name= "ideal_sequence");
    super.new(name);
    `uvm_info("IDEAL_SEQ", "Inside Constructor", UVM_HIGH)
  endfunction
  
  // --- Body Task --- //
  task body();
    `uvm_info("IDEAL_SEQ", "Inside body task", UVM_HIGH)
    
    // --- Randomize --- //
    ideal_tx = alu_reg_pipeline_sequence_item::type_id::create("ideal_tx");
    start_item(ideal_tx);
    ideal_tx.randomize() with{
      WB_ready        == 1'b1;
    };
    finish_item(ideal_tx);
        
  endtask : body
  
endclass : ideal_sequence

// --- Ideal WB Flag Sequence --- //
/*
  Constraint for ALURP_2A - Identifying stalls
    - Idea is to constraint WB_PR and WB_ROB
      to all values but 1 value and then issue
      that value in the stall seq to validate
      timing
*/
class ideal_WB_flag_sequence extends uvm_sequence;
  `uvm_object_utils(ideal_WB_flag_sequence)
  
  alu_reg_pipeline_sequence_item ideal_WB_flag_tx;
  
  // --- Constructor --- //
  function new(string name= "ideal_WB_flag_sequence");
    super.new(name);
    `uvm_info("IDEAL_WB_FLAG_SEQ", "Inside Constructor", UVM_HIGH)
  endfunction
  
  // --- Body Task --- //
  task body();
    `uvm_info("IDEAL_WB_FLAG_SEQ", "Inside body task", UVM_HIGH)
    
    // --- Randomize --- //
    ideal_WB_flag_tx = alu_reg_pipeline_sequence_item::type_id::create("ideal_WB_flag_tx");
    start_item(ideal_WB_flag_tx);
    ideal_WB_flag_tx.randomize() with {
      WB_ready        == 1'b1;
      issue_dest_PR   != 7'h1;
      issue_ROB_index != 7'h1;
    };
    finish_item(ideal_WB_flag_tx);
        
  endtask : body
  
endclass : ideal_WB_flag_sequence

`endif