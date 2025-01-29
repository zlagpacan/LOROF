/*
  Module        : alu_reg_pipeline
  UMV Component : scoreboard
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_SCOREBOARD_SV
`define ALU_REG_PIPELINE_SCOREBOARD_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Scoreboard --- //
class alu_reg_pipeline_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(alu_reg_pipeline_scoreboard)

  // --- Scoreboard Components --- //
  uvm_analysis_imp #(alu_reg_pipeline_sequence_item, alu_reg_pipeline_scoreboard) scoreboard_port;
  alu_reg_pipeline_sequence_item transactions[$];

  // --- Constructor --- //
  function new(string name = "alu_reg_pipeline_scoreboard", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SCB_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new

  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SCB_CLASS", "Build Phase", UVM_HIGH)
   
    // --- Scoreboard Port --- //
    scoreboard_port = new("scoreboard_port", this);
    
  endfunction : build_phase

  // --- Write Transaction --- //
  function void write(alu_reg_pipeline_sequence_item item);
    transactions.push_back(item);
  endfunction : write 

  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCB_CLASS", "Run Phase", UVM_HIGH)
   
    // --- Transaction Stack --- //
    forever begin
      alu_reg_pipeline_sequence_item curr_tx;
      wait((transactions.size() != 0));
      curr_tx = transactions.pop_front();
      compare(curr_tx);
    end
    
  endtask : run_phase

  // --- Compare --- //
  task compare(alu_reg_pipeline_sequence_item curr_tx);

  // --- Reset Check --- //
    if (curr_tx.nRST == 1'b0) begin
      // - ready_out
      if (curr_tx.issue_ready == '1) begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : PASSED"), UVM_LOW)
      end else begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : FAILED"), UVM_LOW)
      end
      // - WB_valid_out
      if (curr_tx.WB_valid == '0) begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : PASSED"), UVM_LOW)
      end else begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : FAILED"), UVM_LOW)
      end
      // - WB_data_out
      if (curr_tx.WB_data == '0) begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : PASSED"), UVM_LOW)
      end else begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : FAILED"), UVM_LOW)
      end
      // - WB_PR_out
      if (curr_tx.WB_PR == '0) begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : PASSED"), UVM_LOW)
      end else begin
        `uvm_info("COMPARE", $sformatf("Test Case: ALP_0 : FAILED"), UVM_LOW)
      end
    end

  endtask : compare

endclass : alu_reg_pipeline_scoreboard

`endif