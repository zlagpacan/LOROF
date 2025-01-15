/*
  Module        : alu
  UMV Component : scoreboard
  Author        : Adam Keith
*/

`ifndef ALU_SCOREBOARD_SV
`define ALU_SCOREBOARD_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "alu_pkg.svh"
import alu_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Scoreboard --- //
class alu_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(alu_scoreboard)

  // --- Scoreboard Components --- //
  uvm_analysis_imp #(alu_sequence_item, alu_scoreboard) scoreboard_port;
  alu_sequence_item transactions[$];

  // --- Constructor --- //
  function new(string name = "alu_scoreboard", uvm_component parent);
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
  function void write(alu_sequence_item curr_tx);
    transactions.push_back(curr_tx);
  endfunction : write 

  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCB_CLASS", "Run Phase", UVM_HIGH)
   
    // --- Transaction Stack --- //
    forever begin
      alu_sequence_item curr_tx;
      wait((transactions.size() != 0));
      curr_tx = transactions.pop_front();
      compare(curr_tx);
    end
    
  endtask : run_phase

  // --- Compare --- //
  task compare(alu_sequence_item curr_tx);
    `uvm_info("COMPARE", $sformatf("n_rst: %b, out: %0h", curr_tx.n_rst, curr_tx.out), UVM_HIGH)

  // User fills in 

  // NOTE: Not robust - just for demo
    case(curr_tx.n_rst)
      1'b0: begin
        if ((curr_tx.out == '0)) begin
          `uvm_info("COMPARE", $sformatf("Test Case Reset: PASSED"), UVM_HIGH)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case Reset: FAILED"), UVM_HIGH)
        end
      end
    endcase

  endtask : compare

endclass : alu_scoreboard

`endif