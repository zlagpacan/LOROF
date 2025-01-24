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
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
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
  function void write(alu_sequence_item item);
    transactions.push_back(item);
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

    case(curr_tx.op)
      4'b0000 : begin
        if (curr_tx.out == curr_tx.A + curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b0001 : begin
        if (curr_tx.out == curr_tx.A << curr_tx.B[4:0]) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b0010 : begin
        if (curr_tx.out == (signed(curr_tx.A) < signed(curr_tx.B) ? '1 : '0)) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b0011 : begin
        if (curr_tx.out == (unsigned(curr_tx.A) < unsigned(curr_tx.B) ? '1 : '0)) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b0100 : begin
        if (curr_tx.out == curr_tx.A ^ curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b0101 : begin
        if (curr_tx.out == curr_tx.A >> curr_tx.B[4:0]) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b0110 : begin
        if (curr_tx.out == curr_tx.A | curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b0111 : begin
        if (curr_tx.out == curr_tx.A & curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1000 : begin
        if (curr_tx.out == curr_tx.A - curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1001 : begin
        if (curr_tx.out == curr_tx.A << curr_tx.B[4:0]) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1010 : begin
        if (curr_tx.out == (signed(curr_tx.A) < signed(curr_tx.B) ? '1 : '0)) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1011 : begin
        if (curr_tx.out == (unsigned(curr_tx.A) < unsigned(curr_tx.B) ? '1 : '0)) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1100 : begin
        if (curr_tx.out == curr_tx.A ^ curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1101 : begin
        if (curr_tx.out == signed(curr_tx.A) >>> signed(curr_tx.B)) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1110 : begin
        if (curr_tx.out == curr_tx.A | curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
      4'b1111 : begin
        if (curr_tx.out == curr_tx.A & curr_tx.B) begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: PASSED"), UVM_LOW)
        end else begin
          `uvm_info("COMPARE", $sformatf("Test Case : ALU_0 - alu add op: FAILED"), UVM_LOW)
        end
      end
    endcase


  endtask : compare

endclass : alu_scoreboard

`endif