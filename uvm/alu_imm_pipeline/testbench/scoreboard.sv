/*
  Module        : alu_imm_pipeline
  UMV Component : scoreboard
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_SCOREBOARD_SV
`define ALU_IMM_PIPELINE_SCOREBOARD_SV

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
class alu_imm_pipeline_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(alu_imm_pipeline_scoreboard)

  // --- Scoreboard Components --- //
  uvm_analysis_export#(alu_imm_pipeline_sequence_item)   expected_export;
  uvm_analysis_export#(alu_imm_pipeline_sequence_item)   actual_export;
  uvm_tlm_analysis_fifo#(alu_imm_pipeline_sequence_item) expected_fifo;
  uvm_tlm_analysis_fifo#(alu_imm_pipeline_sequence_item) actual_fifo;

  int m_matches, m_mismatches, num_transactions;

  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_scoreboard", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SCB_CLASS", "Inside Constructor", UVM_HIGH)

    m_matches = 0;
    m_mismatches = 0;
    num_transactions = 0;
  endfunction : new

  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    // --- TLM FIFO Ports --- //
    expected_fifo = new("expected_fifo", this);
    actual_fifo   = new("actual_fifo", this);
    // --- Scoreboard Exports --- //
    expected_export = new("expected_export", this);
    actual_export   = new("actual_export", this);
  endfunction : build_phase

  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    // --- Connecting Fifos to Exports --- //
    expected_export.connect(expected_fifo.analysis_export);
    actual_export.connect(actual_fifo.analysis_export);
  endfunction

  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCB_CLASS", "Run Phase", UVM_HIGH)
   
    alu_imm_pipeline_sequence_item expected_tx;
    alu_imm_pipeline_sequence_item actual_tx;

    forever begin
      expected_fifo.get(expected_tx);
      actual_fifo.get(actual_tx);
      num_transactions++;

      if (expected_tx.compare(actual_tx)) begin
        m_matches++;
        uvm_report_info("SB", "Data match");
      end 
      else begin
        m_mismatches++;
        `uvm_info("SCBD", $sformatf("Test Case: : FAILED"), UVM_LOW)
        // expected_tx.print_transaction("expected_tx");
        // actual_tx.print_transaction("actual_tx");
      end
    end
    
  endtask : run_phase

  // function void report_phase(uvm_phase phase);
  //   `uvm_report_info("Comparator", $sformatf("Matches:    %0d", m_matches));
  //   `uvm_report_info("Comparator", $sformatf("Mismatches: %0d", m_mismatches));
  //   `uvm_report_info("Num trans", $sformatf("Number of transactions: %0d", num_transactions));
  // endfunction

endclass : alu_imm_pipeline_scoreboard

`endif