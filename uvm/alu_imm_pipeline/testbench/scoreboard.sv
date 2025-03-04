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

  alu_imm_pipeline_sequence_item expected_tx;
  alu_imm_pipeline_sequence_item actual_tx;

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
    super.build_phase(phase);
    
    // --- Create FIFOs --- //
    expected_fifo = new("expected_fifo", this);
    actual_fifo   = new("actual_fifo", this);

    // --- Create Exports --- //
    expected_export = new("expected_export", this);
    actual_export = new("actual_export", this);

    // --- Connect Exports to FIFOs --- //
    expected_export.connect(expected_fifo.analysis_export);
    actual_export.connect(actual_fifo.analysis_export);
  endfunction : build_phase

  // --- Run Phase --- //
  task run_phase(uvm_phase phase);
    super.run_phase(phase);
   


    // Allocate memory for transactions
    expected_tx = alu_imm_pipeline_sequence_item::type_id::create("expected_tx");
    actual_tx = alu_imm_pipeline_sequence_item::type_id::create("actual_tx");

    forever begin
      expected_fifo.get(expected_tx);
      actual_fifo.get(actual_tx);
      num_transactions++;

      if (expected_tx.compare(actual_tx)) begin
        m_matches++;
        // TODO: test case name param
        `uvm_info("SCBD", "Test Case: PASSED", UVM_LOW)
        expected_tx.print();
        actual_tx.print();
      end 
      else begin
        m_mismatches++;
        `uvm_info("SCBD", "Test Case: FAILED", UVM_LOW)
        expected_tx.print();
        actual_tx.print();
      end
    end
  endtask : run_phase

  // --- Report Phase --- //
  function void report_phase(uvm_phase phase);

  // TODO:

  endfunction

endclass : alu_imm_pipeline_scoreboard

`endif
