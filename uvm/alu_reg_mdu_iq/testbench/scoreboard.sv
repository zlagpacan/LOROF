/*
  Module        : alu_reg_mdu_iq
  UMV Component : scoreboard
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_SCOREBOARD_SV
`define ALU_REG_MDU_IQ_SCOREBOARD_SV

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
class alu_reg_mdu_iq_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(alu_reg_mdu_iq_scoreboard)

  // --- Scoreboard Components --- //
  uvm_analysis_export#(alu_reg_mdu_iq_sequence_item) predicted_export; // to recieve result from predictor
  uvm_analysis_export#(alu_reg_mdu_iq_sequence_item) actual_export; // to recieve result from DUT
  uvm_tlm_analysis_fifo#(alu_reg_mdu_iq_sequence_item) predicted_fifo;
  uvm_tlm_analysis_fifo#(alu_reg_mdu_iq_sequence_item) actual_fifo;
  int m_matches, m_mismatches, num_transactions;

  // uvm_analysis_imp #(alu_reg_mdu_iq_sequence_item, alu_reg_mdu_iq_scoreboard) scoreboard_port;
  // alu_reg_mdu_iq_sequence_item transactions[$];

  // --- Constructor --- //
  function new(string name = "alu_reg_mdu_iq_scoreboard", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SCB_CLASS", "Inside Constructor", UVM_HIGH)
    m_matches = 0;
    m_mismatches = 0;
    num_transactions = 0;
  endfunction : new

  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SCB_CLASS", "Build Phase", UVM_HIGH)
   
    // --- TLM FIFO Ports --- //
    predicted_fifo = new("predicted_fifo", this);
    actual_fifo = new("actual_fifo", this);

    // --- Scoreboard Exports --- //
    predicted_export = new("predicted_export", this);
    actual_export = new("actual_export", this);

    // --- Scoreboard Port --- //
    // scoreboard_port = new("scoreboard_port", this);
  endfunction : build_phase

  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    // --- Connecting Fifos to Exports --- //
    predicted_export.connect(predicted_fifo.analysis_export);
    actual_export.connect(actual_fifo.analysis_export);
  endfunction


  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCB_CLASS", "Run Phase", UVM_HIGH)
   
    // --- Transaction Stack --- //
   

    forever begin
      alu_reg_mdu_iq_sequence_item predicted_tx;
      alu_reg_mdu_iq_sequence_item actual_tx;
      predicted_fifo.get(predicted_tx); // get value from fifo and put into predicted_tx
      actual_fifo.get(actual_tx); // get value from fifo and put into actual_tx
      num_transactions++;
      if (predicted_tx.compare(actual_tx)) begin
            m_matches++;
            uvm_report_info("SB", "Data match");
      end 
      else begin
            m_mismatches++;
            uvm_report_info("SB", "Error: Data mismatch");
            predicted_tx.print_transaction("predicted_tx");
            actual_tx.print_transaction("actual_tx");
            // `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", curr_trans.convert2str()), UVM_LOW)
            // `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", per_trans.convert2str()), UVM_LOW)
      end
    end
  endtask : run_phase

  function void report_phase(uvm_phase phase);
    uvm_report_info("Comparator", $sformatf("Matches:    %0d", m_matches));
    uvm_report_info("Comparator", $sformatf("Mismatches: %0d", m_mismatches));
    uvm_report_info("Num trans", $sformatf("Number of transactions: %0d", num_transactions));
  endfunction
endclass : alu_reg_mdu_iq_scoreboard

`endif