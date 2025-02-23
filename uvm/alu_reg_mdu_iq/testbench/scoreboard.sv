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
  uvm_analysis_imp #(alu_reg_mdu_iq_sequence_item, alu_reg_mdu_iq_scoreboard) scoreboard_port;
  alu_reg_mdu_iq_sequence_item transactions[$];
  int m_matches, m_mismatches, num_transactions;

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
   
    // --- Scoreboard Port --- //
    scoreboard_port = new("scoreboard_port", this);
    
  endfunction : build_phase

  // --- Write Transaction --- //
  function void write(alu_reg_mdu_iq_sequence_item item);
    transactions.push_back(item);
  endfunction : write 

  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCB_CLASS", "Run Phase", UVM_HIGH)
   
    // --- Transaction Stack --- //
    forever begin
      alu_reg_mdu_iq_sequence_item curr_tx;
      alu_reg_mdu_iq_sequence_item pred_tx;
      wait((transactions.size() != 0));
      num_transactions++;
      curr_tx = transactions.pop_front();
      pred_tx = alu_reg_mdu_iq_sequence_item::type_id::create("pred_tx");
      pred_tx.copy(curr_tx);
      compare(pred_tx);

      if (per_trans.compare(curr_trans)) begin
            m_matches++;
            uvm_report_info("SB", "Data match");
      end 
      else begin
            m_mismatches++;
            uvm_report_info("SB", "Error: Data mismatch");
            `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", curr_trans.convert2str()), UVM_LOW)
            `uvm_info(get_type_name(), $sformatf("Monitor found packet %s", per_trans.convert2str()), UVM_LOW)

      end

    end
    
  endtask : run_phase

  // --- Compare --- //
  task predict(alu_reg_mdu_iq_sequence_item pred_tx);

  if(pred_tx.nRST == 0) begin
    pred_tx.dispatch_ack_by_way = '0;  
    pred_tx.issue_alu_reg_valid = '0;
    pred_tx.issue_alu_reg_op = '0;
    pred_tx.issue_alu_reg_A_forward = '0;
    pred_tx.issue_alu_reg_A_bank = '0;
    pred_tx.issue_alu_reg_B_forward = '0;
    pred_tx.issue_alu_reg_B_bank = '0;
    pred_tx.issue_alu_reg_dest_PR = '0;
    pred_tx.issue_alu_reg_ROB_index = '0;
    pred_tx.PRF_alu_reg_req_A_valid = '0;
    pred_tx.PRF_alu_reg_req_A_PR = '0;
    pred_tx.PRF_alu_reg_req_B_valid = '0;
    pred_tx.PRF_alu_reg_req_B_PR = '0;
    pred_tx.issue_mdu_valid = '0;
    pred_tx.issue_mdu_op = '0;
    pred_tx.issue_mdu_A_forward = '0;
    pred_tx.issue_mdu_A_bank = '0;
    pred_tx.issue_mdu_B_forward = '0;
    pred_tx.issue_mdu_B_bank = '0;
    pred_tx.issue_mdu_dest_PR = '0;
    pred_tx.issue_mdu_ROB_index = '0;
    pred_tx.PRF_mdu_req_A_valid = '0;
    pred_tx.PRF_mdu_req_A_PR = '0;
    pred_tx.PRF_mdu_req_B_valid = '0;
    pred_tx.PRF_mdu_req_B_PR = '0;
 end
  // User fills in 

  // if(curr_tx.nRST == 0) begin
  //   uvm_report_info("CHECK RESET");
  //   if(curr_tx.dispatch_ack_by_way != '0) begin
  //     uvm_report_info("COMPARE", $sformatf("Test Case: RESET0 : FAILED, curr_tx.dispatch_ack_by_way == %0d",curr_tx.dispatch_ack_by_way), UVM_NONE);
  //     m_mismatches++
  //   end
  //   else begin
  //     uvm_report_info("COMPARE", $sformatf("Test Case: RESET0 : PASSED, curr_tx.dispatch_ack_by_way == %0d",curr_tx.dispatch_ack_by_way), UVM_NONE);
  //     m_mismatches++
  //   end
  // end

  endtask : predict

endclass : alu_reg_mdu_iq_scoreboard

`endif