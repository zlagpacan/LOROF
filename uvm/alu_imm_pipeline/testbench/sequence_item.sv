/*
  Module        : alu_imm_pipeline
  UMV Component : sequence_item
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_SEQ_ITEM_SV
`define ALU_IMM_PIPELINE_SEQ_ITEM_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Transaction --- //
class alu_imm_pipeline_sequence_item extends uvm_sequence_item;
  `uvm_object_utils(alu_imm_pipeline_sequence_item)

  // --- Control Signals --- //
  rand logic nRST;

  // --- Randomized Inputs --- //
  randc logic                                 issue_valid;
  randc logic [3:0]                           issue_op;
  randc logic [11:0]                          issue_imm12;
  randc logic                                 issue_A_forward;
  randc logic                                 issue_A_is_zero;
  randc logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank;
  randc logic [LOG_PR_COUNT-1:0]              issue_dest_PR;
  randc logic [LOG_ROB_ENTRIES-1:0]           issue_ROB_index;
  randc logic                                 A_reg_read_ack;
  randc logic                                 A_reg_read_port;
  rand  logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port;
  rand  logic [PRF_BANK_COUNT-1:0][31:0]      forward_data_by_bank;
  randc logic                                 WB_ready;
  
  // --- Outputs --- //
  logic                       issue_ready;
  logic                       WB_valid;
  logic [31:0]                WB_data;
  logic [LOG_PR_COUNT-1:0]    WB_PR;
  logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index;
  
  // --- Constraints --- //
  /*
    The idea is to have the base seq item be the 'ideal' sequence
      - 1 op per cycle
  */
  constraint nRST_ideal            { soft nRST            == 1'b1; }
  constraint issue_valid_ideal     { soft issue_valid     == 1'b1; }
  constraint issue_A_forward_ideal { soft issue_A_forward == 1'b1; }

  // Temp Void - Dist constraints won't override
  // constraint WB_ready_ideal        { soft WB_ready        == 1'b1; }

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    alu_imm_pipeline_sequence_item rhs_tx;
    if (!$cast(rhs_tx, rhs)) return 0; // Type check

    return (
        // (issue_valid === rhs_tx.issue_valid) &&
        // (issue_op === rhs_tx.issue_op) &&
        // (issue_imm12 === rhs_tx.issue_imm12) &&
        // (issue_A_forward === rhs_tx.issue_A_forward) &&
        // (issue_A_is_zero === rhs_tx.issue_A_is_zero) &&
        // (issue_A_bank === rhs_tx.issue_A_bank) &&
        // (issue_dest_PR === rhs_tx.issue_dest_PR) &&
        // (issue_ROB_index === rhs_tx.issue_ROB_index) &&
        // (A_reg_read_ack === rhs_tx.A_reg_read_ack) &&
        // (A_reg_read_port === rhs_tx.A_reg_read_port) &&
        // (reg_read_data_by_bank_by_port === rhs_tx.reg_read_data_by_bank_by_port) &&
        // (forward_data_by_bank === rhs_tx.forward_data_by_bank) &&
        // (WB_ready === rhs_tx.WB_ready) &&
        (issue_ready === rhs_tx.issue_ready) &&
        (WB_valid === rhs_tx.WB_valid) &&
        (WB_data === rhs_tx.WB_data) &&
        (WB_PR === rhs_tx.WB_PR) &&
        (WB_ROB_index === rhs_tx.WB_ROB_index)
    );

  endfunction

  virtual function void copy(uvm_object rhs);
    alu_imm_pipeline_sequence_item tr;
    if (!$cast(tr, rhs)) begin
      `uvm_error("COPY", "Cast failed in copy() method")
      return;
    end
    
    super.copy(rhs); // Copy base class fields
    
    this.nRST = tr.nRST;
    this.issue_valid = tr.issue_valid;
    this.issue_op = tr.issue_op;
    this.issue_imm12 = tr.issue_imm12;
    this.issue_A_forward = tr.issue_A_forward;
    this.issue_A_is_zero = tr.issue_A_is_zero;
    this.issue_A_bank = tr.issue_A_bank;
    this.issue_dest_PR = tr.issue_dest_PR;
    this.issue_ROB_index = tr.issue_ROB_index;
    this.A_reg_read_ack = tr.A_reg_read_ack;
    this.A_reg_read_port = tr.A_reg_read_port;
    this.reg_read_data_by_bank_by_port = tr.reg_read_data_by_bank_by_port;
    this.forward_data_by_bank = tr.forward_data_by_bank;
    this.WB_ready = tr.WB_ready;
    this.issue_ready = tr.issue_ready;
    this.WB_valid = tr.WB_valid;
    this.WB_data = tr.WB_data;
    this.WB_PR = tr.WB_PR;
    this.WB_ROB_index = tr.WB_ROB_index;
  endfunction


  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_imm_pipeline_sequence_item

`endif