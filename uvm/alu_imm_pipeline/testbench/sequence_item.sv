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

  // --- UVM Debug Macro --- //
  `uvm_object_utils_begin(transaction)
    // --- Reset --- //
    `uvm_field_int(nRST,            UVM_NOCOMPARE)
    // --- Inputs --- //
    `uvm_field_int(issue_valid,     UVM_NOCOMPARE)
    `uvm_field_int(issue_op,        UVM_NOCOMPARE)
    `uvm_field_int(issue_A_forward, UVM_NOCOMPARE)
    `uvm_field_int(issue_A_bank,    UVM_NOCOMPARE)
    `uvm_field_int(issue_A_is_zero, UVM_NOCOMPARE)
    `uvm_field_int(issue_B_forward, UVM_NOCOMPARE)
    `uvm_field_int(issue_B_bank,    UVM_NOCOMPARE)
    `uvm_field_int(issue_dest_PR,   UVM_NOCOMPARE)
    `uvm_field_int(issue_ROB_index, UVM_NOCOMPARE)
    `uvm_field_int(A_reg_read_ack,  UVM_NOCOMPARE)
    `uvm_field_int(A_reg_read_port, UVM_NOCOMPARE)
    `uvm_field_int(B_reg_read_ack,  UVM_NOCOMPARE)
    `uvm_field_int(B_reg_read_port, UVM_NOCOMPARE)
    `uvm_field_int(WB_ready,        UVM_NOCOMPARE)
    // --- Inputs : Arrays --- //
    `uvm_field_sarray_int(reg_read_data_by_bank_by_port, UVM_NOCOMPARE)
    `uvm_field_sarray_int(forward_data_by_bank,          UVM_NOCOMPARE)
    // --- Outputs --- //
    `uvm_field_int(issue_ready,     UVM_DEFAULT)
    `uvm_field_int(WB_valid,        UVM_DEFAULT)
    `uvm_field_int(WB_data,         UVM_DEFAULT)
    `uvm_field_int(WB_PR,           UVM_DEFAULT)
    `uvm_field_int(WB_ROB_index,    UVM_DEFAULT)
  `uvm_object_utils_end
  
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

  // --- Constructor --- //
  function new(string name = "alu_imm_pipeline_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_imm_pipeline_sequence_item

`endif