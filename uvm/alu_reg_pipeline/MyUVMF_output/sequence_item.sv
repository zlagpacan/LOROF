/*
  Module        : alu_reg_pipeline
  UMV Component : sequence_item
  Author        : 
*/

`ifndef ALU_REG_PIPELINE_SEQ_ITEM_SV
`define ALU_REG_PIPELINE_SEQ_ITEM_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Transaction --- //
class alu_reg_pipeline_sequence_item extends uvm_sequence_item;
  `uvm_object_utils(alu_reg_pipeline_sequence_item)

  // --- Control Signals --- //
  rand logic nRST;

  // --- Randomized Inputs --- //
  randc logic                                 issue_valid;
  randc logic [3:0]                           issue_op;
  randc logic                                 issue_A_forward;
  randc logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank;
  randc logic                                 issue_B_forward;
  randc logic [LOG_PRF_BANK_COUNT-1:0]        issue_B_bank;
  randc logic [LOG_PR_COUNT-1:0]              issue_dest_PR;
  randc logic [LOG_ROB_ENTRIES-1:0]           issue_ROB_index;
  randc logic                                 A_reg_read_ack;
  randc logic                                 A_reg_read_port;
  randc logic                                 B_reg_read_ack;
  randc logic                                 B_reg_read_port;
  randc logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank;
  randc logic [PRF_BANK_COUNT-1:0][31:0]      forward_data_by_bank;
  randc logic                                 WB_ready;
  
  // --- Outputs --- //
  logic                       issue_ready;
  logic                       WB_valid;
  logic [31:0]                WB_data;
  logic [LOG_PR_COUNT-1:0]    WB_PR;
  logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index;
  
  // --- Constraints --- //

  // --- Constructor --- //
  function new(string name = "alu_reg_pipeline_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_reg_pipeline_sequence_item

`endif