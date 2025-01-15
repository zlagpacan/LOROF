/*
  Module        : alu_pipeline
  UMV Component : sequence_item
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_SEQ_ITEM_SV
`define ALU_PIPELINE_SEQ_ITEM_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Transaction --- //
class alu_pipeline_sequence_item extends uvm_sequence_item;
  `uvm_object_utils(alu_pipeline_sequence_item)

  // --- Control Signals --- //
  rand logic nRST;

  // --- Randomized Inputs --- //
  randc logic                            valid_in;
  randc logic [3:0]                      op_in;
  randc logic                            is_imm_in;
  randc logic [31:0]                     imm_in;
  randc logic                            A_unneeded_in;
  randc logic                            A_forward_in;
  randc logic [LOG_PRF_BANK_COUNT-1:0]   A_bank_in;
  randc logic                            B_forward_in;
  randc logic [LOG_PRF_BANK_COUNT-1:0]   B_bank_in;
  randc logic [LOG_PR_COUNT-1:0]         dest_PR_in;
  randc logic                            A_reg_read_valid_in;
  randc logic                            B_reg_read_valid_in;
  randc logic [LOG_ROB_ENTRIES-1:0]      ROB_index_in;
  randc logic [PRF_BANK_COUNT-1:0][31:0] reg_read_data_by_bank_in;
  randc logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank_in;
  
  // --- Outputs --- //
  logic                       ready_out;
  logic                       WB_valid_out;
  logic [31:0]                WB_data_out;
  logic [LOG_PR_COUNT-1:0]    WB_PR_out;
  logic [LOG_ROB_ENTRIES-1:0] WB_ROB_index_out;
  
  // --- Constraints --- //

  // --- Constructor --- //
  function new(string name = "alu_pipeline_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_pipeline_sequence_item

`endif