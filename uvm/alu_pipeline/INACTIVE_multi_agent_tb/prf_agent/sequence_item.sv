/*
  Module        : alu_pipeline_prf
  UMV Component : sequence_item
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_PRF_SEQ_ITEM_SV
`define ALU_PIPELINE_PRF_SEQ_ITEM_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.svh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Transaction --- //
class alu_pipeline_prf_sequence_item extends uvm_sequence_item;
  `uvm_object_utils(alu_pipeline_prf_sequence_item)

  // --- Randomized Inputs --- //
  randc logic                            A_reg_read_valid_in;
  randc logic                            B_reg_read_valid_in;
  randc logic [LOG_ROB_ENTRIES-1:0]      ROB_index_in;
  randc logic [PRF_BANK_COUNT-1:0][31:0] reg_read_data_by_bank_in;
  randc logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank_in;
  
  // --- Outputs --- //
  logic                                  WB_valid_out;
  logic [31:0]                           WB_data_out;
  logic [LOG_PR_COUNT-1:0]               WB_PR_out;
  logic [LOG_ROB_ENTRIES-1:0]            WB_ROB_index_out;   
  
  // --- Constraints --- //

  // --- Constructor --- //
  function new(string name = "alu_pipeline_prf_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_pipeline_prf_sequence_item

`endif