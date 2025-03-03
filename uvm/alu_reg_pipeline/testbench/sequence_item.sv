/*
  Module        : alu_reg_pipeline
  UMV Component : sequence_item
  Author        : Adam Keith
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
  rand logic                                  nRST;

  // --- Randomized Inputs --- //
  rand  logic                                 issue_valid;
  randc logic [3:0]                           issue_op;
  randc logic                                 issue_A_forward;
  randc logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank;
  randc logic                                 issue_A_is_zero;
  randc logic                                 issue_B_forward;
  randc logic [LOG_PRF_BANK_COUNT-1:0]        issue_B_bank;
  randc logic [LOG_PR_COUNT-1:0]              issue_dest_PR;
  randc logic [LOG_ROB_ENTRIES-1:0]           issue_ROB_index;
  randc logic                                 A_reg_read_ack;
  randc logic                                 A_reg_read_port;
  randc logic                                 B_reg_read_ack;
  randc logic                                 B_reg_read_port;
  rand  logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port;
  rand  logic [PRF_BANK_COUNT-1:0][31:0]      forward_data_by_bank;
  rand  logic                                 WB_ready;
  
  // --- Outputs --- //
  logic                                       issue_ready;
  logic                                       WB_valid;
  logic [31:0]                                WB_data;
  logic [LOG_PR_COUNT-1:0]                    WB_PR;
  logic [LOG_ROB_ENTRIES-1:0]                 WB_ROB_index;
  
  // --- Constraints --- //
  /*
    The idea is to have the base seq item be the 'ideal' sequence
      - 1 op per cycle
  */
  constraint nRST_ideal            { soft nRST            == 1'b1; }
  constraint issue_valid_ideal     { soft issue_valid     == 1'b1; }
  constraint issue_A_forward_ideal { soft issue_A_forward == 1'b1; }
  constraint issue_B_forward_ideal { soft issue_B_forward == 1'b1; }
  // TODO: clarify with Zach
  constraint issue_B_forward_ideal { soft issue_A_is_zero == 1'b0; }

  // Temp Void - Dist constraints won't override
  // constraint WB_ready_ideal        { soft WB_ready        == 1'b1; }

  // --- Constructor --- //
  function new(string name = "alu_reg_pipeline_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_reg_pipeline_sequence_item

`endif