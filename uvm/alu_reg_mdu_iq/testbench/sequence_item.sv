/*
  Module        : alu_reg_mdu_iq
  UMV Component : sequence_item
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_SEQ_ITEM_SV
`define ALU_REG_MDU_IQ_SEQ_ITEM_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Transaction --- //
class alu_reg_mdu_iq_sequence_item extends uvm_sequence_item;
  `uvm_object_utils(alu_reg_mdu_iq_sequence_item)

  // --- Control Signals --- //
  rand logic nRST;

  // --- Randomized Inputs --- //
  randc logic [3:0]                                                     dispatch_attempt_by_way;
  randc logic [3:0]                                                     dispatch_valid_alu_reg_by_way;
  randc logic [3:0]                                                     dispatch_valid_mdu_by_way;
  randc logic [3:0][3:0]                                                dispatch_op_by_way;
  randc logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_A_PR_by_way;
  randc logic [3:0]                                                     dispatch_A_ready_by_way;
  randc logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_B_PR_by_way;
  randc logic [3:0]                                                     dispatch_B_ready_by_way;
  randc logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_dest_PR_by_way;
  randc logic [3:0][LOG_ROB_ENTRIES-1:0]                                dispatch_ROB_index_by_way;
  randc logic                                                           alu_reg_pipeline_ready;
  randc logic                                                           mdu_pipeline_ready;
  randc logic [PRF_BANK_COUNT-1:0]                                      WB_bus_valid_by_bank;
  randc logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;
  
  // --- Outputs --- //
  logic [3:0]                    dispatch_ack_by_way;
  logic                          issue_alu_reg_valid;
  logic [3:0]                    issue_alu_reg_op;
  logic                          issue_alu_reg_A_forward;
  logic [LOG_PRF_BANK_COUNT-1:0] issue_alu_reg_A_bank;
  logic                          issue_alu_reg_B_forward;
  logic [LOG_PRF_BANK_COUNT-1:0] issue_alu_reg_B_bank;
  logic [LOG_PR_COUNT-1:0]       issue_alu_reg_dest_PR;
  logic [LOG_ROB_ENTRIES-1:0]    issue_alu_reg_ROB_index;
  logic                          PRF_alu_reg_req_A_valid;
  logic [LOG_PR_COUNT-1:0]       PRF_alu_reg_req_A_PR;
  logic                          PRF_alu_reg_req_B_valid;
  logic [LOG_PR_COUNT-1:0]       PRF_alu_reg_req_B_PR;
  logic                          issue_mdu_valid;
  logic [3:0]                    issue_mdu_op;
  logic                          issue_mdu_A_forward;
  logic [LOG_PRF_BANK_COUNT-1:0] issue_mdu_A_bank;
  logic                          issue_mdu_B_forward;
  logic [LOG_PRF_BANK_COUNT-1:0] issue_mdu_B_bank;
  logic [LOG_PR_COUNT-1:0]       issue_mdu_dest_PR;
  logic [LOG_ROB_ENTRIES-1:0]    issue_mdu_ROB_index;
  logic                          PRF_mdu_req_A_valid;
  logic [LOG_PR_COUNT-1:0]       PRF_mdu_req_A_PR;
  logic                          PRF_mdu_req_B_valid;
  logic [LOG_PR_COUNT-1:0]       PRF_mdu_req_B_PR;
  
  // --- Constraints --- //

  // --- Constructor --- //
  function new(string name = "alu_reg_mdu_iq_sequence_item");
    super.new(name);
  endfunction : new

endclass : alu_reg_mdu_iq_sequence_item

`endif