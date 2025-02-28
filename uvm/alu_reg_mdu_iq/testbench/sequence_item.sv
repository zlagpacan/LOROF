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

  rand logic [1:0] way; // for functions below 
  // --- Control Signals --- //
  rand logic nRST;

  // --- Randomized Inputs --- //
  rand logic [3:0]                                                     dispatch_attempt_by_way;
  rand logic [3:0]                                                     dispatch_valid_alu_reg_by_way;
  rand logic [3:0]                                                     dispatch_valid_mdu_by_way;
  rand logic [3:0][3:0]                                                dispatch_op_by_way;
  rand logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_A_PR_by_way;
  rand logic [3:0]                                                     dispatch_A_ready_by_way;
  rand logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_B_PR_by_way;
  rand logic [3:0]                                                     dispatch_B_ready_by_way;
  rand logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_dest_PR_by_way;
  rand logic [3:0][LOG_ROB_ENTRIES-1:0]                                dispatch_ROB_index_by_way;
  rand logic                                                           alu_reg_pipeline_ready;
  rand logic                                                           mdu_pipeline_ready;
  rand logic [PRF_BANK_COUNT-1:0]                                      WB_bus_valid_by_bank;
  rand logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;
  
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
  constraint valid_dispatch {
    // dispatch_attempt_by_way solve before {dispatch_valid_alu_reg_by_way, dispatch_valid_mdu_by_way};
    (dispatch_valid_alu_reg_by_way | dispatch_valid_mdu_by_way) <= dispatch_attempt_by_way;
  }


  //TODO MAY NEED TO ADD OPCODE CONSTRAINTS


  // --- Constructor --- //
  function new(string name = "alu_reg_mdu_iq_sequence_item");
    super.new(name);
  endfunction : new


endclass : alu_reg_mdu_iq_sequence_item

// // May use may not will see
//   virtual function void add();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0000;
//   endfunction

//   virtual function void sub ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b1000;
//   endfunction

//  virtual function sll void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0001;
//   endfunction

//  virtual function slt void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0010;
//   endfunction

//  virtual function sltu void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0011;
//   endfunction

//  virtual function xor void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0100;
//   endfunction

//  virtual function srl void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0101;
//   endfunction

//  virtual function sra void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b1101;
//   endfunction

//  virtual function or void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0110;
//   endfunction

//  virtual function and void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b1;
//     dispatch_valid_mdu_by_way[way] = 1'b0;
//     dispatch_op_by_way[way] = 4'b0111;
//   endfunction

//   // MUL DIV FUNCTIONS
//  virtual function MUL void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0000;
//   endfunction

//  virtual function MULH void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0001;
//   endfunction

//  virtual function MULHSU void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0010;
//   endfunction

//  virtual function MULHU void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0011;
//   endfunction
  
//  virtual function DIV void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0100;
//   endfunction

//  virtual function DIVU void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0101;
//   endfunction

//  virtual function REM void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0110;
//   endfunction

//  virtual function REMU void ();
//     dispatch_valid_alu_reg_by_way[way] = 1'b0;
//     dispatch_valid_mdu_by_way[way] = 1'b1;
//     dispatch_op_by_way[way] = 4'b0111;
//   endfunction

`endif