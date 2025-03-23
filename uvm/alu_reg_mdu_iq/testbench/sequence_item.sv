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
  rand logic [3:0]                                                     dispatch_A_is_zero_by_way;
  rand logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_B_PR_by_way;
  rand logic [3:0]                                                     dispatch_B_ready_by_way;
  rand logic [3:0]                                                     dispatch_B_is_zero_by_way;
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
  logic                          issue_alu_reg_A_is_zero;
  logic [LOG_PRF_BANK_COUNT-1:0] issue_alu_reg_A_bank;
  logic                          issue_alu_reg_B_forward;
  logic                          issue_alu_reg_B_is_zero;
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
  logic                          issue_mdu_A_is_zero;
  logic [LOG_PRF_BANK_COUNT-1:0] issue_mdu_A_bank;
  logic                          issue_mdu_B_forward;
  logic                          issue_mdu_B_is_zero;
  logic [LOG_PRF_BANK_COUNT-1:0] issue_mdu_B_bank;
  logic [LOG_PR_COUNT-1:0]       issue_mdu_dest_PR;
  logic [LOG_ROB_ENTRIES-1:0]    issue_mdu_ROB_index;
  logic                          PRF_mdu_req_A_valid;
  logic [LOG_PR_COUNT-1:0]       PRF_mdu_req_A_PR;
  logic                          PRF_mdu_req_B_valid;
  logic [LOG_PR_COUNT-1:0]       PRF_mdu_req_B_PR;
  
  
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    alu_reg_mdu_iq_sequence_item rhs_tx;
    if (!$cast(rhs_tx, rhs)) return 0; // Type check

    return (
        (dispatch_ack_by_way === rhs_tx.dispatch_ack_by_way) &&
        (issue_alu_reg_valid === rhs_tx.issue_alu_reg_valid) &&
        (issue_alu_reg_op === rhs_tx.issue_alu_reg_op) &&
        (issue_alu_reg_A_forward === rhs_tx.issue_alu_reg_A_forward) &&
        (issue_alu_reg_A_is_zero === rhs_tx.issue_alu_reg_A_is_zero) &&
        (issue_alu_reg_A_bank === rhs_tx.issue_alu_reg_A_bank) &&
        (issue_alu_reg_B_forward === rhs_tx.issue_alu_reg_B_forward) &&
        (issue_alu_reg_B_is_zero === rhs_tx.issue_alu_reg_B_is_zero) &&
        (issue_alu_reg_B_bank === rhs_tx.issue_alu_reg_B_bank) &&
        (issue_alu_reg_dest_PR === rhs_tx.issue_alu_reg_dest_PR) &&
        (issue_alu_reg_ROB_index === rhs_tx.issue_alu_reg_ROB_index) &&
        (PRF_alu_reg_req_A_valid === rhs_tx.PRF_alu_reg_req_A_valid) &&
        (PRF_alu_reg_req_A_PR === rhs_tx.PRF_alu_reg_req_A_PR) &&
        (PRF_alu_reg_req_B_valid === rhs_tx.PRF_alu_reg_req_B_valid) &&
        (PRF_alu_reg_req_B_PR === rhs_tx.PRF_alu_reg_req_B_PR) &&
        (issue_mdu_valid === rhs_tx.issue_mdu_valid) &&
        (issue_mdu_op === rhs_tx.issue_mdu_op) &&
        (issue_mdu_A_forward === rhs_tx.issue_mdu_A_forward) &&
        (issue_mdu_A_is_zero === rhs_tx.issue_mdu_A_is_zero) &&
        (issue_mdu_A_bank === rhs_tx.issue_mdu_A_bank) &&
        (issue_mdu_B_forward === rhs_tx.issue_mdu_B_forward) &&
        (issue_mdu_B_is_zero === rhs_tx.issue_mdu_B_is_zero) &&
        (issue_mdu_B_bank === rhs_tx.issue_mdu_B_bank) &&
        (issue_mdu_dest_PR === rhs_tx.issue_mdu_dest_PR) &&
        (issue_mdu_ROB_index === rhs_tx.issue_mdu_ROB_index) &&
        (PRF_mdu_req_A_valid === rhs_tx.PRF_mdu_req_A_valid) &&
        (PRF_mdu_req_A_PR === rhs_tx.PRF_mdu_req_A_PR) &&
        (PRF_mdu_req_B_valid === rhs_tx.PRF_mdu_req_B_valid) &&
        (PRF_mdu_req_B_PR === rhs_tx.PRF_mdu_req_B_PR)
    );
  endfunction


  virtual function void copy(uvm_object rhs);
    alu_reg_mdu_iq_sequence_item tr;
    if (!$cast(tr, rhs)) begin
      `uvm_error("COPY", "Cast failed in copy() method")
      return;
    end
    
    super.copy(rhs); // Copy base class fields
    
    // Manually copy each field
    this.way = tr.way;
    this.nRST = tr.nRST;
    this.dispatch_attempt_by_way = tr.dispatch_attempt_by_way;
    this.dispatch_valid_alu_reg_by_way = tr.dispatch_valid_alu_reg_by_way;
    this.dispatch_valid_mdu_by_way = tr.dispatch_valid_mdu_by_way;
    this.dispatch_op_by_way = tr.dispatch_op_by_way;
    this.dispatch_A_PR_by_way = tr.dispatch_A_PR_by_way;
    this.dispatch_A_ready_by_way = tr.dispatch_A_ready_by_way;
    this.dispatch_A_is_zero_by_way = tr.dispatch_A_is_zero_by_way;
    this.dispatch_B_PR_by_way = tr.dispatch_B_PR_by_way;
    this.dispatch_B_ready_by_way = tr.dispatch_B_ready_by_way;
    this.dispatch_B_is_zero_by_way = tr.dispatch_B_is_zero_by_way;
    this.dispatch_dest_PR_by_way = tr.dispatch_dest_PR_by_way;
    this.dispatch_ROB_index_by_way = tr.dispatch_ROB_index_by_way;
    this.alu_reg_pipeline_ready = tr.alu_reg_pipeline_ready;
    this.mdu_pipeline_ready = tr.mdu_pipeline_ready;
    this.WB_bus_valid_by_bank = tr.WB_bus_valid_by_bank;
    this.WB_bus_upper_PR_by_bank = tr.WB_bus_upper_PR_by_bank;
    this.dispatch_ack_by_way = tr.dispatch_ack_by_way;
    this.issue_alu_reg_valid = tr.issue_alu_reg_valid;
    this.issue_alu_reg_op = tr.issue_alu_reg_op;
    this.issue_alu_reg_A_forward = tr.issue_alu_reg_A_forward;
    this.issue_alu_reg_A_is_zero = tr.issue_alu_reg_A_is_zero;
    this.issue_alu_reg_A_bank = tr.issue_alu_reg_A_bank;
    this.issue_alu_reg_B_forward = tr.issue_alu_reg_B_forward;
    this.issue_alu_reg_B_is_zero = tr.issue_alu_reg_B_is_zero;
    this.issue_alu_reg_B_bank = tr.issue_alu_reg_B_bank;
    this.issue_alu_reg_dest_PR = tr.issue_alu_reg_dest_PR;
    this.issue_alu_reg_ROB_index = tr.issue_alu_reg_ROB_index;
    this.PRF_alu_reg_req_A_valid = tr.PRF_alu_reg_req_A_valid;
    this.PRF_alu_reg_req_A_PR = tr.PRF_alu_reg_req_A_PR;
    this.PRF_alu_reg_req_B_valid = tr.PRF_alu_reg_req_B_valid;
    this.PRF_alu_reg_req_B_PR = tr.PRF_alu_reg_req_B_PR;
    this.issue_mdu_valid = tr.issue_mdu_valid;
    this.issue_mdu_op = tr.issue_mdu_op;
    this.issue_mdu_A_forward = tr.issue_mdu_A_forward;
    this.issue_mdu_A_is_zero = tr.issue_mdu_A_is_zero;
    this.issue_mdu_A_bank = tr.issue_mdu_A_bank;
    this.issue_mdu_B_forward = tr.issue_mdu_B_forward;
    this.issue_mdu_B_is_zero = tr.issue_mdu_B_is_zero;
    this.issue_mdu_B_bank = tr.issue_mdu_B_bank;
    this.issue_mdu_dest_PR = tr.issue_mdu_dest_PR;
    this.issue_mdu_ROB_index = tr.issue_mdu_ROB_index;
    this.PRF_mdu_req_A_valid = tr.PRF_mdu_req_A_valid;
    this.PRF_mdu_req_A_PR = tr.PRF_mdu_req_A_PR;
    this.PRF_mdu_req_B_valid = tr.PRF_mdu_req_B_valid;
    this.PRF_mdu_req_B_PR = tr.PRF_mdu_req_B_PR;
  endfunction
  // hiiiii
  // TEST GIT
  
  function void print_transaction(string x);
    $display("---- %s Details ---- at time %t",x, $time);
  
    // --- Control Signals ---
    $display("nRST: %b", nRST);
  
    if(x == "predicted_tx") begin
    // --- Randomized Inputs ---
    foreach (dispatch_attempt_by_way[i])
      $display("dispatch_attempt_by_way[%0d]: %b", i, dispatch_attempt_by_way[i]);
  
    foreach (dispatch_valid_alu_reg_by_way[i])
      $display("dispatch_valid_alu_reg_by_way[%0d]: %b", i, dispatch_valid_alu_reg_by_way[i]);
  
    foreach (dispatch_valid_mdu_by_way[i])
      $display("dispatch_valid_mdu_by_way[%0d]: %b", i, dispatch_valid_mdu_by_way[i]);
  
    foreach (dispatch_op_by_way[i])
      $display("dispatch_op_by_way[%0d]: %h", i, dispatch_op_by_way[i]);
  
    foreach (dispatch_A_PR_by_way[i])
      $display("dispatch_A_PR_by_way[%0d]: %h", i, dispatch_A_PR_by_way[i]);
  
    foreach (dispatch_A_ready_by_way[i])
      $display("dispatch_A_ready_by_way[%0d]: %b", i, dispatch_A_ready_by_way[i]);

    foreach (dispatch_A_is_zero_by_way[i])
      $display("dispatch_A_is_zero_by_way[%0d]: %b", i, dispatch_A_is_zero_by_way[i]);
  
    foreach (dispatch_B_PR_by_way[i])
      $display("dispatch_B_PR_by_way[%0d]: %h", i, dispatch_B_PR_by_way[i]);
  
    foreach (dispatch_B_ready_by_way[i])
      $display("dispatch_B_ready_by_way[%0d]: %b", i, dispatch_B_ready_by_way[i]);

    foreach (dispatch_B_is_zero_by_way[i])
      $display("dispatch_B_is_zero_by_way[%0d]: %b", i, dispatch_B_is_zero_by_way[i]);
  
    foreach (dispatch_dest_PR_by_way[i])
      $display("dispatch_dest_PR_by_way[%0d]: %h", i, dispatch_dest_PR_by_way[i]);
  
    foreach (dispatch_ROB_index_by_way[i])
      $display("dispatch_ROB_index_by_way[%0d]: %h", i, dispatch_ROB_index_by_way[i]);
  
    $display("alu_reg_pipeline_ready: %b", alu_reg_pipeline_ready);
    $display("mdu_pipeline_ready: %b", mdu_pipeline_ready);
  
    foreach (WB_bus_valid_by_bank[i])
      $display("WB_bus_valid_by_bank[%0d]: %b", i, WB_bus_valid_by_bank[i]);
  
    foreach (WB_bus_upper_PR_by_bank[i])
      $display("WB_bus_upper_PR_by_bank[%0d]: %h", i, WB_bus_upper_PR_by_bank[i]);
    end
    // --- Outputs ---

    $display("Outputs");
  
    foreach (dispatch_ack_by_way[i])
      $display("dispatch_ack_by_way[%0d]: %b", i, dispatch_ack_by_way[i]);
  
    $display("issue_alu_reg_valid: %b", issue_alu_reg_valid);
    $display("issue_alu_reg_op: %h", issue_alu_reg_op);
    $display("issue_alu_reg_A_forward: %b", issue_alu_reg_A_forward);
    $display("issue_alu_reg_A_is_zero: %b", issue_alu_reg_A_is_zero);
    $display("issue_alu_reg_A_bank: %h", issue_alu_reg_A_bank);
    $display("issue_alu_reg_B_forward: %b", issue_alu_reg_B_forward);
    $display("issue_alu_reg_B_is_zero: %b", issue_alu_reg_B_is_zero);
    $display("issue_alu_reg_B_bank: %h", issue_alu_reg_B_bank);
    $display("issue_alu_reg_dest_PR: %h", issue_alu_reg_dest_PR);
    $display("issue_alu_reg_ROB_index: %h", issue_alu_reg_ROB_index);
  
    $display("PRF_alu_reg_req_A_valid: %b", PRF_alu_reg_req_A_valid);
    $display("PRF_alu_reg_req_A_PR: %h", PRF_alu_reg_req_A_PR);
    $display("PRF_alu_reg_req_B_valid: %b", PRF_alu_reg_req_B_valid);
    $display("PRF_alu_reg_req_B_PR: %h", PRF_alu_reg_req_B_PR);
  
    $display("issue_mdu_valid: %b", issue_mdu_valid);
    $display("issue_mdu_op: %h", issue_mdu_op);
    $display("issue_mdu_A_forward: %b", issue_mdu_A_forward);
    $display("issue_mdu_A_is_zero: %b", issue_mdu_A_is_zero);
    $display("issue_mdu_A_bank: %h", issue_mdu_A_bank);
    $display("issue_mdu_B_forward: %b", issue_mdu_B_forward);
    $display("issue_mdu_B_is_zero: %b", issue_mdu_B_is_zero);
    $display("issue_mdu_B_bank: %h", issue_mdu_B_bank);
    $display("issue_mdu_dest_PR: %h", issue_mdu_dest_PR);
    $display("issue_mdu_ROB_index: %h", issue_mdu_ROB_index);
  
    $display("PRF_mdu_req_A_valid: %b", PRF_mdu_req_A_valid);
    $display("PRF_mdu_req_A_PR: %h", PRF_mdu_req_A_PR);
    $display("PRF_mdu_req_B_valid: %b", PRF_mdu_req_B_valid);
    $display("PRF_mdu_req_B_PR: %h", PRF_mdu_req_B_PR);
  
    $display("---- End of Transaction ----\n");
  endfunction

  
  
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