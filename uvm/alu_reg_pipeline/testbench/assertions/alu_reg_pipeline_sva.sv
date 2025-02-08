/*
  Module        : alu_reg_pipeline
  UMV Component : System Verilog Assertions
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_SVA_SV
`define ALU_REG_PIPELINE_SVA_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- SVA Checks --- //
module alu_reg_pipeline_sva (
    input logic                                 CLK,
    input logic                                 nRST,
    input logic                                 issue_valid,
    input logic [3:0]                           issue_op,
    input logic                                 issue_A_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank,
    input logic                                 issue_B_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_B_bank,
    input logic [LOG_PR_COUNT-1:0]              issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           issue_ROB_index,
    input logic                                 A_reg_read_ack,
    input logic                                 A_reg_read_port,
    input logic                                 B_reg_read_ack,
    input logic                                 B_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port,
    input logic [PRF_BANK_COUNT-1:0][31:0]      forward_data_by_bank,
    input logic                                 WB_ready,
    input logic                                 issue_ready,
    input logic                                 WB_valid,
    input logic [31:0]                          WB_data,
    input logic [LOG_PR_COUNT-1:0]              WB_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           WB_ROB_index
);

   // --- Test Case ALURP_0 Coverage --- //
  sequence DUT_reset;
    @(posedge CLK) ~nRST;
  endsequence
  
  property DUT_RESET_EVENT;
    @(posedge CLK) (DUT_reset);
  endproperty
  c_ALURP_0: cover property (DUT_RESET_EVENT);

  // --- Test Case ALURP_1 Coverage --- //
  sequence WB_stall;
    @(posedge CLK) ~WB_ready;
  endsequence

  property WB_STALL_EVENT;
    @(posedge CLK) disable iff (~nRST)
    (WB_stall);
  endproperty
  c_ALURP_1: cover property (WB_STALL_EVENT);

  // --- Test Case ALURP_2A Coverage --- //
  sequence ISS_stall;
    @(posedge CLK) ~issue_valid;
  endsequence

  property ISS_STALL_EVENT;
    @(posedge CLK) disable iff (~nRST)
    (ISS_stall);
  endproperty
  c_ALURP_2A: cover property (ISS_STALL_EVENT);

  // --- SVA Properties --- //

  // --- Test Case ALURP_1 Properties --- //
  property sva_WB_valid_stall;
    @(posedge CLK) disable iff (~nRST)
    (WB_stall) |=> (WB_valid === $past(WB_valid));
  endproperty

  property sva_WB_data_stall;
    @(posedge CLK) disable iff (~nRST)
    (WB_stall) |=> (WB_data === $past(WB_data));
  endproperty

  property sva_WB_PR_stall;
    @(posedge CLK) disable iff (~nRST)
    (WB_stall) |=> (WB_PR === $past(WB_PR));
  endproperty

  property sva_WB_ROB_index_stall;
    @(posedge CLK) disable iff (~nRST)
    (WB_stall) |=> (WB_ROB_index === $past(WB_ROB_index));
  endproperty

  // --- Test Case ALURP_2A Properties --- //
  property ISS_WB_PR_stall;
    @(posedge CLK) disable iff (~nRST)
    (ISS_stall) |-> ##[2:4] (WB_PR != 7'h1);
  endproperty

  property ISS_WB_ROB_stall;
    @(posedge CLK) disable iff (~nRST)
    (ISS_stall) |-> ##[2:4] (WB_ROB_index != 7'h1);
  endproperty
  
  // --- SVA Instances --- //

  // --- Test Case ALURP_1 Instances --- //
  a_ALURP_1_WB_VALID: assert property (sva_WB_valid_stall) begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_VALID : PASSED"), UVM_LOW)
  end else begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_VALID : FAILED"), UVM_LOW)
  end

  a_ALURP_1_WB_DATA: assert property (sva_WB_data_stall) begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_DATA : PASSED"), UVM_LOW)
  end else begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_DATA : FAILED"), UVM_LOW)
  end

  a_ALURP_1_WB_PR: assert property (sva_WB_PR_stall) begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_PR : PASSED"), UVM_LOW)
  end else begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_PR : FAILED"), UVM_LOW)
  end

  a_ALURP_1_WB_ROB: assert property (sva_WB_ROB_index_stall) begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_ROB : PASSED"), UVM_LOW)
  end else begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_1_WB_ROB : FAILED"), UVM_LOW)
  end

  // --- Test Case ALURP_2A Instances --- //
  a_ALURP_2A_WB_PR: assert property (ISS_WB_PR_stall) begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_2A_ISS_WB_PR_stall : PASSED"), UVM_LOW)
  end else begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_2A_ISS_WB_PR_stall : FAILED"), UVM_LOW)
  end

  a_ALURP_2A_WB_ROB_index: assert property (ISS_WB_ROB_stall) begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_2A_ISS_WB_ROB_index_stall : PASSED"), UVM_LOW)
  end else begin
    `uvm_info("sva", $sformatf("Test Case: ALURP_2A_ISS_WB_ROB_index_stall : FAILED"), UVM_LOW)
  end

endmodule

`endif