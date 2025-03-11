/*
  Module        : alu_imm_pipeline
  UMV Component : System Verilog Assertions
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_SVA_SV
`define ALU_IMM_PIPELINE_SVA_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- SVA Checks --- //
module alu_imm_pipeline_sva (
    input logic                                 CLK,
    input logic                                 nRST,
    input logic                                 issue_valid,
    input logic [3:0]                           issue_op,
    input logic [11:0]                          issue_imm12,
    input logic                                 issue_A_forward,
    input logic                                 issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank,
    input logic [LOG_PR_COUNT-1:0]              issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           issue_ROB_index,
    input logic                                 A_reg_read_ack,
    input logic                                 A_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port,
    input logic [PRF_BANK_COUNT-1:0][31:0]      forward_data_by_bank,
    input logic                                 WB_ready,
    input logic                                 issue_ready,
    input logic                                 WB_valid,
    input logic [31:0]                          WB_data,
    input logic [LOG_PR_COUNT-1:0]              WB_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           WB_ROB_index
);

  // --- Debug --- //
  string seperator = "------------------------------------------------------------------------------------------------------------------------------";

  // --- Test Case Coverage --- //
  // sequence DUT_reset;
  //   @(posedge CLK) ~nRST;
  // endsequence
  
  // property DUT_RESET_EVENT;
  //   @(posedge CLK) (DUT_reset);
  // endproperty
  // c_ALURP_0: cover property (DUT_RESET_EVENT);

  // --- SVA Properties --- //

  // --- Test Case ALURP_1 Properties --- //
  property tc_WB_valid_stall;
    @(posedge CLK) disable iff (~nRST)
    (~WB_ready) |=> (WB_valid === $past(WB_valid));
  endproperty

  property tc_WB_data_stall;
    @(posedge CLK) disable iff (~nRST)
    (~WB_ready) |=> (WB_data === $past(WB_data));
  endproperty

  property tc_WB_PR_stall;
    @(posedge CLK) disable iff (~nRST)
    (~WB_ready) |=> (WB_PR === $past(WB_PR));
  endproperty

  property tc_WB_ROB_index_stall;
    @(posedge CLK) disable iff (~nRST)
    (~WB_ready) |=> (WB_ROB_index === $past(WB_ROB_index));
  endproperty

  // --- Test Case ALURP_1 Instances --- //
  a_tc_WB_valid_stall: assert property (tc_WB_valid_stall) begin
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : PASSED"), UVM_LOW)
  end else begin
    $display(seperator);
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : FAILED"), UVM_LOW)
    `uvm_info("sva", $sformatf("Sub-test : WB_valid stall"), UVM_LOW)
    $display(seperator);
  end

  a_tc_WB_data_stall: assert property (tc_WB_data_stall) begin
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : PASSED"), UVM_LOW)
  end else begin
    $display(seperator);
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : FAILED"), UVM_LOW)
    `uvm_info("sva", $sformatf("Sub-test : WB_data stall"), UVM_LOW)
    $display(seperator);
  end

  a_tc_WB_PR_stall: assert property (tc_WB_PR_stall) begin
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : PASSED"), UVM_LOW)
  end else begin
    $display(seperator);
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : FAILED"), UVM_LOW)
    `uvm_info("sva", $sformatf("Sub-test : WB_PR stall"), UVM_LOW)
    $display(seperator);
  end

  a_tc_WB_ROB_index_stall: assert property (tc_WB_ROB_index_stall) begin
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : PASSED"), UVM_LOW)
  end else begin
    $display(seperator);
    `uvm_info("sva", $sformatf("Test Case: tc_wb_stall : FAILED"), UVM_LOW)
    `uvm_info("sva", $sformatf("Sub-test : WB_ROB_index stall"), UVM_LOW)
    $display(seperator);
  end

endmodule

`endif