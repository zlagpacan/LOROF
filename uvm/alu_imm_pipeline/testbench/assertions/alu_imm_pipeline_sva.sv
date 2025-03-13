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

  // --- Test Case tc_wb_stall Properties --- //
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

  // --- Test Case tc_standard_wb Properties --- //
  logic inv_nRST;
  logic inv_WB_ready;
  logic inv_issue_valid;

  // assign inv_nRST        = $past(nRST, 1) | $past(nRST, 2) | $past(nRST, 3);
  // assign inv_WB_ready    = $past(WB_ready, 1) | $past(WB_ready, 2) | $past(WB_ready, 3);
  // assign inv_issue_valid = $past(issue_valid, 1) | $past(issue_valid, 2) | $past(issue_valid, 3);

  always_ff @(posedge CLK or negedge nRST) begin
    if (~nRST) begin
        inv_nRST        <= 1'b0;
        inv_WB_ready    <= 1'b0;
        inv_issue_valid <= 1'b0;
    end else begin
        inv_nRST        <= $past(nRST, 1) | $past(nRST, 2) | $past(nRST, 3);
        inv_WB_ready    <= $past(WB_ready, 1) | $past(WB_ready, 2) | $past(WB_ready, 3);
        inv_issue_valid <= $past(issue_valid, 1) | $past(issue_valid, 2) | $past(issue_valid, 3);
    end
  end

  property tc_standard_WB_PR;
    @(posedge CLK) disable iff (inv_nRST || inv_WB_ready || inv_issue_valid)
    (WB_PR === $past(issue_dest_PR, 3));
  endproperty

  property tc_standard_WB_ROB_index;
    @(posedge CLK) disable iff (inv_nRST || inv_WB_ready || inv_issue_valid)
    (WB_ROB_index === $past(issue_ROB_index, 3));
  endproperty

  // --- Test Case tc_wb_stall Instances --- //
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

  // --- Test Case tc_standard_wb Instances --- //
  a_tc_standard_WB_PR: assert property (tc_standard_WB_PR) begin
    `uvm_info("sva", $sformatf("Test Case: tc_standard_wb : PASSED"), UVM_LOW)
  end else begin
    $display(seperator);
    `uvm_info("sva", $sformatf("Test Case: tc_standard_wb : FAILED"), UVM_LOW)
    `uvm_info("sva", $sformatf("Sub-test : WB_PR pass through"), UVM_LOW)
    $display(seperator);
  end

  a_tc_standard_WB_ROB_index: assert property (tc_standard_WB_ROB_index) begin
    `uvm_info("sva", $sformatf("Test Case: tc_standard_wb : PASSED"), UVM_LOW)
  end else begin
    $display(seperator);
    `uvm_info("sva", $sformatf("Test Case: tc_standard_wb : FAILED"), UVM_LOW)
    `uvm_info("sva", $sformatf("Sub-test : WB_ROB_index pass through"), UVM_LOW)
    $display(seperator);
  end

endmodule

`endif