/*
  Module        : alu_pipeline
  UMV Component : System Verilog Assertions
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_SVA_SV
`define ALU_PIPELINE_SVA_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- SVA Checks --- //
module alu_pipeline_sva (
    input logic                    CLK,
    input logic                    nRST,
    input logic                    ready_out,
    input logic                    WB_valid_out,
    input logic [31:0]             WB_data_out,
    input logic [LOG_PR_COUNT-1:0] WB_PR_out
);

  sequence sva_reset_sequence;
    ~nRST;
  endsequence

  // --- SVA Properties --- //
  property sva_ready_out_rst;
    @(posedge CLK)
    (sva_reset_sequence) |-> (ready_out == 1'b1);
  endproperty

  property sva_valid_out_rst;
    @(posedge CLK)
    (sva_reset_sequence) |-> (WB_valid_out == 1'b0);
  endproperty

  property sva_WB_data_out_rst;
    @(posedge CLK)
    (sva_reset_sequence) |-> (WB_data_out == '0);
  endproperty

  property sva_WB_PR_out_rst;
    @(posedge CLK)
    (sva_reset_sequence) |-> (WB_PR_out == '0);
  endproperty

  // --- SVA Instances --- //
  /* 
    Test Case Tag: ALP0
    Test Case Name : Power-on-Reset
  */

  assert property (sva_ready_out_rst) begin
    $display("SVA_INFO @%tns a_ALP0_ready_out_rst - PASSED", $time());
  end else begin
    $display("SVA_INFO @%tns a_ALP0_ready_out_rst - FAILED", $time());
  end
  c_ALP0_ready_out_rst:     cover  property (sva_ready_out_rst);

  assert property (sva_valid_out_rst) begin
    $display("SVA_INFO @%tns a_ALP0_valid_out_rst - PASSED", $time());
  end else begin
    $display("SVA_INFO @%tns a_ALP0_valid_out_rst - FAILED", $time());
  end
  c_ALP0_valid_out_rst:     cover  property (sva_valid_out_rst);

  assert property (sva_WB_data_out_rst) begin
    $display("SVA_INFO @%tns a_ALP0_WB_data_out_rst - PASSED", $time());
  end else begin
    $display("SVA_INFO @%tns a_ALP0_WB_data_out_rst - FAILED", $time());
  end
  c_ALP0_WB_data_out_rst:   cover  property (sva_WB_data_out_rst);

  assert property (sva_WB_PR_out_rst) begin
    $display("SVA_INFO @%tns a_ALP0_WB_PR_out_rst - PASSED", $time());
  end else begin
    $display("SVA_INFO @%tns a_ALP0_WB_PR_out_rst - FAILED", $time());
  end
  c_ALP0_WB_PR_out_rst:     cover  property (sva_WB_PR_out_rst);

endmodule

`endif