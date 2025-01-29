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

  sequence WB_stall;
    ~WB_ready;
  endsequence

  // --- SVA Properties --- //
  property sva_WB_valid_stall;
    @(posedge CLK) disable iff (~nRST)
    (WB_stall) |=> (WB_valid == $past(WB_valid));
  endproperty

  // --- SVA Instances --- //
  a_ALURP_1A: assert property (sva_WB_valid_stall) begin
    $display("SVA_INFO @%t Test Case: ALURP_1 : PASSED", $time());
  end else begin
    $display("SVA_INFO @%t Test Case: ALURP_1 : FAILED", $time());
  end
  c_ALURP_1A: cover property (sva_WB_valid_stall);

endmodule

`endif