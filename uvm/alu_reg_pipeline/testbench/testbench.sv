/*
  Module        : alu_reg_pipeline
  UMV Component : testbench
  Author        : Adam Keith
*/

`ifndef ALU_REG_PIPELINE_TESTBENCH_SV
`define ALU_REG_PIPELINE_TESTBENCH_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "interface.sv"
`include "sequence_item.sv"
`include "sequences/reset_seq.sv"
`include "sequencer.sv"
`include "driver.sv"
`include "monitor.sv"
`include "agent.sv"
`include "scoreboard.sv"
`include "env.sv"
`include "test.sv"

`timescale 1ns/1ns

module top;
  
  // --- Sim Clock --- // 
  logic CLK;
  alu_reg_pipeline_if alu_reg_pipeline_intf(.CLK(CLK));
  parameter CLK_PERIOD = 4;

  // --- DUT Instance --- //
  alu_reg_pipeline DUT(
    .CLK(CLK),
    .nRST(alu_reg_pipeline_intf.nRST),
    .issue_op(alu_reg_pipeline_intf.issue_op),
    .issue_A_forward(alu_reg_pipeline_intf.issue_A_forward),
    .issue_A_bank(alu_reg_pipeline_intf.issue_A_bank),
    .issue_B_forward(alu_reg_pipeline_intf.issue_B_forward),
    .issue_B_bank(alu_reg_pipeline_intf.issue_B_bank),
    .issue_dest_PR(alu_reg_pipeline_intf.issue_dest_PR),
    .issue_ROB_index(alu_reg_pipeline_intf.issue_ROB_index),
    .A_reg_read_ack(alu_reg_pipeline_intf.A_reg_read_ack),
    .A_reg_read_port(alu_reg_pipeline_intf.A_reg_read_port),
    .reg_read_data_by_bank(alu_reg_pipeline_intf.reg_read_data_by_bank),
    .forward_data_by_bank(alu_reg_pipeline_intf.forward_data_by_bank),
    .WB_ready(alu_reg_pipeline_intf.WB_ready),
    .issue_ready(alu_reg_pipeline_intf.issue_ready),
    .WB_valid(alu_reg_pipeline_intf.WB_valid),
    .WB_data(alu_reg_pipeline_intf.WB_data),
    .WB_PR(alu_reg_pipeline_intf.WB_PR),
    .WB_ROB_index(alu_reg_pipeline_intf.WB_ROB_index)
  );
  
  // --- Interface --- //
  initial begin : VIF
    uvm_config_db #(virtual alu_reg_pipeline_if)::set(null, "*", "vif", alu_reg_pipeline_intf);
  end
  
  // --- Start Test --- //
  initial begin : TEST
    run_test("alu_reg_pipeline_test");
  end
  
  // --- Clock Generation --- //
  always begin : CLK_GEN
      CLK = 1'b1;
      #(0.5 * CLK_PERIOD);
      CLK = 1'b0;
      #(0.5 * CLK_PERIOD);
  end

  // --- Maximum Sim Duration --- //
  initial begin : TIMEOUT
    #(1000 * CLK_PERIOD);
    $display("Sorry! Ran out of clock cycles");
    $finish();
  end
  
endmodule : top

`endif