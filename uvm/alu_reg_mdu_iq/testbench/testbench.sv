/*
  Module        : alu_reg_mdu_iq
  UMV Component : testbench
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_TESTBENCH_SV
`define ALU_REG_MDU_IQ_TESTBENCH_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "interface.sv"
`include "sequence_item.sv"
// `include "sequence.sv"
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

  parameter CLK_PERIOD = 10;


   // --- Clock Generation --- //
  always begin : CLK_GEN
    CLK = 1'b1;
    #(0.5 * CLK_PERIOD);
    CLK = 1'b0;
    #(0.5 * CLK_PERIOD);
end

  alu_reg_mdu_iq_if alu_reg_mdu_iq_intf(.CLK(CLK));

  // --- DUT Instance --- //
  alu_reg_mdu_iq MDU_IQ(
    .CLK(CLK),
    .nRST(alu_reg_mdu_iq_intf.nRST),
    .dispatch_attempt_by_way(alu_reg_mdu_iq_intf.dispatch_attempt_by_way),
    .dispatch_valid_alu_reg_by_way(alu_reg_mdu_iq_intf.dispatch_valid_alu_reg_by_way),
    .dispatch_valid_mdu_by_way(alu_reg_mdu_iq_intf.dispatch_valid_mdu_by_way),
    .dispatch_op_by_way(alu_reg_mdu_iq_intf.dispatch_op_by_way),
    .dispatch_A_PR_by_way(alu_reg_mdu_iq_intf.dispatch_A_PR_by_way),
    .dispatch_A_ready_by_way(alu_reg_mdu_iq_intf.dispatch_A_ready_by_way),
    .dispatch_A_is_zero_by_way(alu_reg_mdu_iq_intf.dispatch_A_is_zero_by_way),
    .dispatch_B_PR_by_way(alu_reg_mdu_iq_intf.dispatch_B_PR_by_way),
    .dispatch_B_ready_by_way(alu_reg_mdu_iq_intf.dispatch_B_ready_by_way),
    .dispatch_B_is_zero_by_way(alu_reg_mdu_iq_intf.dispatch_B_is_zero_by_way),
    .dispatch_dest_PR_by_way(alu_reg_mdu_iq_intf.dispatch_dest_PR_by_way),
    .dispatch_ROB_index_by_way(alu_reg_mdu_iq_intf.dispatch_ROB_index_by_way),
    .alu_reg_pipeline_ready(alu_reg_mdu_iq_intf.alu_reg_pipeline_ready),
    .mdu_pipeline_ready(alu_reg_mdu_iq_intf.mdu_pipeline_ready),
    .WB_bus_valid_by_bank(alu_reg_mdu_iq_intf.WB_bus_valid_by_bank),
    .WB_bus_upper_PR_by_bank(alu_reg_mdu_iq_intf.WB_bus_upper_PR_by_bank),
    .dispatch_ack_by_way(alu_reg_mdu_iq_intf.dispatch_ack_by_way),
    .issue_alu_reg_valid(alu_reg_mdu_iq_intf.issue_alu_reg_valid),
    .issue_alu_reg_op(alu_reg_mdu_iq_intf.issue_alu_reg_op),
    .issue_alu_reg_A_forward(alu_reg_mdu_iq_intf.issue_alu_reg_A_forward),
    .issue_alu_reg_A_is_zero(alu_reg_mdu_iq_intf.issue_alu_reg_A_is_zero),
    .issue_alu_reg_A_bank(alu_reg_mdu_iq_intf.issue_alu_reg_A_bank),
    .issue_alu_reg_B_forward(alu_reg_mdu_iq_intf.issue_alu_reg_B_forward),
    .issue_alu_reg_B_is_zero(alu_reg_mdu_iq_intf.issue_alu_reg_B_is_zero),
    .issue_alu_reg_B_bank(alu_reg_mdu_iq_intf.issue_alu_reg_B_bank),
    .issue_alu_reg_dest_PR(alu_reg_mdu_iq_intf.issue_alu_reg_dest_PR),
    .issue_alu_reg_ROB_index(alu_reg_mdu_iq_intf.issue_alu_reg_ROB_index),
    .PRF_alu_reg_req_A_valid(alu_reg_mdu_iq_intf.PRF_alu_reg_req_A_valid),
    .PRF_alu_reg_req_A_PR(alu_reg_mdu_iq_intf.PRF_alu_reg_req_A_PR),
    .PRF_alu_reg_req_B_valid(alu_reg_mdu_iq_intf.PRF_alu_reg_req_B_valid),
    .PRF_alu_reg_req_B_PR(alu_reg_mdu_iq_intf.PRF_alu_reg_req_B_PR),
    .issue_mdu_valid(alu_reg_mdu_iq_intf.issue_mdu_valid),
    .issue_mdu_op(alu_reg_mdu_iq_intf.issue_mdu_op),
    .issue_mdu_A_forward(alu_reg_mdu_iq_intf.issue_mdu_A_forward),
    .issue_mdu_A_is_zero(alu_reg_mdu_iq_intf.issue_mdu_A_is_zero),
    .issue_mdu_A_bank(alu_reg_mdu_iq_intf.issue_mdu_A_bank),
    .issue_mdu_B_forward(alu_reg_mdu_iq_intf.issue_mdu_B_forward),
    .issue_mdu_B_is_zero(alu_reg_mdu_iq_intf.issue_mdu_B_is_zero),
    .issue_mdu_B_bank(alu_reg_mdu_iq_intf.issue_mdu_B_bank),
    .issue_mdu_dest_PR(alu_reg_mdu_iq_intf.issue_mdu_dest_PR),
    .issue_mdu_ROB_index(alu_reg_mdu_iq_intf.issue_mdu_ROB_index),
    .PRF_mdu_req_A_valid(alu_reg_mdu_iq_intf.PRF_mdu_req_A_valid),
    .PRF_mdu_req_A_PR(alu_reg_mdu_iq_intf.PRF_mdu_req_A_PR),
    .PRF_mdu_req_B_valid(alu_reg_mdu_iq_intf.PRF_mdu_req_B_valid),
    .PRF_mdu_req_B_PR(alu_reg_mdu_iq_intf.PRF_mdu_req_B_PR)
  );
  
  // --- Interface --- //
  initial begin : VIF
    $timeformat(-9, 0, " ns", 10); // Set time format to nanoseconds with 3 decimal place
    uvm_config_db #(virtual alu_reg_mdu_iq_if)::set(null, "*", "vif", alu_reg_mdu_iq_intf);
  end
  
  // --- Start Test --- //
  initial begin : TEST
    run_test("alu_reg_mdu_iq_test");
  end
  
 
  // --- Maximum Sim Duration --- //
  initial begin : TIMEOUT
    #(1000 * CLK_PERIOD);
    $display("Sorry! Ran out of clock cycles");
    $finish();
  end
  
endmodule : top

`endif