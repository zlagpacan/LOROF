/*
  Module        : alu_pipeline
  UMV Component : testbench
  Author        : Adam Keith
*/

`ifndef ALU_PIPELINE_TESTBENCH_SV
`define ALU_PIPELINE_TESTBENCH_SV

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
  alu_pipeline_if alu_pipeline_intf(.CLK(CLK));
  parameter CLK_PERIOD = 4;

  // --- DUT Instance --- //
  alu_pipeline DUT(
    .CLK(CLK),
    .nRST(alu_pipeline_intf.nRST),
    .op_in(alu_pipeline_intf.op_in),
    .is_imm_in(alu_pipeline_intf.is_imm_in),
    .imm_in(alu_pipeline_intf.imm_in),
    .A_unneeded_in(alu_pipeline_intf.A_unneeded_in),
    .A_forward_in(alu_pipeline_intf.A_forward_in),
    .A_bank_in(alu_pipeline_intf.A_bank_in),
    .B_forward_in(alu_pipeline_intf.B_forward_in),
    .B_bank_in(alu_pipeline_intf.B_bank_in),
    .dest_PR_in(alu_pipeline_intf.dest_PR_in),
    .A_reg_read_valid_in(alu_pipeline_intf.A_reg_read_valid_in),
    .B_reg_read_valid_in(alu_pipeline_intf.B_reg_read_valid_in),
    .ROB_index_in(alu_pipeline_intf.ROB_index_in),
    .reg_read_data_by_bank_in(alu_pipeline_intf.reg_read_data_by_bank_in),
    .forward_data_by_bank_in(alu_pipeline_intf.forward_data_by_bank_in),
    .ready_out(alu_pipeline_intf.ready_out),
    .WB_valid_out(alu_pipeline_intf.WB_valid_out),
    .WB_data_out(alu_pipeline_intf.WB_data_out),
    .WB_PR_out(alu_pipeline_intf.WB_PR_out),
    .WB_ROB_index_out(alu_pipeline_intf.WB_ROB_index_out)
  );

  // --- SVA module --- //
  alu_pipeline_sva SVA(
    .CLK(CLK),
    .nRST(nRST),
    .ready_out(ready_out),
    .valid_out(valid_out),
    .WB_data_out(WB_data_out),
    .WB_PR_out(WB_PR_out)
  );
  
  // --- Interface --- //
  initial begin : VIF
    uvm_config_db #(virtual alu_pipeline_if)::set(null, "*", "vif", alu_pipeline_intf);
  end
  
  // --- Start Test --- //
  initial begin : TEST
    run_test("alu_pipeline_test");
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
    $display("Simulation timeout reached (config in uvm testbench)");
    $finish();
  end
  
endmodule : top

`endif