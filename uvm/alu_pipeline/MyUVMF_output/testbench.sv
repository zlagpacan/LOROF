/*
  Module        : alu_pipeline
  UMV Component : testbench
  Author        : 
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
`include "sequence.sv"
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
  parameter CLK_PERIOD = ;

  // --- DUT Instance --- //
  alu_pipeline DUT(
    // User fills in 
    // Will be added feature in later release
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
    $display("Sorry! Ran out of clock cycles");
    $finish();
  end
  
endmodule : top

`endif