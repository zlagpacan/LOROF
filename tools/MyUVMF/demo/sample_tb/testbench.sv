/*
  Module        : alu
  UMV Component : testbench
  Author        : Adam Keith
*/

`ifndef ALU_TESTBENCH_SV
`define ALU_TESTBENCH_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "alu_pkg.svh"
import alu_pkg::*;
    
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
  logic clk;
  alu_if alu_intf(.clk(clk));
  parameter CLK_PERIOD = 4;

  // --- DUT Instance --- //
  alu DUT(
    // User fills in 
    // Will be added feature in later release
    .clk(alu_intf.clk),
    .n_rst(alu_intf.n_rst),
    .a(alu_intf.a),
    .b(alu_intf.b),
    .opcode(alu_intf.opcode),
    .out(alu_intf.out),
    .negative(alu_intf.negative),
    .overflow(alu_intf.overflow),
    .zero(alu_intf.zero)
  );
  
  // --- Interface --- //
  initial begin : VIF
    uvm_config_db #(virtual alu_if)::set(null, "*", "vif", alu_intf);
  end
  
  // --- Start Test --- //
  initial begin : TEST
    run_test("alu_test");
  end
  
  // --- Clock Generation --- //
  always begin : CLK_GEN
      clk = 1'b1;
      #(0.5 * CLK_PERIOD);
      clk = 1'b0;
      #(0.5 * CLK_PERIOD);
  end

  // --- Maximum Sim Duration --- //
  initial begin : TIMEOUT
    #(1000 * CLK_PERIOD);
    $display("Sorry! Ran out of clock cycles");
    $finish();
  end
  
  // --- Generate Waveforms --- //
  initial begin
    $dumpfile("sim.vcd");
    $dumpvars();
  end
  
endmodule : top

`endif