/*
    Module   : alu_pipeline
    Filename : testbench.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_TB_SV
`define ALU_PIPELINE_TB_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
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
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- Timescale --- //
`timescale 1ns/1ns

module top;
  
  // --- Sim Clock --- //
  logic CLK;
  alu_pipeline_if intf(.CLK(CLK));
  parameter CLK_PERIOD = 4;
  
  // --- DUT Instance --- //
  alu_pipeline DUT(
    .CLK          (intf.CLK),
    // TODO: connecting intf gonna be a pain
    // may have to go manual

  );
  
  // --- Interface --- //
  initial begin
    uvm_config_db #(virtual alu_pipeline_if)::set(null, "*", "vif", intf);
  end
  
  // --- Start Test --- //
  initial begin
    run_test("alu_pipeline_test");
  end
  
  // --- Clock Generation --- //
  always begin: CLK_GEN
      CLK = 1'b1;
      #(0.5 * CLK_PERIOD);
      CLK = 1'b0;
      #(0.5 * CLK_PERIOD);
  end

  // --- Maximum Sim Duration --- //
  initial begin
    #(1000 * CLK_PERIOD);
    $display("Sorry! Ran out of clock cycles!");
    $finish();
  end
  
//   // --- Generate Waveforms --- //
//   initial begin
//     $dumpfile("sim.vcd");
//     $dumpvars();
//   end
  
endmodule : top