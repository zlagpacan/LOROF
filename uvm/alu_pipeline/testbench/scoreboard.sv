/*
    Module   : alu_pipeline
    Filename : env.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_SCOREBOARD_SV
`define ALU_PIPELINE_SCOREBOARD_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "sequence_item.sv"
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- ALU Pipeline Scoreboard --- //
class alu_pipeline_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(alu_pipeline_scoreboard)

    // --- UVM Analysis Port --- //
    



endclass : alu_pipeline_scoreboard

`endif
