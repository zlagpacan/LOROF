/*
    Module   : alu_pipeline
    Filename : env.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_AGENT_SV
`define ALU_PIPELINE_AGENT_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "agent.sv"
`include "scoreboard.sv"
`include "interface.sv"
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- ALU Pipeline Environment --- //
class alu_pipeline_env extends uvm_env;
    `uvm_component_utils(alu_pipeline_env)

    // --- Environment Components --- //
    alu_pipeline_agent      alu_pipeline_agnt;
    alu_pipeline_scoreboard alu_pipeline_scbd;

    // --- Constructor --- //
    function new (string name = "alu_pipeline_env", uvm_component parent);
        super.new(name, parent);
        `uvm_info("alu_pipeline_env", "build phase", UVM_HIGH)

        alu_pipeline_agnt = alu_pipeline_agent::type_id::create::("alu_pipeline_agnt", this);
        alu_pipeline_scbd = alu_pipeline_scoreboard::type_id::create::("alu_pipeline_scbd", this);

    endfunction : build_phase

    // --- Connect Phase --- //
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("alu_pipeline_env", "connect phase", UVM_HIGH)

        // FIXME: Make scoreboard port and connect
        alu_pipeline_agnt.alu_pipeline_mon.alu_pipeline_ap.connect();

    endfunction : connect_phase

endclass : alu_pipeline_env

`endif