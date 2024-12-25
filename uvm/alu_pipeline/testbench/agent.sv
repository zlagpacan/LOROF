/*
    Module   : alu_pipeline
    Filename : agent.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_AGENT_SV
`define ALU_PIPELINE_AGENT_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "sequence_item.sv"
`include "sequencer.sv"
`include "driver.sv"
`include "monitor.sv"
`include "interface.sv"
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- ALU Pipeline Agent --- //
class alu_pipeline_agent extends uvm_agent;
    `uvm_component_utils(alu_pipeline_agent)

    // --- Analysis Port --- //
    uvm_analysis_port #(alu_pipeline_seq_item) alu_pipeline_agent_ap;

    // --- Agent Components --- //
    alu_pipeline_driver     alu_pipeline_drv;
    alu_pipeline_sequencer  alu_pipeline_sqr;
    alu_pipeline_monitor    alu_pipeline_mon;

    // --- Interface --- //
    virtual alu_pipeline_if vif;

    // --- Constructor --- //
    function new (string name = "alu_pipeline_agent", uvm_component parent = null);
        super.new(name, parent);
        alu_pipeline_agent_ap = new("alu_pipeline_agent_ap", this);
    endfunction : new

    // --- Build Phase --- //
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // --- Build Agent Components --- //
        alu_pipeline_drv = alu_pipeline_driver::type_id::create("alu_pipeline_drv", this);
        alu_pipeline_sqr = alu_pipeline_sequencer::type_id::create("alu_pipeline_sqr", this);
        alu_pipeline_mon = alu_pipeline_monitor::type_id::create("alu_pipeline_mon", this);

        if(!uvm_config_db #(virtual alu_pipeline_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("alu_pipeline_agent", "No virtual interface for alu_pipeline_if")
        end
    endfunction : build_phase

    // --- Connect Phase --- //
    virtual function void connect_phase(uvm_phase phase);
        alu_pipeline_drv.seq_item_port.connect(alu_pipeline_sqr.seq_item_export);
        uvm_report_info("alu_pipeline_agent", "Connected driver to sequencer", UVM_HIGH);

        alu_pipeline_mon.alu_pipeline_ap.connect(alu_pipeline_agent_ap);
        uvm_report_info("alu_pipeline_agent", "Connected monitor analysis port to agent analysis port", UVM_HIGH);
    endfunction : connect_phase

endclass : alu_pipeline_agent

`endif