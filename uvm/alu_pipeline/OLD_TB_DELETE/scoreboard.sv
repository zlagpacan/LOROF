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
    uvm_analysis_imp #(alu_pipeline_seq_item, alu_pipeline_scoreboard) alu_pipeline_scbd_ap;
    alu_pipeline_seq_item transactions[$];

    // --- Constructor --- //
    function new (string name = "alu_pipeline_scoreboard", uvm_component parent);
        super.new(name, parent);
        `uvm_info("alu_pipeline_scoreboard", "Constructor", UVM_HIGH)
    endfunction : new
    
    // --- Build Phase --- //
    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("alu_pipeline_scoreboard", "Build Phase", UVM_HIGH)
    
        // --- Scoreboard Port --- //
        alu_pipeline_scbd_ap = new("alu_pipeline_scbd_ap", this);
        
    endfunction : build_phase

    // --- Connect Phase --- //
    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("alu_pipeline_scoreboard", "Connect Phase", UVM_HIGH)
    
    endfunction : connect_phase
    
    // --- Write Sequence Item --- //
    function void write (alu_pipeline_seq_item alu_pipeline_tx);
        transactions.push_back(alu_pipeline_tx);
    endfunction : write 

    // --- Run Phase --- //
    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        `uvm_info("alu_pipeline_scoreboard", "Run Phase", UVM_HIGH)
    
        // --- Sequence Item Stack --- //
        forever begin
        alu_pipeline_seq_item curr_trans;
        wait((transactions.size() != 0));
        curr_trans = transactions.pop_front();
        compare(curr_trans);
        end
        
    endtask : run_phase

    // --- Compare --- //
    task compare (alu_pipeline_seq_item curr_trans);

        // --- Actual vs Expected --- //

        // --- SVA? -- //

    endtask : compare

endclass : alu_pipeline_scoreboard

`endif
