/*
    Module   : alu_pipeline
    Filename : sequence.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_SEQUENCE_SV
`define ALU_PIPELINE_SEQUENCE_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "sequence_item.sv"
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- Reset Sequence --- //
class alu_pipeline_rst_seq extends uvm_sequence;
    `uvm_object_utils(alu_pipeline_rst_seq)

    alu_pipeline_seq_item rst_pkt;

    // --- Constructor --- //
    function new (string name = "alu_pipeline_rst_seq");
        super.new(name);
        `uvm_info("alu_pipeline_rst_seq", "Constructor", UVM_HIGH)
    endfunction : new

    // --- Body Task --- //
    task body ();
        `uvm_info("alu_pipeline_rst_seq", "Body", UVM_HIGH)
        
        // --- Randomize With Reset --- //
        rst_pkt = alu_pipeline_rst_seq::type_id::create("rst_pkt");
        start_item(rst_pkt);
        rst_pkt.randomize() with {nRST == 1'b0;};
        finish_item(rst_pkt);
            
    endtask : body

endclass : alu_pipeline_rst_seq

`endif