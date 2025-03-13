/*
  Module        : alu_imm_pipeline
  UMV Component : coverage tracker
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_COV_SV
`define ALU_IMM_PIPELINE_COV_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
class alu_imm_pipeline_coverage extends uvm_subscriber#(alu_imm_pipeline_sequence_item); 
    `uvm_component_utils(alu_imm_pipeline_coverage)

    uvm_analysis_port#(alu_imm_pipeline_sequence_item) cov_ap;

    function new(string name = "alu_imm_pipeline_coverage", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cov_ap = new("cov_ap", this);
    endfunction : build_phase

    function void write(alu_imm_pipeline_sequence_item t);

    endfunction : write

endclass

`endif