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

        // --- Test Case Coverage : tc_reset --- //
        sequence DUT_reset;
          @(posedge t.CLK) ~(t.nRST);
        endsequence
        
        property DUT_RESET_EVENT;
          @(posedge t.CLK) (DUT_reset);
        endproperty
        cov_tc_reset: cover property (DUT_RESET_EVENT);
        
        // --- Test Case Coverage : tc_wb_stall --- //
        sequence WB_stall;
          @(posedge t.CLK) ~(t.WB_ready);
        endsequence
        
        property WB_STALL_EVENT;
          @(posedge t.CLK) disable iff (~t.nRST)
          (WB_stall);
        endproperty
        cov_tc_wb_stall: cover property (WB_STALL_EVENT);

    endfunction : write

endclass

`endif