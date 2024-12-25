/*
    Module   : alu_pipeline
    Filename : monitor.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_MONITOR_SV
`define ALU_PIPELINE_MONITOR_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "sequence_item.sv"
`include "interface.sv"
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- ALU Pipeline Monitor --- //
class alu_pipeline_monitor extends uvm_monitor;
    `uvm_component_utils(alu_pipeline_monitor)

    // --- Interface --- //
    virtual alu_pipeline_if vif;
    alu_pipeline_seq_item alu_tx;

    // --- Analysis Port --- //
    uvm_analysis_port #(alu_pipeline_seq_item) alu_pipeline_ap;

	// --- Constructor --- //
	function new(string name = "alu_pipeline_monitor", uvm_component parent = null);
		super.new(name, parent);
		`uvm_info("alu_pipeline_monitor", "Constructor", UVM_HIGH)
	endfunction

	// --- Build Phase --- //
	virtual function void build_phase (uvm_phase phase);
		super.build_phase(phase);
		`uvm_info("alu_pipeline_monitor", "Build Phase", UVM_HIGH)

		// --- Build + Check Monitor Port --- //
	    alu_pipeline_ap = new("alu_pipeline_ap", this);

		if(!uvm_config_db #(virtual alu_pipeline_if)::get(this, "", "vif", vif)) begin
			`uvm_fatal("alu_pipeline_monitor", "No virtual interface for alu_pipeline_if")
		end
	endfunction : build_phase

    // --- Run Phase --- //
    virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
		`uvm_info("alu_pipeline_monitor", "Run Phase", UVM_HIGH)

		// --- Create ALU Transaction --- //		
		alu_tx = alu_pipeline_seq_item::type_id::create("alu_tx");

		// --- Run Phase --- //
		forever begin
			wait(vif.nRST);

			// --- Input Sample --- //
			@(posedge vif.CLK);			
            // --- OP Issue --- //
            alu_tx.nRST                     = vif.nRST;
            alu_tx.valid_in                 = vif.valid_in;
            alu_tx.op_in                    = vif.op_in;
            alu_tx.imm_in                   = vif.imm_in;
            alu_tx.is_imm_in                = vif.is_imm_in;
            alu_tx.A_forward_in             = vif.A_forward_in;
            alu_tx.A_unneeded_in            = vif.A_unneeded_in;
            alu_tx.B_forward_in             = vif.B_forward_in;
            alu_tx.A_bank_in                = vif.A_bank_in;
            alu_tx.B_forward_in             = vif.B_forward_in;
            alu_tx.B_bank_in                = vif.B_bank_in;
            alu_tx.dest_PR_in               = vif.dest_PR_in;
            alu_tx.B_bank_in                = vif.B_bank_in;
            // --- PRF --- //
            alu_tx.B_reg_read_valid_in      = vif.B_reg_read_valid_in;
            alu_tx.A_reg_read_valid_in      = vif.A_reg_read_valid_in;
            alu_tx.forward_data_by_bank_in  = vif.forward_data_by_bank_in;
            alu_tx.reg_read_data_by_bank_in = vif.reg_read_data_by_bank_in;
			
			// --- Output Sample --- //
			@(posedge vif.CLK);			
            alu_tx.ready_out                = vif.ready_out;
            alu_tx.WB_valid_out             = vif.WB_valid_out;
            alu_tx.WB_data_out              = vif.WB_data_out;
            alu_tx.WB_PR_out                = vif.WB_PR_out;

			// --- Send to Scoreboard --- //
			alu_pipeline_ap.write(alu_tx);
	
		end
	endtask : run_phase

endclass : alu_pipeline_monitor

`endif