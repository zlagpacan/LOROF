/*
    Module   : alu_pipeline
    Filename : driver.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_DRIVER_SV
`define ALU_PIPELINE_DRIVER_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "sequence_item.sv"
`include "interface.sv"
`include "core_types_pkg.vh"
import core_types_pkg::*;

class alu_pipeline_driver extends uvm_driver;
    `uvm_component_utils (alu_pipeline_driver)

	// --- Virtual Interface --- //
    virtual alu_pipeline_if vif;

	// --- Constructor --- //
    function new (string name="alu_pipeline_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

	// --- Build Phase --- //
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        // --- Virtual Interface Check --- //
        if(!uvm_config_db #(virtual alu_pipeline_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("alu_pipeline_driver", "No virtual interface for alu_pipeline")
        end
    endfunction

    // --- Run Phase --- //
    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        `uvm_info("alu_pipeline_driver", "Inside Run Phase", UVM_HIGH)

        // --- Transaction Queue --- //
        forever begin 
            alu_tx = alu_pipeline_seq_item::type_id::create("alu_tx");
            seq_item_port.get_next_item(alu_tx);
            drive(alu_tx);
            seq_item_port.item_done();
        end
    endtask : run_phase

    // --- Drive Virtual Interface --- //
    task drive(alu_pipeline_seq_item alu_tx);
        // --- Interface Clock --- //
        @(posedge vif.CLK);
        // --- OP Issue --- //
        vif.nRST                     <= alu_tx.nRST;
        vif.valid_in                 <= alu_tx.valid_in;
        vif.op_in                    <= alu_tx.op_in;
        vif.imm_in                   <= alu_tx.imm_in;
        vif.is_imm_in                <= alu_tx.is_imm_in;
        vif.A_forward_in             <= alu_tx.A_forward_in;
        vif.A_unneeded_in            <= alu_tx.A_unneeded_in;
        vif.B_forward_in             <= alu_tx.B_forward_in;
        vif.A_bank_in                <= alu_tx.A_bank_in;
        vif.B_forward_in             <= alu_tx.B_forward_in;
        vif.B_bank_in                <= alu_tx.B_bank_in;
        vif.dest_PR_in               <= alu_tx.dest_PR_in;
        vif.B_bank_in                <= alu_tx.B_bank_in;
        // --- PRF --- //
        vif.B_reg_read_valid_in      <= alu_tx.B_reg_read_valid_in;
        vif.A_reg_read_valid_in      <= alu_tx.A_reg_read_valid_in;
        vif.forward_data_by_bank_in  <= alu_tx.forward_data_by_bank_in;
        vif.reg_read_data_by_bank_in <= alu_tx.reg_read_data_by_bank_in;

    endtask : drive

endclass : alu_pipeline_driver