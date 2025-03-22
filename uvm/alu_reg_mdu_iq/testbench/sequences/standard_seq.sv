`ifndef STANDARD_SEQ_SV
`define STANDARD_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

class standard_sequence extends uvm_sequence;
    `uvm_object_utils(standard_sequence)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "standard_sequence");
        super.new(name);
        `uvm_info("STANDARD_SEQ", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("STANDARD_SEQ", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_attempt_by_way == 4'b1;
            dispatch_valid_alu_reg_by_way == 4'b1;
            dispatch_A_ready_by_way == 4'b1;
            alu_reg_pipeline_ready == 1;
            WB_bus_valid_by_bank == 0;
        };
        finish_item(standard_tx);
    endtask

endclass : standard_sequence

`endif