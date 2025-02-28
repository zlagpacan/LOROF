`ifndef RESET_SEQ_SV
`define RESET_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

class reset_sequence extends uvm_sequence;
    `uvm_object_utils(reset_sequence)
    alu_reg_mdu_iq_sequence_item reset_tx;

    function new(string name = "reset_sequence");
        super.new(name);
        `uvm_info("RESET_SEQ", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("RESET_SEQ", "Inside body task", UVM_HIGH)

        reset_tx = alu_reg_mdu_iq_sequence_item::type_id::create("reset_tx");
        start_item(reset_tx);
        reset_tx.randomize() with {
            nRST == 1'b0;
            dispatch_attempt_by_way == {4{1'b0}};
            dispatch_valid_alu_reg_by_way == {4{1'b0}};
            alu_reg_pipeline_ready == 1;
            WB_bus_valid_by_bank ==  {4{1'b0}};
        };
        finish_item(reset_tx);
    endtask

endclass : reset_sequence


class garbage_sequence extends uvm_sequence;
    `uvm_object_utils(garbage_sequence)
    alu_reg_mdu_iq_sequence_item garb_tx;

    function new(string name = "garbage_sequence");
        super.new(name);
        `uvm_info("GARBAGE_SEQ", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("GARBAGE_SEQ", "Inside body task", UVM_HIGH)
        garb_tx = alu_reg_mdu_iq_sequence_item::type_id::create("garb_tx");
        start_item(garb_tx);
        garb_tx.randomize() with {
            nRST == 1'b1;
            // dispatch_attempt_by_way == {4{1'b0}};
            // dispatch_valid_alu_reg_by_way == {4{1'b0}};
            // alu_reg_pipeline_ready == 1;
            // WB_bus_valid_by_bank ==  {4{1'b0}};
        };
        finish_item(garb_tx);
    endtask

endclass : garbage_sequence

`endif