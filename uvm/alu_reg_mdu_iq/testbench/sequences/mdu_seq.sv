`ifndef MDU_SEQ_SV
`define MDU_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

class simp_mdu_seq extends uvm_sequence;
    `uvm_object_utils(simp_mdu_seq)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_mdu_seq");
        super.new(name);
        `uvm_info("simp_mdu_seq", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_mdu_seq", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_attempt_by_way == 4'b1;
            dispatch_valid_alu_reg_by_way == 4'b0;
            dispatch_valid_mdu_by_way == 4'b1; // no mdu dispatch 
            dispatch_A_ready_by_way == 4'b1;
            dispatch_B_ready_by_way == 4'b1;
            alu_reg_pipeline_ready == 0; // alu reg pipe not ready
            mdu_pipeline_ready == 1; // MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_mdu_seq

class simp_mdu_seq2 extends uvm_sequence;
    `uvm_object_utils(simp_mdu_seq2)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_reg_seq2");
        super.new(name);
        `uvm_info("simp_reg_seq2", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_reg_seq2", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            $countones(standard_tx.dispatch_attempt_by_way) == 2;
            $countones(standard_tx.dispatch_valid_mdu_by_way) == 2; 
            nRST == 1'b1;
            dispatch_valid_alu_reg_by_way == 4'b0; // no mdu dispatch 
            dispatch_A_ready_by_way == 4'b1;
            dispatch_B_ready_by_way == 4'b1;
            alu_reg_pipeline_ready == 0; // alu reg not ready
            mdu_pipeline_ready == 1; // MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_mdu_seq2

class simp_mdu_a_b_nr extends uvm_sequence;
    `uvm_object_utils(simp_mdu_a_b_nr)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_mdu_a_b_nr");
        super.new(name);
        `uvm_info("simp_mdu_a_b_nr", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_mdu_a_b_nr", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_valid_alu_reg_by_way == 4'b0; // no mdu dispatch 
            dispatch_A_ready_by_way == 4'b0;
            dispatch_B_ready_by_way == 4'b0;
            dispatch_A_is_zero_by_way == 4'b0;
            dispatch_B_is_zero_by_way == 4'b0;
            alu_reg_pipeline_ready == 0; // alu reg pipe not ready
            mdu_pipeline_ready == 1; // MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_mdu_a_b_nr


class mdu_normal_op_no_wb extends uvm_sequence;
    `uvm_object_utils(mdu_normal_op_no_wb)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "mdu_normal_op_no_wb");
        super.new(name);
        `uvm_info("mdu_normal_op_no_wb", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("mdu_normal_op_no_wb", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_valid_alu_reg_by_way == 4'b0; // no mdu dispatch 
            alu_reg_pipeline_ready == 0; // no MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : mdu_normal_op_no_wb

class mdu_normal_pipe_nr extends uvm_sequence;
    `uvm_object_utils(mdu_normal_pipe_nr)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "mdu_normal_pipe_nr");
        super.new(name);
        `uvm_info("mdu_normal_pipe_nr", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("mdu_normal_pipe_nr", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            nRST == 1'b1;
            mdu_pipeline_ready == 1'b0;
            dispatch_valid_alu_reg_by_way == 4'b0; // no alu_reg dispatch 
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : mdu_normal_pipe_nr


`endif