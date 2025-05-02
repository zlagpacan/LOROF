`ifndef REG_MDU_SEQ_SV
`define REG_MDU_SEQ_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

class simp_reg_mdu_seq extends uvm_sequence;
    `uvm_object_utils(simp_reg_mdu_seq)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_reg_mdu_seq");
        super.new(name);
        `uvm_info("simp_reg_mdu_seq", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_reg_mdu_seq", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        standard_tx.randomize() with {
            nRST == 1'b1;
            $countones(dispatch_attempt_by_way) == 2;
            $countones(dispatch_valid_alu_reg_by_way) == 1;
            $countones(dispatch_valid_mdu_by_way) == 1;
            dispatch_A_ready_by_way == '1;
            dispatch_B_ready_by_way == '1;
            alu_reg_pipeline_ready == 1;
            mdu_pipeline_ready == 1; 
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_reg_mdu_seq


class simp_reg_mdu_nr extends uvm_sequence;
    `uvm_object_utils(simp_reg_mdu_nr)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_reg_mdu_nr");
        super.new(name);
        `uvm_info("simp_reg_mdu_nr", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_reg_mdu_nr", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_A_ready_by_way == '0;
            dispatch_B_ready_by_way == '0;
            dispatch_A_is_zero_by_way == 4'b0;
            dispatch_B_is_zero_by_way == 4'b0;
            alu_reg_pipeline_ready == 1;
            mdu_pipeline_ready == 1; 
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_reg_mdu_nr


class simp_reg_mdu_no_wb_full_op extends uvm_sequence;
    `uvm_object_utils(simp_reg_mdu_no_wb_full_op)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_reg_mdu_no_wb_full_op");
        super.new(name);
        `uvm_info("simp_reg_mdu_no_wb_full_op", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_reg_mdu_no_wb_full_op", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        standard_tx.randomize() with {
            nRST == 1'b1;
            WB_bus_valid_by_bank == 0; // no wb
            foreach(dispatch_A_ready_by_way[i]) {
            ( dispatch_A_ready_by_way[i] == 1'b1) dist {1:=100, 0:=0};
            }
            foreach(dispatch_B_ready_by_way[i]) {
            ( dispatch_B_ready_by_way[i] == 1'b1) dist {1:=100, 0:=0};
            }

            foreach(dispatch_A_is_zero_by_way[i]) {
            ( dispatch_A_is_zero_by_way[i] == 1'b1) dist {1:=100, 0:=0};
            }
            foreach(dispatch_A_is_zero_by_way[i]) {
            (dispatch_A_is_zero_by_way[i] == 1'b1) dist {1:=100, 0:=0};
            }
        };
        finish_item(standard_tx);
    endtask

endclass : simp_reg_mdu_no_wb_full_op


class simp_reg_mdu_pipe_nr extends uvm_sequence;
    `uvm_object_utils(simp_reg_mdu_pipe_nr)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_reg_mdu_pipe_nr");
        super.new(name);
        `uvm_info("simp_reg_mdu_pipe_nr", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_reg_mdu_pipe_nr", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        standard_tx.randomize() with {
            nRST == 1'b1;
            alu_reg_pipeline_ready == 0;
            mdu_pipeline_ready == 0; 
            // WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_reg_mdu_pipe_nr
`endif