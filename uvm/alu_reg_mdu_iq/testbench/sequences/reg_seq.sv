`ifndef REG_SEQ_SV
`define REG_SEQ_SV

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
            // dispatch_attempt_by_way == 4'b1;
            // // dispatch_valid_alu_reg_by_way == 4'b1;
            // dispatch_valid_mdu_by_way == 4'b1;
            // dispatch_A_ready_by_way == 4'b1;
            // alu_reg_pipeline_ready == 1;
            // // mdu_pipeline_ready == 1;
            // WB_bus_valid_by_bank == 0;
        };
        finish_item(standard_tx);
    endtask

endclass : standard_sequence

class simp_reg_seq extends uvm_sequence;
    `uvm_object_utils(simp_reg_seq)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_reg_seq");
        super.new(name);
        `uvm_info("simp_reg_seq", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_reg_seq", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_attempt_by_way == 4'b1;
            dispatch_valid_alu_reg_by_way == 4'b1;
            dispatch_valid_mdu_by_way == 4'b0; // no mdu dispatch 
            dispatch_A_ready_by_way == 4'b1;
            dispatch_B_ready_by_way == 4'b1;
            alu_reg_pipeline_ready == 1; // alu reg pipready
            mdu_pipeline_ready == 0; // no MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_reg_seq

class simp_reg_seq2 extends uvm_sequence;
    `uvm_object_utils(simp_reg_seq2)
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
            $countones(standard_tx.dispatch_valid_alu_reg_by_way) == 2; 
            nRST == 1'b1;
            dispatch_valid_mdu_by_way == 4'b0; // no mdu dispatch 
            dispatch_A_ready_by_way == 4'b1;
            dispatch_B_ready_by_way == 4'b1;
            alu_reg_pipeline_ready == 1; // alu reg pipready
            mdu_pipeline_ready == 0; // no MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_reg_seq2

class simp_a_b_nr extends uvm_sequence;
    `uvm_object_utils(simp_a_b_nr)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "simp_a_b_nr");
        super.new(name);
        `uvm_info("simp_a_b_nr", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("simp_a_b_nr", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_valid_mdu_by_way == 4'b0; // no mdu dispatch 
            dispatch_A_ready_by_way == 4'b0;
            dispatch_B_ready_by_way == 4'b0;
            dispatch_A_is_zero_by_way == 4'b0;
            dispatch_B_is_zero_by_way == 4'b0;
            alu_reg_pipeline_ready == 1; // alu reg pipready
            mdu_pipeline_ready == 0; // no MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : simp_a_b_nr


class reg_normal_op_no_wb extends uvm_sequence;
    `uvm_object_utils(reg_normal_op_no_wb)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "reg_normal_op_no_wb");
        super.new(name);
        `uvm_info("reg_normal_op_no_wb", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("reg_normal_op_no_wb", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            nRST == 1'b1;
            dispatch_valid_mdu_by_way == 4'b0; // no mdu dispatch 
            mdu_pipeline_ready == 0; // no MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : reg_normal_op_no_wb

class reg_normal_pipe_nr extends uvm_sequence;
    `uvm_object_utils(reg_normal_pipe_nr)
    alu_reg_mdu_iq_sequence_item standard_tx;

    function new(string name = "reg_normal_pipe_nr");
        super.new(name);
        `uvm_info("reg_normal_pipe_nr", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("reg_normal_pipe_nr", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            nRST == 1'b1;
            alu_reg_pipeline_ready == 1'b0;
            dispatch_valid_mdu_by_way == 4'b0; // no mdu dispatch 
            mdu_pipeline_ready == 0; // no MDU ready
            WB_bus_valid_by_bank == 0; // no wb
        };
        finish_item(standard_tx);
    endtask

endclass : reg_normal_pipe_nr

class reg_normal_pipe_wb extends uvm_sequence;
    `uvm_object_utils(reg_normal_pipe_wb)
    alu_reg_mdu_iq_sequence_item standard_tx;
    logic [1:0] [6:0] x1 = 'z;
    logic [1:0] [6:0] x2 = 'z;
    
    function new(string name = "reg_normal_pipe_wb");
        super.new(name);
        `uvm_info("reg_normal_pipe_wb", "Inside Constructor", UVM_HIGH)
    endfunction

    task body(); 
        `uvm_info("reg_normal_pipe_wb", "Inside body task", UVM_HIGH)
        standard_tx = alu_reg_mdu_iq_sequence_item::type_id::create("standard_tx");
        start_item(standard_tx);
        
        standard_tx.randomize() with {
            nRST == 1'b1;
            alu_reg_pipeline_ready == 1'b1;
            dispatch_valid_mdu_by_way == 4'b0; // no mdu dispatch 
            mdu_pipeline_ready == 0; // no MDU ready
            dispatch_A_ready_by_way == 4'b0;
            dispatch_B_ready_by_way == 4'b0;
            dispatch_A_is_zero_by_way == 4'b0;
            dispatch_B_is_zero_by_way == 4'b0;
            WB_bus_valid_by_bank == '1; // all wb
            if(x1[0] == 'hz) {
                x1[0][6:2] == dispatch_A_PR_by_way[0];
            }
            else WB_bus_upper_PR_by_bank[0] == x1[0][6:2];

            if(x1[1] == 'hz) {
                x1[1][6:2] == dispatch_A_PR_by_way[1];
            }
            else WB_bus_upper_PR_by_bank[1] == x1[1][6:2];

            if(x2[0] == 'hz) {
                x2[0][6:2] == dispatch_B_PR_by_way[0];
            }
            else WB_bus_upper_PR_by_bank[2] == x2[0][6:2];

            if(x2[1] == 'hz) {
                x2[1][6:2] == dispatch_B_PR_by_way[1];
            }
            else WB_bus_upper_PR_by_bank[3] == x1[1][6:2];
            // foreach(x1[i]) {
            //     if(x1[i] !== 'hz) {
            //         WB_bus_upper_PR_by_bank[i] == x1[i][6:2];
            //     }
            //     else {
            //         x1[i][6:2] == WB_bus_upper_PR_by_bank[i];
            //     }
            //     if(x2[i] !== 'hz) begin
            //         WB_bus_upper_PR_by_bank[i] == x2[i][6:2];
            //     end
            //     else {
            //         x1[i][6:2] == WB_bus_upper_PR_by_bank[i];
            //     }
            // }
            // dispatch_A_PR_by_way == {WB_bus_upper_PR_by_bank[idx],idx};
            // dispatch_B_PR_by_way == {WB_bus_upper_PR_by_bank[idx2],idx2};
        };
        finish_item(standard_tx);
    endtask

endclass : reg_normal_pipe_wb


`endif