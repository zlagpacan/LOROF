/*
    Module   : alu_pipeline
    Filename : sequence_item.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_TX_SV
`define ALU_PIPELINE_TX_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Dependencies --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- ALU Pipeline Sequence Item --- //
class alu_pipeline_seq_item extends uvm_sequence_item

    // --- Reset --- //
    logic nRST;

    // --- OP Issue : Signals --- //
    randc logic [3:0] op_in;

    // --- OP Issue : Constraints --- //
    constraint op_in_range {
        op_in inside {
            4'b0000,
            4'b0001,
            4'b0010,
            4'b0011,
            4'b0100,
            4'b0101,
            4'b0110,
            4'b0111,
            4'b1000,
            4'b1101,
            4'b1111
        };
    }

endclass : alu_pipeline_seq_item