/*
    Filename: alu_reg_dq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_reg_dq module. 
    Spec: LOROF/spec/design/alu_reg_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_dq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // ALU op 4-wide enQ array
	input logic [3:0] next_enQ_valid_array,
	input logic [3:0][3:0] next_enQ_op_array,
	input logic [3:0][LOG_PR_COUNT-1:0] next_enQ_A_PR_array,
	input logic [3:0][LOG_PR_COUNT-1:0] next_enQ_B_PR_array,
	input logic [3:0][LOG_PR_COUNT-1:0] next_enQ_dest_PR_array,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_enQ_ROB_index_array,

    // ALU op 4-wide enQ feedback array
	output logic [3:0] last_enQ_ready_array,

    // ALU op 4-wide deQ array
	output logic [3:0] last_deQ_valid_array,
	output logic [3:0][3:0] last_deQ_op_array,
	output logic [3:0][LOG_PR_COUNT-1:0] last_deQ_A_PR_array,
	output logic [3:0][LOG_PR_COUNT-1:0] last_deQ_B_PR_array,
	output logic [3:0][LOG_PR_COUNT-1:0] last_deQ_dest_PR_array,
	output logic [3:0][LOG_ROB_ENTRIES-1:0] last_deQ_ROB_index_array,

    // ALU op 4-wide deQ feedback array
	input logic [3:0] next_deQ_ready_array
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // ALU op 4-wide enQ array
	logic [3:0] enQ_valid_array;
	logic [3:0][3:0] enQ_op_array;
	logic [3:0][LOG_PR_COUNT-1:0] enQ_A_PR_array;
	logic [3:0][LOG_PR_COUNT-1:0] enQ_B_PR_array;
	logic [3:0][LOG_PR_COUNT-1:0] enQ_dest_PR_array;
	logic [3:0][LOG_ROB_ENTRIES-1:0] enQ_ROB_index_array;

    // ALU op 4-wide enQ feedback array
	logic [3:0] enQ_ready_array;

    // ALU op 4-wide deQ array
	logic [3:0] deQ_valid_array;
	logic [3:0][3:0] deQ_op_array;
	logic [3:0][LOG_PR_COUNT-1:0] deQ_A_PR_array;
	logic [3:0][LOG_PR_COUNT-1:0] deQ_B_PR_array;
	logic [3:0][LOG_PR_COUNT-1:0] deQ_dest_PR_array;
	logic [3:0][LOG_ROB_ENTRIES-1:0] deQ_ROB_index_array;

    // ALU op 4-wide deQ feedback array
	logic [3:0] deQ_ready_array;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_reg_dq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // ALU op 4-wide enQ array
			enQ_valid_array <= '0;
			enQ_op_array <= '0;
			enQ_A_PR_array <= '0;
			enQ_B_PR_array <= '0;
			enQ_dest_PR_array <= '0;
			enQ_ROB_index_array <= '0;

		    // ALU op 4-wide enQ feedback array
			last_enQ_ready_array <= '0;

		    // ALU op 4-wide deQ array
			last_deQ_valid_array <= '0;
			last_deQ_op_array <= '0;
			last_deQ_A_PR_array <= '0;
			last_deQ_B_PR_array <= '0;
			last_deQ_dest_PR_array <= '0;
			last_deQ_ROB_index_array <= '0;

		    // ALU op 4-wide deQ feedback array
			deQ_ready_array <= '0;
        end
        else begin


		    // ALU op 4-wide enQ array
			enQ_valid_array <= next_enQ_valid_array;
			enQ_op_array <= next_enQ_op_array;
			enQ_A_PR_array <= next_enQ_A_PR_array;
			enQ_B_PR_array <= next_enQ_B_PR_array;
			enQ_dest_PR_array <= next_enQ_dest_PR_array;
			enQ_ROB_index_array <= next_enQ_ROB_index_array;

		    // ALU op 4-wide enQ feedback array
			last_enQ_ready_array <= enQ_ready_array;

		    // ALU op 4-wide deQ array
			last_deQ_valid_array <= deQ_valid_array;
			last_deQ_op_array <= deQ_op_array;
			last_deQ_A_PR_array <= deQ_A_PR_array;
			last_deQ_B_PR_array <= deQ_B_PR_array;
			last_deQ_dest_PR_array <= deQ_dest_PR_array;
			last_deQ_ROB_index_array <= deQ_ROB_index_array;

		    // ALU op 4-wide deQ feedback array
			deQ_ready_array <= next_deQ_ready_array;
        end
    end

endmodule