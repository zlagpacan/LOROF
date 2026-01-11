/*
    Filename: alu_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu module. 
    Spec: LOROF/spec/design/alu.md
*/

`timescale 1ns/100ps

`include "instr_types.vh"

module alu_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [3:0] next_op,
	input logic [63:0] next_A,
	input logic [63:0] next_B,

	output logic [63:0] last_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [3:0] op;
	logic [63:0] A;
	logic [63:0] B;

	logic [63:0] out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	alu #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			op <= '0;
			A <= '0;
			B <= '0;

			last_out <= '0;
        end
        else begin
			op <= next_op;
			A <= next_A;
			B <= next_B;

			last_out <= out;
        end
    end

endmodule