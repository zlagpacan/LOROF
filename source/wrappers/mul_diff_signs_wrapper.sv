/*
    Filename: mul_diff_signs_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mul_diff_signs module. 
    Spec: LOROF/spec/design/mul_diff_signs.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;


module mul_diff_signs_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

	input logic [31:0] next_A,
	input logic [31:0] next_B,

	input logic [1:0] next_sel,

	output logic [63:0] last_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic [31:0] A;
	logic [31:0] B;

	logic [1:0] sel;

	logic [63:0] out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mul_diff_signs #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			A <= '0;
			B <= '0;

			sel <= '0;

			last_out <= '0;
        end
        else begin

			A <= next_A;
			B <= next_B;

			sel <= next_sel;

			last_out <= out;
        end
    end

endmodule