/*
    Filename: stupid_mul_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stupid_mul module. 
    Spec: LOROF/spec/design/stupid_mul.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stupid_mul_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

	input logic signed [31:0] next_A,
	input logic signed [31:0] next_B,

	output logic signed [63:0] last_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic signed [31:0] A;
	logic signed [31:0] B;

	logic signed [63:0] out;

    // ----------------------------------------------------------------
    // Module Instantiation:

    stupid_mul WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			A <= '0;
			B <= '0;

			last_out <= '0;
        end
        else begin

			A <= next_A;
			B <= next_B;

			last_out <= out;
        end
    end

endmodule