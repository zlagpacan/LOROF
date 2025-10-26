/*
    Filename: div_stupid_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around div_stupid module. 
    Spec: LOROF/spec/design/div_stupid.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module div_stupid_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

	input logic signed [31:0] next_A,
	input logic signed [31:0] next_B,

	output logic signed [31:0] last_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic signed [31:0] A;
	logic signed [31:0] B;

	logic signed [31:0] out;

    // ----------------------------------------------------------------
    // Module Instantiation:

    div_stupid WRAPPED_MODULE (.*);

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