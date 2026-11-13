/*
    Filename: mul_diff_signs_65_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mul_diff_signs_65 module. 
    Spec: LOROF/spec/design/mul_diff_signs_65.md
*/

`timescale 1ns/100ps


module mul_diff_signs_65_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

	input logic [63:0] next_A,
	input logic [63:0] next_B,

	input logic [1:0] next_sel,

	output logic [127:0] last_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic [63:0] A;
	logic [63:0] B;

	logic [1:0] sel;

	logic [127:0] out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mul_diff_signs_65 #(
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