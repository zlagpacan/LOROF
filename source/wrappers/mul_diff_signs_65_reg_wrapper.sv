/*
    Filename: mul_diff_signs_65_reg_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mul_diff_signs_65_reg module. 
    Spec: LOROF/spec/design/mul_diff_signs_65_reg.md
*/

`timescale 1ns/100ps


module mul_diff_signs_65_reg_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

	input logic [63:0] next_A,
	input logic [63:0] next_B,

	input logic [1:0] next_sel,

	output logic [127:0] last_out_reg_reg
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic [63:0] A;
	logic [63:0] B;

	logic [1:0] sel;

	logic [127:0] out_reg_reg;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mul_diff_signs_65_reg #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			A <= '0;
			B <= '0;

			sel <= '0;

			last_out_reg_reg <= '0;
        end
        else begin

			A <= next_A;
			B <= next_B;

			sel <= next_sel;

			last_out_reg_reg <= out_reg_reg;
        end
    end

endmodule