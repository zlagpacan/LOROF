/*
    Filename: div64_nonrestoring_skip_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around div64_nonrestoring_skip module. 
    Spec: LOROF/spec/design/div64_nonrestoring_skip.md
*/

`timescale 1ns/100ps


module div64_nonrestoring_skip_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // fsm control
	input logic next_clear,
	input logic next_is_signed,
	output logic last_done,
	input logic next_stall_if_done,

    // inputs
	input logic [63:0] next_A64_in,
	input logic [63:0] next_B64_in,

    // outputs
	output logic [63:0] last_quotient_out,
	output logic [63:0] last_remainder_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // fsm control
	logic clear;
	logic is_signed;
	logic done;
	logic stall_if_done;

    // inputs
	logic [63:0] A64_in;
	logic [63:0] B64_in;

    // outputs
	logic [63:0] quotient_out;
	logic [63:0] remainder_out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	div64_nonrestoring_skip #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // fsm control
			clear <= '0;
			is_signed <= '0;
			last_done <= '0;
			stall_if_done <= '0;

		    // inputs
			A64_in <= '0;
			B64_in <= '0;

		    // outputs
			last_quotient_out <= '0;
			last_remainder_out <= '0;
        end
        else begin


		    // fsm control
			clear <= next_clear;
			is_signed <= next_is_signed;
			last_done <= done;
			stall_if_done <= next_stall_if_done;

		    // inputs
			A64_in <= next_A64_in;
			B64_in <= next_B64_in;

		    // outputs
			last_quotient_out <= quotient_out;
			last_remainder_out <= remainder_out;
        end
    end

endmodule