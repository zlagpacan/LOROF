/*
    Filename: div32_nonrestoring_skip_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around div32_nonrestoring_skip module. 
    Spec: LOROF/spec/design/div32_nonrestoring_skip.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module div32_nonrestoring_skip_wrapper #(
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
	input logic [31:0] next_A32_in,
	input logic [31:0] next_B32_in,

    // outputs
	output logic [31:0] last_quotient_out,
	output logic [31:0] last_remainder_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // fsm control
	logic clear;
	logic is_signed;
	logic done;
	logic stall_if_done;

    // inputs
	logic [31:0] A32_in;
	logic [31:0] B32_in;

    // outputs
	logic [31:0] quotient_out;
	logic [31:0] remainder_out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	div32_nonrestoring_skip #(
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
			A32_in <= '0;
			B32_in <= '0;

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
			A32_in <= next_A32_in;
			B32_in <= next_B32_in;

		    // outputs
			last_quotient_out <= quotient_out;
			last_remainder_out <= remainder_out;
        end
    end

endmodule