/*
    Filename: countones_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around countones module. 
    Spec: LOROF/spec/design/countones.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module countones_wrapper #(
    parameter WIDTH = 28
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_input_vec,

	output logic [$clog2(WIDTH+1)-1:0] last_countones
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] input_vec;

	logic [$clog2(WIDTH+1)-1:0] countones;

    // ----------------------------------------------------------------
    // Module Instantiation:

    countones #(.WIDTH(WIDTH)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			input_vec <= '0;

			last_countones <= '0;
        end
        else begin
			input_vec <= next_input_vec;

			last_countones <= countones;
        end
    end

endmodule