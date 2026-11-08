/*
    Filename: simple_comparator_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around simple_comparator module. 
    Spec: LOROF/spec/design/simple_comparator.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module simple_comparator_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [31:0] next_A,
	input logic [31:0] next_B,
	output logic last_eq,
	output logic last_lts,
	output logic last_ltu
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [31:0] A;
	logic [31:0] B;
	logic eq;
	logic lts;
	logic ltu;

    // ----------------------------------------------------------------
    // Module Instantiation:

    simple_comparator WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			A <= '0;
			B <= '0;
			last_eq <= '0;
			last_lts <= '0;
			last_ltu <= '0;
        end
        else begin
			A <= next_A;
			B <= next_B;
			last_eq <= eq;
			last_lts <= lts;
			last_ltu <= ltu;
        end
    end

endmodule