/*
    Filename: majority_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around majority module. 
    Spec: LOROF/spec/design/majority.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter WIDTH = 8;
parameter THRESHOLD = 4;

module majority_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_vec,
	output logic last_above_threshold
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] vec;
	logic above_threshold;

    // ----------------------------------------------------------------
    // Module Instantiation:

	majority #(
		.WIDTH(WIDTH),
		.THRESHOLD(THRESHOLD)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			vec <= '0;
			last_above_threshold <= '0;
        end
        else begin
			vec <= next_vec;
			last_above_threshold <= above_threshold;
        end
    end

endmodule