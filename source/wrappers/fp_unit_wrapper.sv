/*
    Filename: fp_unit_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fp_unit module. 
    Spec: LOROF/spec/design/fp_unit.md
*/

`timescale 1ns/100ps

import lzc_wire::*;
import fp_wire::*;

module fp_unit_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,
	input fp_unit_in_type next_fp_unit_i,
	// output fp_unit_out_type last_fp_unit_o,
	// output fp_unit_out_type last_last_fp_unit_o,
	output fp_unit_out_type last_last_last_fp_unit_o,
	input  next_clear
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic reset;
	logic clock;
	fp_unit_in_type fp_unit_i;
	fp_unit_out_type fp_unit_o;
	logic clear;

    fp_unit_out_type last_fp_unit_o;
    fp_unit_out_type last_last_fp_unit_o;

    // ----------------------------------------------------------------
    // Module Instantiation:

    assign clock = CLK;
    assign reset = nRST;

	fp_unit #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			fp_unit_i <= '0;
			last_fp_unit_o <= '0;
			last_last_fp_unit_o <= '0;
			last_last_last_fp_unit_o <= '0;
			clear <= '0;
        end
        else begin
			fp_unit_i <= next_fp_unit_i;
			last_fp_unit_o <= fp_unit_o;
            last_last_fp_unit_o <= last_fp_unit_o;
            last_last_last_fp_unit_o <= last_last_fp_unit_o;
			clear <= next_clear;
        end
    end

endmodule