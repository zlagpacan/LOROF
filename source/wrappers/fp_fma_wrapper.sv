/*
    Filename: fp_fma_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fp_fma module. 
    Spec: LOROF/spec/design/fp_fma.md
*/

`timescale 1ns/100ps

import lzc_wire::*;
import fp_wire::*;

module fp_fma_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,
	input fp_fma_in_type next_fp_fma_i,
	output fp_fma_out_type last_fp_fma_o,
	input lzc_256_out_type next_lzc_o,
	output lzc_256_in_type last_lzc_i,
	input  next_clear
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic reset;
	logic clock;
	fp_fma_in_type fp_fma_i;
	fp_fma_out_type fp_fma_o;
	lzc_256_out_type lzc_o;
	lzc_256_in_type lzc_i;
	logic clear;

    // ----------------------------------------------------------------
    // Module Instantiation:

    assign clock = CLK;
    assign reset = nRST;

	fp_fma #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			fp_fma_i <= '0;
			last_fp_fma_o <= '0;
			lzc_o <= '0;
			last_lzc_i <= '0;
			clear <= '0;
        end
        else begin
			fp_fma_i <= next_fp_fma_i;
			last_fp_fma_o <= fp_fma_o;
			lzc_o <= next_lzc_o;
			last_lzc_i <= lzc_i;
			clear <= next_clear;
        end
    end

endmodule