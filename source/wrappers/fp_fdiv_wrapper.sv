/*
    Filename: fp_fdiv_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fp_fdiv module. 
    Spec: LOROF/spec/design/fp_fdiv.md
*/

`timescale 1ns/100ps

import fp_wire::*;

module fp_fdiv_wrapper #(
	parameter int PERFORMANCE = 0
) (

    // seq
    input logic CLK,
    input logic nRST,
	input fp_fdiv_in_type next_fp_fdiv_i,
	output fp_fdiv_out_type last_fp_fdiv_o,
	input fp_mac_out_type next_fp_mac_o,
	output fp_mac_in_type last_fp_mac_i,
	input  next_clear
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic reset;
	logic clock;
	fp_fdiv_in_type fp_fdiv_i;
	fp_fdiv_out_type fp_fdiv_o;
	fp_mac_out_type fp_mac_o;
	fp_mac_in_type fp_mac_i;
	logic clear;

    // ----------------------------------------------------------------
    // Module Instantiation:

    assign clock = CLK;
    assign reset = nRST;

	fp_fdiv #(
		.PERFORMANCE(PERFORMANCE)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			fp_fdiv_i <= '0;
			last_fp_fdiv_o <= '0;
			fp_mac_o <= '0;
			last_fp_mac_i <= '0;
			clear <= '0;
        end
        else begin
			fp_fdiv_i <= next_fp_fdiv_i;
			last_fp_fdiv_o <= fp_fdiv_o;
			fp_mac_o <= next_fp_mac_o;
			last_fp_mac_i <= fp_mac_i;
			clear <= next_clear;
        end
    end

endmodule