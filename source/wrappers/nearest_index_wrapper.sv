/*
    Filename: nearest_index_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around nearest_index module. 
    Spec: LOROF/spec/design/nearest_index.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter VECTOR_WIDTH = 32;
parameter INDEX_WIDTH = $clog2(VECTOR_WIDTH);

module nearest_index_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [VECTOR_WIDTH-1:0] next_bit_vector,
	input logic [INDEX_WIDTH-1:0] next_target_index,

	output logic last_bit_present,
	output logic [INDEX_WIDTH-1:0] last_nearest_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [VECTOR_WIDTH-1:0] bit_vector;
	logic [INDEX_WIDTH-1:0] target_index;

	logic bit_present;
	logic [INDEX_WIDTH-1:0] nearest_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	nearest_index #(
		.VECTOR_WIDTH(VECTOR_WIDTH),
		.INDEX_WIDTH(INDEX_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			bit_vector <= '0;
			target_index <= '0;

			last_bit_present <= '0;
			last_nearest_index <= '0;
        end
        else begin
			bit_vector <= next_bit_vector;
			target_index <= next_target_index;

			last_bit_present <= bit_present;
			last_nearest_index <= nearest_index;
        end
    end

endmodule