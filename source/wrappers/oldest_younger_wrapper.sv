/*
    Filename: oldest_younger_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around oldest_younger module. 
    Spec: LOROF/spec/design/oldest_younger.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module oldest_younger_wrapper #(
	parameter VECTOR_WIDTH = 8,
	parameter INDEX_WIDTH = $clog2(VECTOR_WIDTH)
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [VECTOR_WIDTH-1:0] next_req_vec,

	input logic [INDEX_WIDTH-1:0] next_head_index,
	input logic [VECTOR_WIDTH-1:0] next_head_mask,

	input logic [INDEX_WIDTH-1:0] next_target_index,
	input logic [VECTOR_WIDTH-1:0] next_target_mask,

	output logic last_younger_present,
	output logic [INDEX_WIDTH-1:0] last_oldest_younger_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [VECTOR_WIDTH-1:0] req_vec;

	logic [INDEX_WIDTH-1:0] head_index;
	logic [VECTOR_WIDTH-1:0] head_mask;

	logic [INDEX_WIDTH-1:0] target_index;
	logic [VECTOR_WIDTH-1:0] target_mask;

	logic younger_present;
	logic [INDEX_WIDTH-1:0] oldest_younger_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	oldest_younger #(
		.VECTOR_WIDTH(VECTOR_WIDTH),
		.INDEX_WIDTH(INDEX_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;

			head_index <= '0;
			head_mask <= '0;

			target_index <= '0;
			target_mask <= '0;

			last_younger_present <= '0;
			last_oldest_younger_index <= '0;
        end
        else begin
			req_vec <= next_req_vec;

			head_index <= next_head_index;
			head_mask <= next_head_mask;

			target_index <= next_target_index;
			target_mask <= next_target_mask;

			last_younger_present <= younger_present;
			last_oldest_younger_index <= oldest_younger_index;
        end
    end

endmodule