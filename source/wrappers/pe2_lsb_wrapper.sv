/*
    Filename: pe2_lsb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pe2_lsb module. 
    Spec: LOROF/spec/design/pe2_lsb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter WIDTH = 8;

module pe2_lsb_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_req_vec,

	output logic [WIDTH-1:0] last_ack_one_hot,
	output logic [$clog2(WIDTH)-1:0] last_ack_index,

	output logic last_found_first,
	output logic last_found_second
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] req_vec;

	logic [WIDTH-1:0] ack_one_hot;
	logic [$clog2(WIDTH)-1:0] ack_index;

	logic found_first;
	logic found_second;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pe2_lsb #(
		.WIDTH(WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;

			last_ack_one_hot <= '0;
			last_ack_index <= '0;

			last_found_first <= '0;
			last_found_second <= '0;
        end
        else begin
			req_vec <= next_req_vec;

			last_ack_one_hot <= ack_one_hot;
			last_ack_index <= ack_index;

			last_found_first <= found_first;
			last_found_second <= found_second;
        end
    end

endmodule