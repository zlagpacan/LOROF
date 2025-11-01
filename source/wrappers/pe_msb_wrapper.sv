/*
    Filename: pe_msb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pe_msb module. 
    Spec: LOROF/spec/design/pe_msb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module pe_msb_wrapper #(
	parameter WIDTH = 8,
	parameter USE_ONE_HOT = 1,
	parameter USE_COLD = 0,
	parameter USE_INDEX = 0
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_req_vec,

	output logic [WIDTH-1:0] last_ack_one_hot,
	output logic [WIDTH-1:0] last_ack_mask,
	output logic [WIDTH-1:0] last_cold_ack_mask,
	output logic [$clog2(WIDTH)-1:0] last_ack_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] req_vec;

	logic [WIDTH-1:0] ack_one_hot;
	logic [WIDTH-1:0] ack_mask;
	logic [WIDTH-1:0] cold_ack_mask;
	logic [$clog2(WIDTH)-1:0] ack_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pe_msb #(
		.WIDTH(WIDTH),
		.USE_ONE_HOT(USE_ONE_HOT),
		.USE_COLD(USE_COLD),
		.USE_INDEX(USE_INDEX)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;

			last_ack_one_hot <= '0;
			last_ack_mask <= '0;
			last_cold_ack_mask <= '0;
			last_ack_index <= '0;
        end
        else begin
			req_vec <= next_req_vec;

			last_ack_one_hot <= ack_one_hot;
			last_ack_mask <= ack_mask;
			last_cold_ack_mask <= cold_ack_mask;
			last_ack_index <= ack_index;
        end
    end

endmodule