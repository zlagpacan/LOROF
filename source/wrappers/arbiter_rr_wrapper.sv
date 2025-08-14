/*
    Filename: arbiter_rr_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around arbiter_rr module. 
    Spec: LOROF/spec/design/arbiter_rr.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter REQUESTER_COUNT = 4;
parameter LOG_REQUESTER_COUNT = $clog2(REQUESTER_COUNT);

module arbiter_rr_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

	input logic [REQUESTER_COUNT-1:0] next_req_vec,
	output logic last_req_present,

	input logic next_ack_ready,
	output logic [REQUESTER_COUNT-1:0] last_ack_one_hot,
	output logic [LOG_REQUESTER_COUNT-1:0] last_ack_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic [REQUESTER_COUNT-1:0] req_vec;
	logic req_present;

	logic ack_ready;
	logic [REQUESTER_COUNT-1:0] ack_one_hot;
	logic [LOG_REQUESTER_COUNT-1:0] ack_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	arbiter_rr #(
		.REQUESTER_COUNT(REQUESTER_COUNT),
		.LOG_REQUESTER_COUNT(LOG_REQUESTER_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			req_vec <= '0;
			last_req_present <= '0;

			ack_ready <= '0;
			last_ack_one_hot <= '0;
			last_ack_index <= '0;
        end
        else begin

			req_vec <= next_req_vec;
			last_req_present <= req_present;

			ack_ready <= next_ack_ready;
			last_ack_one_hot <= ack_one_hot;
			last_ack_index <= ack_index;
        end
    end

endmodule