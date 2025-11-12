/*
    Filename: arbiter2_rr_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around arbiter2_rr module. 
    Spec: LOROF/spec/design/arbiter2_rr.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module arbiter2_rr_wrapper #(
	parameter REQUESTOR_COUNT = 8,
	parameter LOG_REQUESTOR_COUNT = $clog2(REQUESTOR_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

	input logic next_req_valid,
	input logic [REQUESTOR_COUNT-1:0] next_req_vec,

	output logic last_port0_ack_valid,
	output logic [REQUESTOR_COUNT-1:0] last_port0_ack_one_hot,

	output logic last_port1_ack_valid,
	output logic [REQUESTOR_COUNT-1:0] last_port1_ack_one_hot
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic req_valid;
	logic [REQUESTOR_COUNT-1:0] req_vec;

	logic port0_ack_valid;
	logic [REQUESTOR_COUNT-1:0] port0_ack_one_hot;

	logic port1_ack_valid;
	logic [REQUESTOR_COUNT-1:0] port1_ack_one_hot;

    // ----------------------------------------------------------------
    // Module Instantiation:

	arbiter2_rr #(
		.REQUESTOR_COUNT(REQUESTOR_COUNT),
		.LOG_REQUESTOR_COUNT(LOG_REQUESTOR_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			req_valid <= '0;
			req_vec <= '0;

			last_port0_ack_valid <= '0;
			last_port0_ack_one_hot <= '0;

			last_port1_ack_valid <= '0;
			last_port1_ack_one_hot <= '0;
        end
        else begin

			req_valid <= next_req_valid;
			req_vec <= next_req_vec;

			last_port0_ack_valid <= port0_ack_valid;
			last_port0_ack_one_hot <= port0_ack_one_hot;

			last_port1_ack_valid <= port1_ack_valid;
			last_port1_ack_one_hot <= port1_ack_one_hot;
        end
    end

endmodule