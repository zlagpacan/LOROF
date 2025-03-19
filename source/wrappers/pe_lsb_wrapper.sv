/*
    Filename: pe_lsb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pe_lsb module. 
    Spec: LOROF/spec/design/pe_lsb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

parameter WIDTH = 8;

module pe_lsb_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_req_vec,
	output logic [WIDTH-1:0] last_ack_one_hot,
	output logic [WIDTH-1:0] last_ack_mask
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] req_vec;
	logic [WIDTH-1:0] ack_one_hot;
	logic [WIDTH-1:0] ack_mask;

    // ----------------------------------------------------------------
    // Module Instantiation:

    pe_lsb WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;
			last_ack_one_hot <= '0;
			last_ack_mask <= '0;
        end
        else begin
			req_vec <= next_req_vec;
			last_ack_one_hot <= ack_one_hot;
			last_ack_mask <= ack_mask;
        end
    end

endmodule