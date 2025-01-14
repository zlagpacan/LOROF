/*
    Filename: pq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pq module. 
    Spec: LOROF/spec/design/pq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module pq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [14-1:0] next_req_vec,
	output logic [14-1:0] last_pq_vec
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [14-1:0] req_vec;
	logic [14-1:0] pq_vec;

    // ----------------------------------------------------------------
    // Module Instantiation:

    pq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;
			last_pq_vec <= '0;
        end
        else begin
			req_vec <= next_req_vec;
			last_pq_vec <= pq_vec;
        end
    end

endmodule