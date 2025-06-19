/*
    Filename: cb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around cb module. 
    Spec: LOROF/spec/design/cb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter DATA_WIDTH = 32;
parameter NUM_ENTRIES = 32;
parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES);

module cb_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // enq
	input logic next_enq_valid,
	input logic [DATA_WIDTH-1:0] next_enq_data,

    // deq
	output logic last_deq_valid,
	output logic [DATA_WIDTH-1:0] last_deq_data,

    // deq feedback
	input logic next_deq_ready
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // enq
	logic enq_valid;
	logic [DATA_WIDTH-1:0] enq_data;

    // deq
	logic deq_valid;
	logic [DATA_WIDTH-1:0] deq_data;

    // deq feedback
	logic deq_ready;

    // ----------------------------------------------------------------
    // Module Instantiation:

	cb #(
		.DATA_WIDTH(DATA_WIDTH),
		.NUM_ENTRIES(NUM_ENTRIES),
		.LOG_NUM_ENTRIES(LOG_NUM_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // enq
			enq_valid <= '0;
			enq_data <= '0;

		    // deq
			last_deq_valid <= '0;
			last_deq_data <= '0;

		    // deq feedback
			deq_ready <= '0;
        end
        else begin

		    // enq
			enq_valid <= next_enq_valid;
			enq_data <= next_enq_data;

		    // deq
			last_deq_valid <= deq_valid;
			last_deq_data <= deq_data;

		    // deq feedback
			deq_ready <= next_deq_ready;
        end
    end

endmodule