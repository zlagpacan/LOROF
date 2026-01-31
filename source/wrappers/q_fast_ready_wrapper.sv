/*
    Filename: q_fast_ready_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around q_fast_ready module. 
    Spec: LOROF/spec/design/q_fast_ready.md
*/

`timescale 1ns/100ps


module q_fast_ready_wrapper #(
	parameter DATA_WIDTH = 32,
	parameter NUM_ENTRIES = 32,
	parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // enq
	input logic next_enq_valid,
	input logic [DATA_WIDTH-1:0] next_enq_data,

    // enq feedback
	output logic last_enq_ready,

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

    // enq feedback
	logic enq_ready;

    // deq
	logic deq_valid;
	logic [DATA_WIDTH-1:0] deq_data;

    // deq feedback
	logic deq_ready;

    // ----------------------------------------------------------------
    // Module Instantiation:

	q_fast_ready #(
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

		    // enq feedback
			last_enq_ready <= '0;

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

		    // enq feedback
			last_enq_ready <= enq_ready;

		    // deq
			last_deq_valid <= deq_valid;
			last_deq_data <= deq_data;

		    // deq feedback
			deq_ready <= next_deq_ready;
        end
    end

endmodule