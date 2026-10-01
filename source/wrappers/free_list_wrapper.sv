/*
    Filename: free_list_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around free_list module. 
    Spec: LOROF/spec/design/free_list.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module free_list_wrapper #(
	parameter int unsigned INGRESS_BUFFER_ENTRIES = 16,
	parameter int unsigned EGRESS_BUFFER_ENTRIES = 16
) (

    // seq
    input logic CLK,
    input logic nRST,

    // enq
	input logic [3:0] next_enq_valid_by_way,
	input corep::pr_t [3:0] next_enq_pr_by_way,

    // enq feedback
	output logic [3:0] last_enq_ready_by_way,

    // deq
	output logic [3:0] last_deq_valid_by_way,
	output corep::pr_t [3:0] last_deq_pr_by_way,

    // deq feedback
	input logic [3:0] next_deq_ready_by_way
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // enq
	logic [3:0] enq_valid_by_way;
	corep::pr_t [3:0] enq_pr_by_way;

    // enq feedback
	logic [3:0] enq_ready_by_way;

    // deq
	logic [3:0] deq_valid_by_way;
	corep::pr_t [3:0] deq_pr_by_way;

    // deq feedback
	logic [3:0] deq_ready_by_way;

    // ----------------------------------------------------------------
    // Module Instantiation:

	free_list #(
		.INGRESS_BUFFER_ENTRIES(INGRESS_BUFFER_ENTRIES),
		.EGRESS_BUFFER_ENTRIES(EGRESS_BUFFER_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // enq
			enq_valid_by_way <= '0;
			enq_pr_by_way <= '0;

		    // enq feedback
			last_enq_ready_by_way <= '0;

		    // deq
			last_deq_valid_by_way <= '0;
			last_deq_pr_by_way <= '0;

		    // deq feedback
			deq_ready_by_way <= '0;
        end
        else begin

		    // enq
			enq_valid_by_way <= next_enq_valid_by_way;
			enq_pr_by_way <= next_enq_pr_by_way;

		    // enq feedback
			last_enq_ready_by_way <= enq_ready_by_way;

		    // deq
			last_deq_valid_by_way <= deq_valid_by_way;
			last_deq_pr_by_way <= deq_pr_by_way;

		    // deq feedback
			deq_ready_by_way <= next_deq_ready_by_way;
        end
    end

endmodule