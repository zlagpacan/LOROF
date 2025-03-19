/*
    Filename: free_list_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around free_list module. 
    Spec: LOROF/spec/design/free_list.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module free_list_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // enqueue request
	input logic [FREE_LIST_BANK_COUNT-1:0] next_enq_req_valid_by_bank,
	input logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0] next_enq_req_PR_by_bank,

    // enqueue feedback
	output logic [FREE_LIST_BANK_COUNT-1:0] last_enq_resp_ack_by_bank,

    // dequeue request
	input logic [FREE_LIST_BANK_COUNT-1:0] next_deq_req_valid_by_bank,
	output logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0] last_deq_req_PR_by_bank,

    // dequeue feedback
	output logic [FREE_LIST_BANK_COUNT-1:0] last_deq_resp_ready_by_bank
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // enqueue request
	logic [FREE_LIST_BANK_COUNT-1:0] enq_req_valid_by_bank;
	logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0] enq_req_PR_by_bank;

    // enqueue feedback
	logic [FREE_LIST_BANK_COUNT-1:0] enq_resp_ack_by_bank;

    // dequeue request
	logic [FREE_LIST_BANK_COUNT-1:0] deq_req_valid_by_bank;
	logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0] deq_req_PR_by_bank;

    // dequeue feedback
	logic [FREE_LIST_BANK_COUNT-1:0] deq_resp_ready_by_bank;

    // ----------------------------------------------------------------
    // Module Instantiation:

    free_list WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // enqueue request
			enq_req_valid_by_bank <= '0;
			enq_req_PR_by_bank <= '0;

		    // enqueue feedback
			last_enq_resp_ack_by_bank <= '0;

		    // dequeue request
			deq_req_valid_by_bank <= '0;
			last_deq_req_PR_by_bank <= '0;

		    // dequeue feedback
			last_deq_resp_ready_by_bank <= '0;
        end
        else begin

		    // enqueue request
			enq_req_valid_by_bank <= next_enq_req_valid_by_bank;
			enq_req_PR_by_bank <= next_enq_req_PR_by_bank;

		    // enqueue feedback
			last_enq_resp_ack_by_bank <= enq_resp_ack_by_bank;

		    // dequeue request
			deq_req_valid_by_bank <= next_deq_req_valid_by_bank;
			last_deq_req_PR_by_bank <= deq_req_PR_by_bank;

		    // dequeue feedback
			last_deq_resp_ready_by_bank <= deq_resp_ready_by_bank;
        end
    end

endmodule