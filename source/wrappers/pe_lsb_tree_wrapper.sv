/*
    Filename: pe_lsb_tree_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pe_lsb_tree module. 
    Spec: LOROF/spec/design/pe_lsb_tree.md
*/

`timescale 1ns/100ps


module pe_lsb_tree_wrapper #(
	parameter int unsigned WIDTH = 8,
	parameter int unsigned LEVELS = $clog2(WIDTH)
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_req_vec,

	output logic last_ack_valid,
	output logic [LEVELS-1:0] last_ack_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] req_vec;

	logic ack_valid;
	logic [LEVELS-1:0] ack_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pe_lsb_tree #(
		.WIDTH(WIDTH),
		.LEVELS(LEVELS)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;

			last_ack_valid <= '0;
			last_ack_index <= '0;
        end
        else begin
			req_vec <= next_req_vec;

			last_ack_valid <= ack_valid;
			last_ack_index <= ack_index;
        end
    end

endmodule