/*
    Filename: peN_lsb_tree_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around peN_lsb_tree module. 
    Spec: LOROF/spec/design/peN_lsb_tree.md
*/

`timescale 1ns/100ps


module peN_lsb_tree_wrapper #(
	parameter int unsigned WIDTH = 8,
	parameter int unsigned N = 3,
	parameter int unsigned LOG_WIDTH = $clog2(WIDTH)
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_req_vec,

	output logic [N-1:0] last_ack_valid_by_n,
	output logic [N-1:0][LOG_WIDTH-1:0] last_ack_index_by_n
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] req_vec;

	logic [N-1:0] ack_valid_by_n;
	logic [N-1:0][LOG_WIDTH-1:0] ack_index_by_n;

    // ----------------------------------------------------------------
    // Module Instantiation:

	peN_lsb_tree #(
		.WIDTH(WIDTH),
		.N(N),
		.LOG_WIDTH(LOG_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;

			last_ack_valid_by_n <= '0;
			last_ack_index_by_n <= '0;
        end
        else begin
			req_vec <= next_req_vec;

			last_ack_valid_by_n <= ack_valid_by_n;
			last_ack_index_by_n <= ack_index_by_n;
        end
    end

endmodule