/*
    Filename: ibuffer_marker_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ibuffer_marker module. 
    Spec: LOROF/spec/design/ibuffer_marker.md
*/

`timescale 1ns/100ps


module ibuffer_marker_wrapper #(
	parameter int unsigned WIDTH = 8
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_valid_vec,
	input logic [WIDTH-1:0] next_uncompressed_vec,

	output logic [WIDTH-1:0] last_marker_vec
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] valid_vec;
	logic [WIDTH-1:0] uncompressed_vec;

	logic [WIDTH-1:0] marker_vec;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ibuffer_marker #(
		.WIDTH(WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			valid_vec <= '0;
			uncompressed_vec <= '0;

			last_marker_vec <= '0;
        end
        else begin
			valid_vec <= next_valid_vec;
			uncompressed_vec <= next_uncompressed_vec;

			last_marker_vec <= marker_vec;
        end
    end

endmodule