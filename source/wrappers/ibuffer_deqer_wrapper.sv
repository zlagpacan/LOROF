/*
    Filename: ibuffer_deqer_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ibuffer_deqer module. 
    Spec: LOROF/spec/design/ibuffer_deqer.md
*/

`timescale 1ns/100ps


module ibuffer_deqer_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

	input logic [15:0] next_valid_vec,
	input logic [15:0] next_uncompressed_vec,

	output logic [15:0][4:0] last_count_out_vec
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic [15:0] valid_vec;
	logic [15:0] uncompressed_vec;

	logic [15:0][4:0] count_out_vec;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ibuffer_deqer #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			valid_vec <= '0;
			uncompressed_vec <= '0;

			last_count_out_vec <= '0;
        end
        else begin

			valid_vec <= next_valid_vec;
			uncompressed_vec <= next_uncompressed_vec;

			last_count_out_vec <= count_out_vec;
        end
    end

endmodule