/*
    Filename: one_hot_dec_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around one_hot_dec module. 
    Spec: LOROF/spec/design/one_hot_dec.md
*/

`timescale 1ns/100ps


module one_hot_dec_wrapper #(
	parameter WIDTH = 8
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic next_valid_in,
	input logic [$clog2(WIDTH)-1:0] next_index_in,

	output logic [WIDTH-1:0] last_one_hot_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic valid_in;
	logic [$clog2(WIDTH)-1:0] index_in;

	logic [WIDTH-1:0] one_hot_out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	one_hot_dec #(
		.WIDTH(WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			valid_in <= '0;
			index_in <= '0;

			last_one_hot_out <= '0;
        end
        else begin
			valid_in <= next_valid_in;
			index_in <= next_index_in;

			last_one_hot_out <= one_hot_out;
        end
    end

endmodule