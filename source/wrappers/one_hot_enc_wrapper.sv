/*
    Filename: one_hot_enc_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around one_hot_enc module. 
    Spec: LOROF/spec/design/one_hot_enc.md
*/

`timescale 1ns/100ps


module one_hot_enc_wrapper #(
	parameter WIDTH = 8
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_one_hot_in,

	output logic last_valid_out,
	output logic [$clog2(WIDTH)-1:0] last_index_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] one_hot_in;

	logic valid_out;
	logic [$clog2(WIDTH)-1:0] index_out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	one_hot_enc #(
		.WIDTH(WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			one_hot_in <= '0;

			last_valid_out <= '0;
			last_index_out <= '0;
        end
        else begin
			one_hot_in <= next_one_hot_in;

			last_valid_out <= valid_out;
			last_index_out <= index_out;
        end
    end

endmodule