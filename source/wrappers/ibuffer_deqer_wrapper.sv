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
	input logic [15:0] next_redirect_vec,

	output logic [15:0][4:0] last_count_vec,
	output logic [15:0] last_deqing_vec,

	output logic [3:0] last_valid_by_way,
	output logic [3:0][3:0] last_first_idx_by_way,
	output logic [3:0][3:0] last_second_idx_by_way
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic [15:0] valid_vec;
	logic [15:0] uncompressed_vec;
	logic [15:0] redirect_vec;

	logic [15:0][4:0] count_vec;
	logic [15:0] deqing_vec;

	logic [3:0] valid_by_way;
	logic [3:0][3:0] first_idx_by_way;
	logic [3:0][3:0] second_idx_by_way;

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
			redirect_vec <= '0;

			last_count_vec <= '0;
			last_deqing_vec <= '0;

			last_valid_by_way <= '0;
			last_first_idx_by_way <= '0;
			last_second_idx_by_way <= '0;
        end
        else begin

			valid_vec <= next_valid_vec;
			uncompressed_vec <= next_uncompressed_vec;
			redirect_vec <= next_redirect_vec;

			last_count_vec <= count_vec;
			last_deqing_vec <= deqing_vec;

			last_valid_by_way <= valid_by_way;
			last_first_idx_by_way <= first_idx_by_way;
			last_second_idx_by_way <= second_idx_by_way;
        end
    end

endmodule