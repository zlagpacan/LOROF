/*
    Filename: pe2_lsb_add_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pe2_lsb_add module. 
    Spec: LOROF/spec/design/pe2_lsb_add.md
*/

`timescale 1ns/100ps


module pe2_lsb_add_wrapper #(
	parameter int unsigned WIDTH = 8
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_req_vec,

	output logic last_ack0_valid,
	output logic [WIDTH-1:0] last_ack0_one_hot,

	output logic last_ack1_valid,
	output logic [WIDTH-1:0] last_ack1_one_hot
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] req_vec;

	logic ack0_valid;
	logic [WIDTH-1:0] ack0_one_hot;

	logic ack1_valid;
	logic [WIDTH-1:0] ack1_one_hot;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pe2_lsb_add #(
		.WIDTH(WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;

			last_ack0_valid <= '0;
			last_ack0_one_hot <= '0;

			last_ack1_valid <= '0;
			last_ack1_one_hot <= '0;
        end
        else begin
			req_vec <= next_req_vec;

			last_ack0_valid <= ack0_valid;
			last_ack0_one_hot <= ack0_one_hot;

			last_ack1_valid <= ack1_valid;
			last_ack1_one_hot <= ack1_one_hot;
        end
    end

endmodule