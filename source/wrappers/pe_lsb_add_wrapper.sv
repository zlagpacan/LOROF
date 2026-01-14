/*
    Filename: pe_lsb_add_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pe_lsb_add module. 
    Spec: LOROF/spec/design/pe_lsb_add.md
*/

`timescale 1ns/100ps


module pe_lsb_add_wrapper #(
	parameter WIDTH = 8
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [WIDTH-1:0] next_req_vec,

	output logic [WIDTH-1:0] last_ack_one_hot
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [WIDTH-1:0] req_vec;

	logic [WIDTH-1:0] ack_one_hot;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pe_lsb_add #(
		.WIDTH(WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_vec <= '0;

			last_ack_one_hot <= '0;
        end
        else begin
			req_vec <= next_req_vec;

			last_ack_one_hot <= ack_one_hot;
        end
    end

endmodule