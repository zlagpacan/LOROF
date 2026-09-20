/*
    Filename: pmux_lsb_for_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pmux_lsb_for module. 
    Spec: LOROF/spec/design/pmux_lsb_for.md
*/

`timescale 1ns/100ps


module pmux_lsb_for_wrapper #(
	parameter int unsigned SEL_WIDTH = 8,
	parameter int unsigned DATA_WIDTH = 8
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [SEL_WIDTH-1:0] next_req_valid_vec,
	input logic [SEL_WIDTH-1:0][DATA_WIDTH-1:0] next_req_data_vec,

	output logic [SEL_WIDTH-1:0] last_resp_valid_vec,
	output logic [DATA_WIDTH-1:0] last_resp_data
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [SEL_WIDTH-1:0] req_valid_vec;
	logic [SEL_WIDTH-1:0][DATA_WIDTH-1:0] req_data_vec;

	logic [SEL_WIDTH-1:0] resp_valid_vec;
	logic [DATA_WIDTH-1:0] resp_data;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pmux_lsb_for #(
		.SEL_WIDTH(SEL_WIDTH),
		.DATA_WIDTH(DATA_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			req_valid_vec <= '0;
			req_data_vec <= '0;

			last_resp_valid_vec <= '0;
			last_resp_data <= '0;
        end
        else begin
			req_valid_vec <= next_req_valid_vec;
			req_data_vec <= next_req_data_vec;

			last_resp_valid_vec <= resp_valid_vec;
			last_resp_data <= resp_data;
        end
    end

endmodule