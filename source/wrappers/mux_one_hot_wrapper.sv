/*
    Filename: mux_one_hot_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mux_one_hot module. 
    Spec: LOROF/spec/design/mux_one_hot.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module mux_one_hot_wrapper #(
	parameter COUNT = 4,
	parameter WIDTH = 32
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [COUNT-1:0] next_sel_one_hot,
	input logic [COUNT-1:0][WIDTH-1:0] next_data_by_requestor,

	output logic [WIDTH-1:0] last_selected_data
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [COUNT-1:0] sel_one_hot;
	logic [COUNT-1:0][WIDTH-1:0] data_by_requestor;

	logic [WIDTH-1:0] selected_data;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mux_one_hot #(
		.COUNT(COUNT),
		.WIDTH(WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			sel_one_hot <= '0;
			data_by_requestor <= '0;

			last_selected_data <= '0;
        end
        else begin
			sel_one_hot <= next_sel_one_hot;
			data_by_requestor <= next_data_by_requestor;

			last_selected_data <= selected_data;
        end
    end

endmodule