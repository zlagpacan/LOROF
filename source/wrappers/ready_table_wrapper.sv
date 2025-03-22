/*
    Filename: ready_table_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ready_table module. 
    Spec: LOROF/spec/design/ready_table.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ready_table_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // 8x read ports
	input logic [7:0][LOG_PR_COUNT-1:0] next_read_PR_by_port,
	output logic [7:0] last_read_ready_by_port,

    // 4x set ports
	input logic [3:0] next_set_valid_by_port,
	input logic [3:0][LOG_PR_COUNT-1:0] next_set_PR_by_port,

    // 4x clear ports
	input logic [3:0] next_clear_valid_by_port,
	input logic [3:0][LOG_PR_COUNT-1:0] next_clear_PR_by_port
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // 8x read ports
	logic [7:0][LOG_PR_COUNT-1:0] read_PR_by_port;
	logic [7:0] read_ready_by_port;

    // 4x set ports
	logic [3:0] set_valid_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] set_PR_by_port;

    // 4x clear ports
	logic [3:0] clear_valid_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] clear_PR_by_port;

    // ----------------------------------------------------------------
    // Module Instantiation:

    ready_table WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // 8x read ports
			read_PR_by_port <= '0;
			last_read_ready_by_port <= '0;

		    // 4x set ports
			set_valid_by_port <= '0;
			set_PR_by_port <= '0;

		    // 4x clear ports
			clear_valid_by_port <= '0;
			clear_PR_by_port <= '0;
        end
        else begin


		    // 8x read ports
			read_PR_by_port <= next_read_PR_by_port;
			last_read_ready_by_port <= read_ready_by_port;

		    // 4x set ports
			set_valid_by_port <= next_set_valid_by_port;
			set_PR_by_port <= next_set_PR_by_port;

		    // 4x clear ports
			clear_valid_by_port <= next_clear_valid_by_port;
			clear_PR_by_port <= next_clear_PR_by_port;
        end
    end

endmodule