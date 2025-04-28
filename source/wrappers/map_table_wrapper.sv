/*
    Filename: map_table_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around map_table module. 
    Spec: LOROF/spec/design/map_table.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module map_table_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // read ports
	input logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_AR_COUNT-1:0] next_read_AR_by_port,
	output logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_PR_COUNT-1:0] last_read_PR_by_port,

    // write ports
	input logic [MAP_TABLE_WRITE_PORT_COUNT-1:0] next_write_valid_by_port,
	input logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_AR_COUNT-1:0] next_write_AR_by_port,
	input logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_PR_COUNT-1:0] next_write_PR_by_port,

    // checkpoint save
	output logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] last_save_map_table,

    // checkpoint restore
	input logic next_restore_valid,
	input logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] next_restore_map_table
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // read ports
	logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_AR_COUNT-1:0] read_AR_by_port;
	logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_PR_COUNT-1:0] read_PR_by_port;

    // write ports
	logic [MAP_TABLE_WRITE_PORT_COUNT-1:0] write_valid_by_port;
	logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_AR_COUNT-1:0] write_AR_by_port;
	logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_PR_COUNT-1:0] write_PR_by_port;

    // checkpoint save
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] save_map_table;

    // checkpoint restore
	logic restore_valid;
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] restore_map_table;

    // ----------------------------------------------------------------
    // Module Instantiation:

    map_table #(
		.MAP_TABLE_READ_PORT_COUNT(MAP_TABLE_READ_PORT_COUNT),
		.MAP_TABLE_WRITE_PORT_COUNT(MAP_TABLE_WRITE_PORT_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // read ports
			read_AR_by_port <= '0;
			last_read_PR_by_port <= '0;

		    // write ports
			write_valid_by_port <= '0;
			write_AR_by_port <= '0;
			write_PR_by_port <= '0;

		    // checkpoint save
			last_save_map_table <= '0;

		    // checkpoint restore
			restore_valid <= '0;
			restore_map_table <= '0;
        end
        else begin


		    // read ports
			read_AR_by_port <= next_read_AR_by_port;
			last_read_PR_by_port <= read_PR_by_port;

		    // write ports
			write_valid_by_port <= next_write_valid_by_port;
			write_AR_by_port <= next_write_AR_by_port;
			write_PR_by_port <= next_write_PR_by_port;

		    // checkpoint save
			last_save_map_table <= save_map_table;

		    // checkpoint restore
			restore_valid <= next_restore_valid;
			restore_map_table <= next_restore_map_table;
        end
    end

endmodule