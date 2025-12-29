/*
    Filename: mem_map_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mem_map module. 
    Spec: LOROF/spec/design/mem_map.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module mem_map_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

    // input
	input logic [PPN_WIDTH-1:0] next_PPN,

    // output
	output logic last_DRAM,
	output logic last_ROM,
	output logic last_IO
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // input
	logic [PPN_WIDTH-1:0] PPN;

    // output
	logic DRAM;
	logic ROM;
	logic IO;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mem_map #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // input
			PPN <= '0;

		    // output
			last_DRAM <= '0;
			last_ROM <= '0;
			last_IO <= '0;
        end
        else begin

		    // input
			PPN <= next_PPN;

		    // output
			last_DRAM <= DRAM;
			last_ROM <= ROM;
			last_IO <= IO;
        end
    end

endmodule