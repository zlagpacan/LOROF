/*
    Filename: ras_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ras module. 
    Spec: LOROF/spec/design/ras.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ras_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // RESP stage
	input logic next_link_RESP,
	input logic [31:0] next_link_full_PC_RESP,
	input logic next_ret_RESP,

	output logic [31:0] last_ret_full_PC_RESP,
	output logic [RAS_INDEX_WIDTH-1:0] last_ras_index_RESP,

    // Update 0
	input logic next_update0_valid,
	input logic [RAS_INDEX_WIDTH-1:0] next_update0_ras_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // RESP stage
	logic link_RESP;
	logic [31:0] link_full_PC_RESP;
	logic ret_RESP;

	logic [31:0] ret_full_PC_RESP;
	logic [RAS_INDEX_WIDTH-1:0] ras_index_RESP;

    // Update 0
	logic update0_valid;
	logic [RAS_INDEX_WIDTH-1:0] update0_ras_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

    ras WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // RESP stage
			link_RESP <= '0;
			link_full_PC_RESP <= '0;
			ret_RESP <= '0;

			last_ret_full_PC_RESP <= '0;
			last_ras_index_RESP <= '0;

		    // Update 0
			update0_valid <= '0;
			update0_ras_index <= '0;
        end
        else begin


		    // RESP stage
			link_RESP <= next_link_RESP;
			link_full_PC_RESP <= next_link_full_PC_RESP;
			ret_RESP <= next_ret_RESP;

			last_ret_full_PC_RESP <= ret_full_PC_RESP;
			last_ras_index_RESP <= ras_index_RESP;

		    // Update 0
			update0_valid <= next_update0_valid;
			update0_ras_index <= next_update0_ras_index;
        end
    end

endmodule