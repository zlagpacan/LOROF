/*
    Filename: upct_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around upct module. 
    Spec: LOROF/spec/design/upct.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module upct_wrapper #(
	parameter UPCT_ENTRIES = 8,
	parameter LOG_UPCT_ENTRIES = $clog2(UPCT_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,


    // RESP stage
	input logic next_read_valid_RESP,
	input logic [LOG_UPCT_ENTRIES-1:0] next_read_index_RESP,

	output logic [UPCT_ENTRIES-1:0][UPPER_PC_WIDTH-1:0] last_upct_array,

    // Update 0
	input logic next_update0_valid,
	input logic [31:0] next_update0_target_full_PC,

    // Update 1
	output logic [LOG_UPCT_ENTRIES-1:0] last_update1_upct_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // RESP stage
	logic read_valid_RESP;
	logic [LOG_UPCT_ENTRIES-1:0] read_index_RESP;

	logic [UPCT_ENTRIES-1:0][UPPER_PC_WIDTH-1:0] upct_array;

    // Update 0
	logic update0_valid;
	logic [31:0] update0_target_full_PC;

    // Update 1
	logic [LOG_UPCT_ENTRIES-1:0] update1_upct_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	upct #(
		.UPCT_ENTRIES(UPCT_ENTRIES),
		.LOG_UPCT_ENTRIES(LOG_UPCT_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // RESP stage
			read_valid_RESP <= '0;
			read_index_RESP <= '0;

			last_upct_array <= '0;

		    // Update 0
			update0_valid <= '0;
			update0_target_full_PC <= '0;

		    // Update 1
			last_update1_upct_index <= '0;
        end
        else begin


		    // RESP stage
			read_valid_RESP <= next_read_valid_RESP;
			read_index_RESP <= next_read_index_RESP;

			last_upct_array <= upct_array;

		    // Update 0
			update0_valid <= next_update0_valid;
			update0_target_full_PC <= next_update0_target_full_PC;

		    // Update 1
			last_update1_upct_index <= update1_upct_index;
        end
    end

endmodule