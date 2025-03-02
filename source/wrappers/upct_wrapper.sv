/*
    Filename: upct_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around upct module. 
    Spec: LOROF/spec/design/upct.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module upct_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // RESP stage
	input logic next_valid_RESP,
	input logic [LOG_UPCT_ENTRIES-1:0] next_upct_index_RESP,
	output logic [UPPER_PC_WIDTH-1:0] last_upper_PC_RESP,

    // Update 0
	input logic next_update0_valid,
	input logic [31:0] next_update0_start_full_PC,

    // Update 1
	output logic [LOG_UPCT_ENTRIES-1:0] last_update1_upct_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // RESP stage
	logic valid_RESP;
	logic [LOG_UPCT_ENTRIES-1:0] upct_index_RESP;
	logic [UPPER_PC_WIDTH-1:0] upper_PC_RESP;

    // Update 0
	logic update0_valid;
	logic [31:0] update0_start_full_PC;

    // Update 1
	logic [LOG_UPCT_ENTRIES-1:0] update1_upct_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

    upct WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // RESP stage
			valid_RESP <= '0;
			upct_index_RESP <= '0;
			last_upper_PC_RESP <= '0;

		    // Update 0
			update0_valid <= '0;
			update0_start_full_PC <= '0;

		    // Update 1
			last_update1_upct_index <= '0;
        end
        else begin


		    // RESP stage
			valid_RESP <= next_valid_RESP;
			upct_index_RESP <= next_upct_index_RESP;
			last_upper_PC_RESP <= upper_PC_RESP;

		    // Update 0
			update0_valid <= next_update0_valid;
			update0_start_full_PC <= next_update0_start_full_PC;

		    // Update 1
			last_update1_upct_index <= update1_upct_index;
        end
    end

endmodule