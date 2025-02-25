/*
    Filename: gbpt_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around gbpt module. 
    Spec: LOROF/spec/design/gbpt.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module gbpt_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // RESP stage
	input logic next_valid_RESP,
	input logic [31:0] next_full_PC_RESP,
	input logic [GH_LENGTH-1:0] next_GH_RESP,
	input logic [ASID_WIDTH-1:0] next_ASID_RESP,

    // RESTART stage
	output logic last_pred_taken_RESTART,

    // Update 0
	input logic next_update0_valid,
	input logic [31:0] next_update0_start_full_PC,
	input logic [GH_LENGTH-1:0] next_update0_GH,
	input logic [ASID_WIDTH-1:0] next_update0_ASID,
	input logic next_update0_taken,

    // Update 1
	output logic last_update1_correct
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // RESP stage
	logic valid_RESP;
	logic [31:0] full_PC_RESP;
	logic [GH_LENGTH-1:0] GH_RESP;
	logic [ASID_WIDTH-1:0] ASID_RESP;

    // RESTART stage
	logic pred_taken_RESTART;

    // Update 0
	logic update0_valid;
	logic [31:0] update0_start_full_PC;
	logic [GH_LENGTH-1:0] update0_GH;
	logic [ASID_WIDTH-1:0] update0_ASID;
	logic update0_taken;

    // Update 1
	logic update1_correct;

    // ----------------------------------------------------------------
    // Module Instantiation:

    gbpt WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // RESP stage
			valid_RESP <= '0;
			full_PC_RESP <= '0;
			GH_RESP <= '0;
			ASID_RESP <= '0;

		    // RESTART stage
			last_pred_taken_RESTART <= '0;

		    // Update 0
			update0_valid <= '0;
			update0_start_full_PC <= '0;
			update0_GH <= '0;
			update0_ASID <= '0;
			update0_taken <= '0;

		    // Update 1
			last_update1_correct <= '0;
        end
        else begin


		    // RESP stage
			valid_RESP <= next_valid_RESP;
			full_PC_RESP <= next_full_PC_RESP;
			GH_RESP <= next_GH_RESP;
			ASID_RESP <= next_ASID_RESP;

		    // RESTART stage
			last_pred_taken_RESTART <= pred_taken_RESTART;

		    // Update 0
			update0_valid <= next_update0_valid;
			update0_start_full_PC <= next_update0_start_full_PC;
			update0_GH <= next_update0_GH;
			update0_ASID <= next_update0_ASID;
			update0_taken <= next_update0_taken;

		    // Update 1
			last_update1_correct <= update1_correct;
        end
    end

endmodule