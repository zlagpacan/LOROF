/*
    Filename: lht_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around lht module. 
    Spec: LOROF/spec/design/lht.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lht_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // REQ stage
	input logic next_valid_REQ,
	input logic [31:0] next_full_PC_REQ,
	input logic [ASID_WIDTH-1:0] next_ASID_REQ,

    // RESP stage
	output logic [LHT_ENTRIES_PER_BLOCK-1:0][LH_LENGTH-1:0] last_lh_by_instr_RESP,

    // Update
	input logic next_update_valid,
	input logic [31:0] next_update_start_full_PC,
	input logic [LH_LENGTH-1:0] next_update_lh
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // REQ stage
	logic valid_REQ;
	logic [31:0] full_PC_REQ;
	logic [ASID_WIDTH-1:0] ASID_REQ;

    // RESP stage
	logic [LHT_ENTRIES_PER_BLOCK-1:0][LH_LENGTH-1:0] lh_by_instr_RESP;

    // Update
	logic update_valid;
	logic [31:0] update_start_full_PC;
	logic [LH_LENGTH-1:0] update_lh;

    // ----------------------------------------------------------------
    // Module Instantiation:

    lht WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // REQ stage
			valid_REQ <= '0;
			full_PC_REQ <= '0;
			ASID_REQ <= '0;

		    // RESP stage
			last_lh_by_instr_RESP <= '0;

		    // Update
			update_valid <= '0;
			update_start_full_PC <= '0;
			update_lh <= '0;
        end
        else begin


		    // REQ stage
			valid_REQ <= next_valid_REQ;
			full_PC_REQ <= next_full_PC_REQ;
			ASID_REQ <= next_ASID_REQ;

		    // RESP stage
			last_lh_by_instr_RESP <= lh_by_instr_RESP;

		    // Update
			update_valid <= next_update_valid;
			update_start_full_PC <= next_update_start_full_PC;
			update_lh <= next_update_lh;
        end
    end

endmodule