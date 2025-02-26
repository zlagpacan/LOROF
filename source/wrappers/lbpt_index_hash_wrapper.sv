/*
    Filename: lbpt_index_hash_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around lbpt_index_hash module. 
    Spec: LOROF/spec/design/lbpt_index_hash.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lbpt_index_hash_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [31:0] next_PC,
	input logic [LH_LENGTH-1:0] next_LH,
	input logic [ASID_WIDTH-1:0] next_ASID,
	output logic [LBPT_INDEX_WIDTH+LOG_LBPT_ENTRIES_PER_BLOCK-1:0] last_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [31:0] PC;
	logic [LH_LENGTH-1:0] LH;
	logic [ASID_WIDTH-1:0] ASID;
	logic [LBPT_INDEX_WIDTH+LOG_LBPT_ENTRIES_PER_BLOCK-1:0] index;

    // ----------------------------------------------------------------
    // Module Instantiation:

    lbpt_index_hash WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			PC <= '0;
			LH <= '0;
			ASID <= '0;
			last_index <= '0;
        end
        else begin
			PC <= next_PC;
			LH <= next_LH;
			ASID <= next_ASID;
			last_index <= index;
        end
    end

endmodule