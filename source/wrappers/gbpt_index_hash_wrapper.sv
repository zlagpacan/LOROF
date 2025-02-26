/*
    Filename: gbpt_index_hash_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around gbpt_index_hash module. 
    Spec: LOROF/spec/design/gbpt_index_hash.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module gbpt_index_hash_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [31:0] next_PC,
	input logic [GH_LENGTH-1:0] next_GH,
	input logic [ASID_WIDTH-1:0] next_ASID,
	output logic [GBPT_INDEX_WIDTH+LOG_GBPT_ENTRIES_PER_BLOCK-1:0] last_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [31:0] PC;
	logic [GH_LENGTH-1:0] GH;
	logic [ASID_WIDTH-1:0] ASID;
	logic [GBPT_INDEX_WIDTH+LOG_GBPT_ENTRIES_PER_BLOCK-1:0] index;

    // ----------------------------------------------------------------
    // Module Instantiation:

    gbpt_index_hash WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			PC <= '0;
			GH <= '0;
			ASID <= '0;
			last_index <= '0;
        end
        else begin
			PC <= next_PC;
			GH <= next_GH;
			ASID <= next_ASID;
			last_index <= index;
        end
    end

endmodule