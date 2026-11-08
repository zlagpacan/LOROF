/*
    Filename: lht_index_hash_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around lht_index_hash module. 
    Spec: LOROF/spec/design/lht_index_hash.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lht_index_hash_wrapper (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [31:0] next_PC,
	input logic [ASID_WIDTH-1:0] next_ASID,
	output logic [LHT_INDEX_WIDTH-1:0] last_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [31:0] PC;
	logic [ASID_WIDTH-1:0] ASID;
	logic [LHT_INDEX_WIDTH-1:0] index;

    // ----------------------------------------------------------------
    // Module Instantiation:

    lht_index_hash WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			PC <= '0;
			ASID <= '0;
			last_index <= '0;
        end
        else begin
			PC <= next_PC;
			ASID <= next_ASID;
			last_index <= index;
        end
    end

endmodule