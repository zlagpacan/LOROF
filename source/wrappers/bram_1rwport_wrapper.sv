/*
    Filename: bram_1rwport_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bram_1rwport module. 
    Spec: LOROF/spec/design/bram_1rwport.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

parameter OUTER_WIDTH = 32;
parameter INNER_WIDTH = 32;

module bram_1rwport_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

	input logic next_ren,
	input logic [INNER_WIDTH/8-1:0] next_wen_byte,
	input logic [$clog2(OUTER_WIDTH)-1:0] next_rwindex,
	output logic [INNER_WIDTH-1:0] last_rdata,
	input logic [INNER_WIDTH-1:0] next_wdata
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic ren;
	logic [INNER_WIDTH/8-1:0] wen_byte;
	logic [$clog2(OUTER_WIDTH)-1:0] rwindex;
	logic [INNER_WIDTH-1:0] rdata;
	logic [INNER_WIDTH-1:0] wdata;

    // ----------------------------------------------------------------
    // Module Instantiation:

    bram_1rwport WRAPPED_MODULE (
		.OUTER_WIDTH(OUTER_WIDTH), 
		.INNER_WIDTH(INNER_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			ren <= '0;
			wen_byte <= '0;
			rwindex <= '0;
			last_rdata <= '0;
			wdata <= '0;
        end
        else begin

			ren <= next_ren;
			wen_byte <= next_wen_byte;
			rwindex <= next_rwindex;
			last_rdata <= rdata;
			wdata <= next_wdata;
        end
    end

endmodule