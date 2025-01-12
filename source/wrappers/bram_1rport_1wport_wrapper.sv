/*
    Filename: bram_1rport_1wport_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bram_1rport_1wport module. 
    Spec: LOROF/spec/design/bram_1rport_1wport.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

parameter OUTER_WIDTH = 32;
parameter INNER_WIDTH = 32;

module bram_1rport_1wport_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

	input logic next_ren,
	input logic [$clog2(OUTER_WIDTH)-1:0] next_rindex,
	output logic [INNER_WIDTH-1:0] last_rdata,

	input logic [INNER_WIDTH/8-1:0] next_wen_byte,
	input logic [$clog2(OUTER_WIDTH)-1:0] next_windex,
	input logic [INNER_WIDTH-1:0] next_wdata
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic ren;
	logic [$clog2(OUTER_WIDTH)-1:0] rindex;
	logic [INNER_WIDTH-1:0] rdata;

	logic [INNER_WIDTH/8-1:0] wen_byte;
	logic [$clog2(OUTER_WIDTH)-1:0] windex;
	logic [INNER_WIDTH-1:0] wdata;

    // ----------------------------------------------------------------
    // Module Instantiation:

    bram_1rport_1wport #(
		.OUTER_WIDTH(OUTER_WIDTH), 
		.INNER_WIDTH(INNER_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			ren <= '0;
			rindex <= '0;
			last_rdata <= '0;

			wen_byte <= '0;
			windex <= '0;
			wdata <= '0;
        end
        else begin

			ren <= next_ren;
			rindex <= next_rindex;
			last_rdata <= rdata;

			wen_byte <= next_wen_byte;
			windex <= next_windex;
			wdata <= next_wdata;
        end
    end

endmodule