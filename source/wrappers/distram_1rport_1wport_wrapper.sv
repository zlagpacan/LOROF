/*
    Filename: distram_1rport_1wport_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around distram_1rport_1wport module. 
    Spec: LOROF/spec/design/distram_1rport_1wport.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

parameter OUTER_WIDTH = 32;
parameter INNER_WIDTH = 32;

module distram_1rport_1wport_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

	input logic [$clog2(OUTER_WIDTH)-1:0] next_rindex,
	output logic [INNER_WIDTH-1:0] last_rdata,

	input logic next_wen,
	input logic [$clog2(OUTER_WIDTH)-1:0] next_windex,
	input logic [INNER_WIDTH-1:0] next_wdata
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic [$clog2(OUTER_WIDTH)-1:0] rindex;
	logic [INNER_WIDTH-1:0] rdata;

	logic wen;
	logic [$clog2(OUTER_WIDTH)-1:0] windex;
	logic [INNER_WIDTH-1:0] wdata;

    // ----------------------------------------------------------------
    // Module Instantiation:

    distram_1rport_1wport WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			rindex <= '0;
			last_rdata <= '0;

			wen <= '0;
			windex <= '0;
			wdata <= '0;
        end
        else begin

			rindex <= next_rindex;
			last_rdata <= rdata;

			wen <= next_wen;
			windex <= next_windex;
			wdata <= next_wdata;
        end
    end

endmodule