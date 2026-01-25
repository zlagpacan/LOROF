/*
    Filename: bram_2rport_1wport_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bram_2rport_1wport module. 
    Spec: LOROF/spec/design/bram_2rport_1wport.md
*/

`timescale 1ns/100ps


module bram_2rport_1wport_wrapper #(
	parameter INNER_WIDTH = 32,
	parameter OUTER_WIDTH = 32,
	parameter INIT_FILE = ""
) (

    // seq
    input logic CLK,
    input logic nRST,

	input logic next_port0_ren,
	input logic [$clog2(OUTER_WIDTH)-1:0] next_port0_rindex,
	output logic [INNER_WIDTH-1:0] last_port0_rdata,

	input logic next_port1_ren,
	input logic [$clog2(OUTER_WIDTH)-1:0] next_port1_rindex,
	output logic [INNER_WIDTH-1:0] last_port1_rdata,

	input logic [INNER_WIDTH/8-1:0] next_wen_byte,
	input logic [$clog2(OUTER_WIDTH)-1:0] next_windex,
	input logic [INNER_WIDTH-1:0] next_wdata
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

	logic port0_ren;
	logic [$clog2(OUTER_WIDTH)-1:0] port0_rindex;
	logic [INNER_WIDTH-1:0] port0_rdata;

	logic port1_ren;
	logic [$clog2(OUTER_WIDTH)-1:0] port1_rindex;
	logic [INNER_WIDTH-1:0] port1_rdata;

	logic [INNER_WIDTH/8-1:0] wen_byte;
	logic [$clog2(OUTER_WIDTH)-1:0] windex;
	logic [INNER_WIDTH-1:0] wdata;

    // ----------------------------------------------------------------
    // Module Instantiation:

	bram_2rport_1wport #(
		.INNER_WIDTH(INNER_WIDTH),
		.OUTER_WIDTH(OUTER_WIDTH),
		.INIT_FILE(INIT_FILE)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

			port0_ren <= '0;
			port0_rindex <= '0;
			last_port0_rdata <= '0;

			port1_ren <= '0;
			port1_rindex <= '0;
			last_port1_rdata <= '0;

			wen_byte <= '0;
			windex <= '0;
			wdata <= '0;
        end
        else begin

			port0_ren <= next_port0_ren;
			port0_rindex <= next_port0_rindex;
			last_port0_rdata <= port0_rdata;

			port1_ren <= next_port1_ren;
			port1_rindex <= next_port1_rindex;
			last_port1_rdata <= port1_rdata;

			wen_byte <= next_wen_byte;
			windex <= next_windex;
			wdata <= next_wdata;
        end
    end

endmodule