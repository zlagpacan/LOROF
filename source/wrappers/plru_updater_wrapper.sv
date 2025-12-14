/*
    Filename: plru_updater_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around plru_updater module. 
    Spec: LOROF/spec/design/plru_updater.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module plru_updater_wrapper #(
	parameter NUM_ENTRIES = 8,
	parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,
	input logic [NUM_ENTRIES-2:0] next_plru_in,

	input logic next_new_valid,
	output logic [LOG_NUM_ENTRIES-1:0] last_new_index,

	input logic next_touch_valid,
	input logic [LOG_NUM_ENTRIES-1:0] next_touch_index,

	output logic [NUM_ENTRIES-2:0] last_plru_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
	logic [NUM_ENTRIES-2:0] plru_in;

	logic new_valid;
	logic [LOG_NUM_ENTRIES-1:0] new_index;

	logic touch_valid;
	logic [LOG_NUM_ENTRIES-1:0] touch_index;

	logic [NUM_ENTRIES-2:0] plru_out;

    // ----------------------------------------------------------------
    // Module Instantiation:

	plru_updater #(
		.NUM_ENTRIES(NUM_ENTRIES),
		.LOG_NUM_ENTRIES(LOG_NUM_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
			plru_in <= '0;

			new_valid <= '0;
			last_new_index <= '0;

			touch_valid <= '0;
			touch_index <= '0;

			last_plru_out <= '0;
        end
        else begin
			plru_in <= next_plru_in;

			new_valid <= next_new_valid;
			last_new_index <= new_index;

			touch_valid <= next_touch_valid;
			touch_index <= next_touch_index;

			last_plru_out <= plru_out;
        end
    end

endmodule