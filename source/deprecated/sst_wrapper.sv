/*
    Filename: sst_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around sst module. 
    Spec: LOROF/spec/design/sst.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module sst_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // new SSID check
	input logic next_new_SSID_valid,
	output logic [SSID_WIDTH-1:0] last_new_SSID,

    // touch check
	input logic next_touch_SSID_valid,
	input logic [SSID_WIDTH-1:0] next_touch_SSID
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // new SSID check
	logic new_SSID_valid;
	logic [SSID_WIDTH-1:0] new_SSID;

    // touch check
	logic touch_SSID_valid;
	logic [SSID_WIDTH-1:0] touch_SSID;

    // ----------------------------------------------------------------
    // Module Instantiation:

    sst #(.STORE_SET_COUNT(STORE_SET_COUNT)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // new SSID check
			new_SSID_valid <= '0;
			last_new_SSID <= '0;

		    // touch check
			touch_SSID_valid <= '0;
			touch_SSID <= '0;
        end
        else begin

		    // new SSID check
			new_SSID_valid <= next_new_SSID_valid;
			last_new_SSID <= new_SSID;

		    // touch check
			touch_SSID_valid <= next_touch_SSID_valid;
			touch_SSID <= next_touch_SSID;
        end
    end

endmodule