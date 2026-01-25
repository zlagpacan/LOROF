/*
    Filename: id_tracker_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around id_tracker module. 
    Spec: LOROF/spec/design/id_tracker.md
*/

`timescale 1ns/100ps


module id_tracker_wrapper #(
	parameter int unsigned TAG_COUNT = 4,
	parameter int unsigned TAG_WIDTH = $clog2(TAG_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // new tag dispatch
	input logic next_new_tag_consume,
	output logic last_new_tag_ready,
	output logic [TAG_WIDTH-1:0] last_new_tag,

    // old tag retirement
	input logic next_old_tag_done,
	input logic [TAG_WIDTH-1:0] next_old_tag
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // new tag dispatch
	logic new_tag_consume;
	logic new_tag_ready;
	logic [TAG_WIDTH-1:0] new_tag;

    // old tag retirement
	logic old_tag_done;
	logic [TAG_WIDTH-1:0] old_tag;

    // ----------------------------------------------------------------
    // Module Instantiation:

	id_tracker #(
		.TAG_COUNT(TAG_COUNT),
		.TAG_WIDTH(TAG_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // new tag dispatch
			new_tag_consume <= '0;
			last_new_tag_ready <= '0;
			last_new_tag <= '0;

		    // old tag retirement
			old_tag_done <= '0;
			old_tag <= '0;
        end
        else begin

		    // new tag dispatch
			new_tag_consume <= next_new_tag_consume;
			last_new_tag_ready <= new_tag_ready;
			last_new_tag <= new_tag;

		    // old tag retirement
			old_tag_done <= next_old_tag_done;
			old_tag <= next_old_tag;
        end
    end

endmodule