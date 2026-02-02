/*
    Filename: id_tracker_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around id_tracker module. 
    Spec: LOROF/spec/design/id_tracker.md
*/

`timescale 1ns/100ps


module id_tracker_wrapper #(
	parameter int unsigned ID_COUNT = 4,
	parameter int unsigned ID_WIDTH = $clog2(ID_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // new id dispatch
	input logic next_new_id_consume,
	output logic last_new_id_ready,
	output logic [ID_WIDTH-1:0] last_new_id,

    // old id retirement
	input logic next_old_id_done,
	input logic [ID_WIDTH-1:0] next_old_id
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // new id dispatch
	logic new_id_consume;
	logic new_id_ready;
	logic [ID_WIDTH-1:0] new_id;

    // old id retirement
	logic old_id_done;
	logic [ID_WIDTH-1:0] old_id;

    // ----------------------------------------------------------------
    // Module Instantiation:

	id_tracker #(
		.ID_COUNT(ID_COUNT),
		.ID_WIDTH(ID_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // new id dispatch
			new_id_consume <= '0;
			last_new_id_ready <= '0;
			last_new_id <= '0;

		    // old id retirement
			old_id_done <= '0;
			old_id <= '0;
        end
        else begin

		    // new id dispatch
			new_id_consume <= next_new_id_consume;
			last_new_id_ready <= new_id_ready;
			last_new_id <= new_id;

		    // old id retirement
			old_id_done <= next_old_id_done;
			old_id <= next_old_id;
        end
    end

endmodule