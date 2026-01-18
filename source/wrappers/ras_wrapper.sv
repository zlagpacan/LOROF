/*
    Filename: ras_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ras module. 
    Spec: LOROF/spec/design/ras.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module ras_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // pc_gen link control
	input logic next_link_valid,
	input corep::PC38_t next_link_pc38,

    // pc_gen return control
	input logic next_ret_valid,
	output corep::PC38_t last_ret_pc38,
	output corep::RAS_idx_t last_ret_ras_index,

    // update control
	input logic next_update_valid,
	input corep::RAS_idx_t next_update_ras_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // pc_gen link control
	logic link_valid;
	corep::PC38_t link_pc38;

    // pc_gen return control
	logic ret_valid;
	corep::PC38_t ret_pc38;
	corep::RAS_idx_t ret_ras_index;

    // update control
	logic update_valid;
	corep::RAS_idx_t update_ras_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ras #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // pc_gen link control
			link_valid <= '0;
			link_pc38 <= '0;

		    // pc_gen return control
			ret_valid <= '0;
			last_ret_pc38 <= '0;
			last_ret_ras_index <= '0;

		    // update control
			update_valid <= '0;
			update_ras_index <= '0;
        end
        else begin


		    // pc_gen link control
			link_valid <= next_link_valid;
			link_pc38 <= next_link_pc38;

		    // pc_gen return control
			ret_valid <= next_ret_valid;
			last_ret_pc38 <= ret_pc38;
			last_ret_ras_index <= ret_ras_index;

		    // update control
			update_valid <= next_update_valid;
			update_ras_index <= next_update_ras_index;
        end
    end

endmodule