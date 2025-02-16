/*
    Filename: bru_pred_info_updater_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bru_pred_info_updater module. 
    Spec: LOROF/spec/design/bru_pred_info_updater.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pred_info_updater_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // inputs
	input logic [3:0] next_op,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_start_pred_info,
	input logic next_is_link_ra,
	input logic next_is_ret_ra,
	input logic next_is_taken,
	input logic next_is_mispredict,
	input logic next_is_out_of_range,

    // outputs
	output logic [BTB_PRED_INFO_WIDTH-1:0] last_updated_pred_info
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // inputs
	logic [3:0] op;
	logic [BTB_PRED_INFO_WIDTH-1:0] start_pred_info;
	logic is_link_ra;
	logic is_ret_ra;
	logic is_taken;
	logic is_mispredict;
	logic is_out_of_range;

    // outputs
	logic [BTB_PRED_INFO_WIDTH-1:0] updated_pred_info;

    // ----------------------------------------------------------------
    // Module Instantiation:

    bru_pred_info_updater WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // inputs
			op <= '0;
			start_pred_info <= '0;
			is_link_ra <= '0;
			is_ret_ra <= '0;
			is_taken <= '0;
			is_mispredict <= '0;
			is_out_of_range <= '0;

		    // outputs
			last_updated_pred_info <= '0;
        end
        else begin

		    // inputs
			op <= next_op;
			start_pred_info <= next_start_pred_info;
			is_link_ra <= next_is_link_ra;
			is_ret_ra <= next_is_ret_ra;
			is_taken <= next_is_taken;
			is_mispredict <= next_is_mispredict;
			is_out_of_range <= next_is_out_of_range;

		    // outputs
			last_updated_pred_info <= updated_pred_info;
        end
    end

endmodule