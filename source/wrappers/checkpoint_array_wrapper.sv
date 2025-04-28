/*
    Filename: checkpoint_array_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around checkpoint_array module. 
    Spec: LOROF/spec/design/checkpoint_array.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module checkpoint_array_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // checkpoint save
	input logic next_save_valid,
	input logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] next_save_map_table,
	input logic [LH_LENGTH-1:0] next_save_LH,
	input logic [GH_LENGTH-1:0] next_save_GH,
	input logic [RAS_INDEX_WIDTH-1:0] next_save_ras_index,

	output logic last_save_ready,
	output logic [CHECKPOINT_INDEX_WIDTH-1:0] last_save_index,

    // checkpoint restore
	input logic [CHECKPOINT_INDEX_WIDTH-1:0] next_restore_index,
	input logic next_restore_clear,

	output logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] last_restore_map_table,
	output logic [LH_LENGTH-1:0] last_restore_LH,
	output logic [GH_LENGTH-1:0] last_restore_GH,
	output logic [RAS_INDEX_WIDTH-1:0] last_restore_ras_index,

    // advertized threshold
	output logic last_above_threshold
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // checkpoint save
	logic save_valid;
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] save_map_table;
	logic [LH_LENGTH-1:0] save_LH;
	logic [GH_LENGTH-1:0] save_GH;
	logic [RAS_INDEX_WIDTH-1:0] save_ras_index;

	logic save_ready;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] save_index;

    // checkpoint restore
	logic [CHECKPOINT_INDEX_WIDTH-1:0] restore_index;
	logic restore_clear;

	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] restore_map_table;
	logic [LH_LENGTH-1:0] restore_LH;
	logic [GH_LENGTH-1:0] restore_GH;
	logic [RAS_INDEX_WIDTH-1:0] restore_ras_index;

    // advertized threshold
	logic above_threshold;

    // ----------------------------------------------------------------
    // Module Instantiation:

    checkpoint_array #(
		.CHECKPOINT_COUNT(CHECKPOINT_COUNT),
		.CHECKPOINT_INDEX_WIDTH(CHECKPOINT_INDEX_WIDTH),
		.CHECKPOINT_THRESHOLD(CHECKPOINT_THRESHOLD)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // checkpoint save
			save_valid <= '0;
			save_map_table <= '0;
			save_LH <= '0;
			save_GH <= '0;
			save_ras_index <= '0;

			last_save_ready <= '0;
			last_save_index <= '0;

		    // checkpoint restore
			restore_index <= '0;
			restore_clear <= '0;

			last_restore_map_table <= '0;
			last_restore_LH <= '0;
			last_restore_GH <= '0;
			last_restore_ras_index <= '0;

		    // advertized threshold
			last_above_threshold <= '0;
        end
        else begin

		    // checkpoint save
			save_valid <= next_save_valid;
			save_map_table <= next_save_map_table;
			save_LH <= next_save_LH;
			save_GH <= next_save_GH;
			save_ras_index <= next_save_ras_index;

			last_save_ready <= save_ready;
			last_save_index <= save_index;

		    // checkpoint restore
			restore_index <= next_restore_index;
			restore_clear <= next_restore_clear;

			last_restore_map_table <= restore_map_table;
			last_restore_LH <= restore_LH;
			last_restore_GH <= restore_GH;
			last_restore_ras_index <= restore_ras_index;

		    // advertized threshold
			last_above_threshold <= above_threshold;
        end
    end

endmodule