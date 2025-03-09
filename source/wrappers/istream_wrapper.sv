/*
    Filename: istream_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around istream module. 
    Spec: LOROF/spec/design/istream.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module istream_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // SENQ stage
	input logic next_valid_SENQ,
	input logic [7:0] next_valid_by_fetch_2B_SENQ,
	input logic [7:0][15:0] next_instr_2B_by_fetch_2B_SENQ,
	input logic [7:0][BTB_PRED_INFO_WIDTH-1:0] next_pred_info_by_fetch_2B_SENQ,
	input logic [7:0] next_pred_lru_by_fetch_2B_SENQ,
	input logic [7:0][MDPT_INFO_WIDTH-1:0] next_mdp_info_by_fetch_2B_SENQ,
	input logic [31:0] next_after_PC_SENQ,
	input logic [LH_LENGTH-1:0] next_LH_SENQ,
	input logic [GH_LENGTH-1:0] next_GH_SENQ,
	input logic [RAS_INDEX_WIDTH-1:0] next_ras_index_SENQ,

    // SENQ feedback
	output logic last_stall_SENQ,

    // SDEQ stage
	output logic last_valid_SDEQ,
	output logic [3:0] last_valid_by_way_SDEQ,
	output logic [3:0] last_uncompressed_by_way_SDEQ,
	output logic [3:0][1:0][15:0] last_instr_2B_by_way_by_chunk_SDEQ,
	output logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0] last_pred_info_by_way_by_chunk_SDEQ,
	output logic [3:0][1:0] last_pred_lru_by_way_by_chunk_SDEQ,
	output logic [3:0][MDPT_INFO_WIDTH-1:0] last_mdp_info_by_way_SDEQ,
	output logic [3:0][31:0] last_PC_by_way_SDEQ,
	output logic [3:0][LH_LENGTH-1:0] last_LH_by_way_SDEQ,
	output logic [3:0][GH_LENGTH-1:0] last_GH_by_way_SDEQ,
	output logic [3:0][RAS_INDEX_WIDTH-1:0] last_ras_index_by_way_SDEQ,

    // SDEQ feedback
	input logic next_stall_SDEQ,

    // control
	input logic next_restart,
	input logic [31:0] next_restart_PC
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // SENQ stage
	logic valid_SENQ;
	logic [7:0] valid_by_fetch_2B_SENQ;
	logic [7:0][15:0] instr_2B_by_fetch_2B_SENQ;
	logic [7:0][BTB_PRED_INFO_WIDTH-1:0] pred_info_by_fetch_2B_SENQ;
	logic [7:0] pred_lru_by_fetch_2B_SENQ;
	logic [7:0][MDPT_INFO_WIDTH-1:0] mdp_info_by_fetch_2B_SENQ;
	logic [31:0] after_PC_SENQ;
	logic [LH_LENGTH-1:0] LH_SENQ;
	logic [GH_LENGTH-1:0] GH_SENQ;
	logic [RAS_INDEX_WIDTH-1:0] ras_index_SENQ;

    // SENQ feedback
	logic stall_SENQ;

    // SDEQ stage
	logic valid_SDEQ;
	logic [3:0] valid_by_way_SDEQ;
	logic [3:0] uncompressed_by_way_SDEQ;
	logic [3:0][1:0][15:0] instr_2B_by_way_by_chunk_SDEQ;
	logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0] pred_info_by_way_by_chunk_SDEQ;
	logic [3:0][1:0] pred_lru_by_way_by_chunk_SDEQ;
	logic [3:0][MDPT_INFO_WIDTH-1:0] mdp_info_by_way_SDEQ;
	logic [3:0][31:0] PC_by_way_SDEQ;
	logic [3:0][LH_LENGTH-1:0] LH_by_way_SDEQ;
	logic [3:0][GH_LENGTH-1:0] GH_by_way_SDEQ;
	logic [3:0][RAS_INDEX_WIDTH-1:0] ras_index_by_way_SDEQ;

    // SDEQ feedback
	logic stall_SDEQ;

    // control
	logic restart;
	logic [31:0] restart_PC;

    // ----------------------------------------------------------------
    // Module Instantiation:

    istream #(
		.ISTREAM_SETS(ISTREAM_SETS),
		.INIT_PC(32'h80000000)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // SENQ stage
			valid_SENQ <= '0;
			valid_by_fetch_2B_SENQ <= '0;
			instr_2B_by_fetch_2B_SENQ <= '0;
			pred_info_by_fetch_2B_SENQ <= '0;
			pred_lru_by_fetch_2B_SENQ <= '0;
			mdp_info_by_fetch_2B_SENQ <= '0;
			after_PC_SENQ <= '0;
			LH_SENQ <= '0;
			GH_SENQ <= '0;
			ras_index_SENQ <= '0;

		    // SENQ feedback
			last_stall_SENQ <= '0;

		    // SDEQ stage
			last_valid_SDEQ <= '0;
			last_valid_by_way_SDEQ <= '0;
			last_uncompressed_by_way_SDEQ <= '0;
			last_instr_2B_by_way_by_chunk_SDEQ <= '0;
			last_pred_info_by_way_by_chunk_SDEQ <= '0;
			last_pred_lru_by_way_by_chunk_SDEQ <= '0;
			last_mdp_info_by_way_SDEQ <= '0;
			last_PC_by_way_SDEQ <= '0;
			last_LH_by_way_SDEQ <= '0;
			last_GH_by_way_SDEQ <= '0;
			last_ras_index_by_way_SDEQ <= '0;

		    // SDEQ feedback
			stall_SDEQ <= '0;

		    // control
			restart <= '0;
			restart_PC <= '0;
        end
        else begin


		    // SENQ stage
			valid_SENQ <= next_valid_SENQ;
			valid_by_fetch_2B_SENQ <= next_valid_by_fetch_2B_SENQ;
			instr_2B_by_fetch_2B_SENQ <= next_instr_2B_by_fetch_2B_SENQ;
			pred_info_by_fetch_2B_SENQ <= next_pred_info_by_fetch_2B_SENQ;
			pred_lru_by_fetch_2B_SENQ <= next_pred_lru_by_fetch_2B_SENQ;
			mdp_info_by_fetch_2B_SENQ <= next_mdp_info_by_fetch_2B_SENQ;
			after_PC_SENQ <= next_after_PC_SENQ;
			LH_SENQ <= next_LH_SENQ;
			GH_SENQ <= next_GH_SENQ;
			ras_index_SENQ <= next_ras_index_SENQ;

		    // SENQ feedback
			last_stall_SENQ <= stall_SENQ;

		    // SDEQ stage
			last_valid_SDEQ <= valid_SDEQ;
			last_valid_by_way_SDEQ <= valid_by_way_SDEQ;
			last_uncompressed_by_way_SDEQ <= uncompressed_by_way_SDEQ;
			last_instr_2B_by_way_by_chunk_SDEQ <= instr_2B_by_way_by_chunk_SDEQ;
			last_pred_info_by_way_by_chunk_SDEQ <= pred_info_by_way_by_chunk_SDEQ;
			last_pred_lru_by_way_by_chunk_SDEQ <= pred_lru_by_way_by_chunk_SDEQ;
			last_mdp_info_by_way_SDEQ <= mdp_info_by_way_SDEQ;
			last_PC_by_way_SDEQ <= PC_by_way_SDEQ;
			last_LH_by_way_SDEQ <= LH_by_way_SDEQ;
			last_GH_by_way_SDEQ <= GH_by_way_SDEQ;
			last_ras_index_by_way_SDEQ <= ras_index_by_way_SDEQ;

		    // SDEQ feedback
			stall_SDEQ <= next_stall_SDEQ;

		    // control
			restart <= next_restart;
			restart_PC <= next_restart_PC;
        end
    end

endmodule