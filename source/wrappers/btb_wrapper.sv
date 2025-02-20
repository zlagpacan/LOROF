/*
    Filename: btb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around btb module. 
    Spec: LOROF/spec/design/btb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // REQ stage
	input logic next_valid_REQ,
	input logic [31:0] next_full_PC_REQ,
	input logic [ASID_WIDTH-1:0] next_ASID_REQ,

    // RESP stage
	output logic [15:0] last_hit_by_instr_RESP,
	output logic [15:0][BTB_PRED_INFO_WIDTH-1:0] last_pred_info_by_instr_RESP,
	output logic [15:0] last_pred_lru_by_instr_RESP,
	output logic [15:0][BTB_TARGET_WIDTH-1:0] last_target_by_instr_RESP,

    // Update 0
	input logic next_update0_valid,
	input logic [31:0] next_update0_start_full_PC,

    // Update 1
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_update1_pred_info,
	input logic next_update1_pred_lru,
	input logic [31:0] next_update1_target_full_PC
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // REQ stage
	logic valid_REQ;
	logic [31:0] full_PC_REQ;
	logic [ASID_WIDTH-1:0] ASID_REQ;

    // RESP stage
	logic [15:0] hit_by_instr_RESP;
	logic [15:0][BTB_PRED_INFO_WIDTH-1:0] pred_info_by_instr_RESP;
	logic [15:0] pred_lru_by_instr_RESP;
	logic [15:0][BTB_TARGET_WIDTH-1:0] target_by_instr_RESP;

    // Update 0
	logic update0_valid;
	logic [31:0] update0_start_full_PC;

    // Update 1
	logic [BTB_PRED_INFO_WIDTH-1:0] update1_pred_info;
	logic update1_pred_lru;
	logic [31:0] update1_target_full_PC;

    // ----------------------------------------------------------------
    // Module Instantiation:

    btb WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // REQ stage
			valid_REQ <= '0;
			full_PC_REQ <= '0;
			ASID_REQ <= '0;

		    // RESP stage
			last_hit_by_instr_RESP <= '0;
			last_pred_info_by_instr_RESP <= '0;
			last_pred_lru_by_instr_RESP <= '0;
			last_target_by_instr_RESP <= '0;

		    // Update 0
			update0_valid <= '0;
			update0_start_full_PC <= '0;

		    // Update 1
			update1_pred_info <= '0;
			update1_pred_lru <= '0;
			update1_target_full_PC <= '0;
        end
        else begin


		    // REQ stage
			valid_REQ <= next_valid_REQ;
			full_PC_REQ <= next_full_PC_REQ;
			ASID_REQ <= next_ASID_REQ;

		    // RESP stage
			last_hit_by_instr_RESP <= hit_by_instr_RESP;
			last_pred_info_by_instr_RESP <= pred_info_by_instr_RESP;
			last_pred_lru_by_instr_RESP <= pred_lru_by_instr_RESP;
			last_target_by_instr_RESP <= target_by_instr_RESP;

		    // Update 0
			update0_valid <= next_update0_valid;
			update0_start_full_PC <= next_update0_start_full_PC;

		    // Update 1
			update1_pred_info <= next_update1_pred_info;
			update1_pred_lru <= next_update1_pred_lru;
			update1_target_full_PC <= next_update1_target_full_PC;
        end
    end

endmodule