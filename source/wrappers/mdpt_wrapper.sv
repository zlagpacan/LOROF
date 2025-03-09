/*
    Filename: mdpt_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mdpt module. 
    Spec: LOROF/spec/design/mdpt.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module mdpt_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // REQ stage
	input logic next_valid_REQ,
	input logic [31:0] next_full_PC_REQ,
	input logic [ASID_WIDTH-1:0] next_ASID_REQ,

    // RESP stage
	output logic [MDPT_ENTRIES_PER_BLOCK-1:0][MDPT_INFO_WIDTH-1:0] last_mdp_info_by_instr_RESP,

    // Dep Update 0 stage
	input logic next_dep_update0_valid,
	input logic [31:0] next_dep_update0_start_full_PC,
	input logic [ASID_WIDTH-1:0] next_dep_update0_ASID,
	input logic [MDPT_INFO_WIDTH-1:0] next_dep_update0_mdp_info
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // REQ stage
	logic valid_REQ;
	logic [31:0] full_PC_REQ;
	logic [ASID_WIDTH-1:0] ASID_REQ;

    // RESP stage
	logic [MDPT_ENTRIES_PER_BLOCK-1:0][MDPT_INFO_WIDTH-1:0] mdp_info_by_instr_RESP;

    // Dep Update 0 stage
	logic dep_update0_valid;
	logic [31:0] dep_update0_start_full_PC;
	logic [ASID_WIDTH-1:0] dep_update0_ASID;
	logic [MDPT_INFO_WIDTH-1:0] dep_update0_mdp_info;

    // ----------------------------------------------------------------
    // Module Instantiation:

    mdpt WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // REQ stage
			valid_REQ <= '0;
			full_PC_REQ <= '0;
			ASID_REQ <= '0;

		    // RESP stage
			last_mdp_info_by_instr_RESP <= '0;

		    // Dep Update 0 stage
			dep_update0_valid <= '0;
			dep_update0_start_full_PC <= '0;
			dep_update0_ASID <= '0;
			dep_update0_mdp_info <= '0;
        end
        else begin


		    // REQ stage
			valid_REQ <= next_valid_REQ;
			full_PC_REQ <= next_full_PC_REQ;
			ASID_REQ <= next_ASID_REQ;

		    // RESP stage
			last_mdp_info_by_instr_RESP <= mdp_info_by_instr_RESP;

		    // Dep Update 0 stage
			dep_update0_valid <= next_dep_update0_valid;
			dep_update0_start_full_PC <= next_dep_update0_start_full_PC;
			dep_update0_ASID <= next_dep_update0_ASID;
			dep_update0_mdp_info <= next_dep_update0_mdp_info;
        end
    end

endmodule