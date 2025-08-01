/*
    Filename: ssu_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ssu module. 
    Spec: LOROF/spec/design/ssu.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter STORE_SET_COUNT = 64;
parameter SSID_WIDTH = $clog2(STORE_SET_COUNT);
parameter SSU_INPUT_BUFFER_ENTRIES = core_types_pkg::SSU_INNER_BUFFER_ENTRIES;
parameter SSU_FUNNEL_BUFFER_ENTRIES = core_types_pkg::SSU_FUNNEL_BUFFER_ENTRIES;

module ssu_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // ldu_cq CAM update
        // implied dep
	input logic next_ldu_cq_CAM_update_valid,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_cq_CAM_update_ld_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_cq_CAM_update_ld_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_cq_CAM_update_stamo_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_cq_CAM_update_stamo_ROB_index,

    // ldu_mq CAM update
        // implied dep
	input logic next_ldu_mq_CAM_update_valid,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_mq_CAM_update_ld_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_mq_CAM_update_ld_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_mq_CAM_update_stamo_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_mq_CAM_update_stamo_ROB_index,

    // ldu_cq commit update
        // implied no dep
        // incorporates ldu_mq commit update
	input logic next_ldu_cq_commit_update_valid,
	input logic [MDPT_INFO_WIDTH-1:0] next_ldu_cq_commit_update_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_ldu_cq_commit_update_ROB_index,

    // stamofu_cq CAM update bank 0
        // implied dep
        // incorporates stamofu_mq CAM update
	input logic next_stamofu_cq_CAM_bank0_update_valid,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_cq_CAM_bank0_update_ld_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_cq_CAM_bank0_update_ld_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_cq_CAM_bank0_update_stamo_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_cq_CAM_bank0_update_stamo_ROB_index,

    // stamofu_cq CAM update bank 1
        // implied dep
        // incorporates stamofu_mq CAM update
	input logic next_stamofu_cq_CAM_bank1_update_valid,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_cq_CAM_bank1_update_ld_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_cq_CAM_bank1_update_ld_ROB_index,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_cq_CAM_bank1_update_stamo_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_cq_CAM_bank1_update_stamo_ROB_index,

    // stamofu_cq commit update
        // implied no dep
        // incorporates stamofu_mq commit update
	input logic next_stamofu_cq_commit_update_valid,
	input logic [MDPT_INFO_WIDTH-1:0] next_stamofu_cq_commit_update_mdp_info,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_cq_commit_update_ROB_index,

    // mdp update to rob
	output logic last_rob_mdp_update_valid,
	output logic [MDPT_INFO_WIDTH-1:0] last_rob_mdp_update_mdp_info,
	output logic [LOG_ROB_ENTRIES-1:0] last_rob_mdp_update_ROB_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // ldu_cq CAM update
        // implied dep
	logic ldu_cq_CAM_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_CAM_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_CAM_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_CAM_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_CAM_update_stamo_ROB_index;

    // ldu_mq CAM update
        // implied dep
	logic ldu_mq_CAM_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] ldu_mq_CAM_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ldu_mq_CAM_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] ldu_mq_CAM_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ldu_mq_CAM_update_stamo_ROB_index;

    // ldu_cq commit update
        // implied no dep
        // incorporates ldu_mq commit update
	logic ldu_cq_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] ldu_cq_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] ldu_cq_commit_update_ROB_index;

    // stamofu_cq CAM update bank 0
        // implied dep
        // incorporates stamofu_mq CAM update
	logic stamofu_cq_CAM_bank0_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_CAM_bank0_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_CAM_bank0_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_CAM_bank0_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_CAM_bank0_update_stamo_ROB_index;

    // stamofu_cq CAM update bank 1
        // implied dep
        // incorporates stamofu_mq CAM update
	logic stamofu_cq_CAM_bank1_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_CAM_bank1_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_CAM_bank1_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_CAM_bank1_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_CAM_bank1_update_stamo_ROB_index;

    // stamofu_cq commit update
        // implied no dep
        // incorporates stamofu_mq commit update
	logic stamofu_cq_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] stamofu_cq_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_cq_commit_update_ROB_index;

    // mdp update to rob
	logic rob_mdp_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] rob_mdp_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] rob_mdp_update_ROB_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ssu #(
		.STORE_SET_COUNT(STORE_SET_COUNT),
		.SSID_WIDTH(SSID_WIDTH),
		.SSU_INPUT_BUFFER_ENTRIES(SSU_INPUT_BUFFER_ENTRIES),
		.SSU_FUNNEL_BUFFER_ENTRIES(SSU_FUNNEL_BUFFER_ENTRIES)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // ldu_cq CAM update
		        // implied dep
			ldu_cq_CAM_update_valid <= '0;
			ldu_cq_CAM_update_ld_mdp_info <= '0;
			ldu_cq_CAM_update_ld_ROB_index <= '0;
			ldu_cq_CAM_update_stamo_mdp_info <= '0;
			ldu_cq_CAM_update_stamo_ROB_index <= '0;

		    // ldu_mq CAM update
		        // implied dep
			ldu_mq_CAM_update_valid <= '0;
			ldu_mq_CAM_update_ld_mdp_info <= '0;
			ldu_mq_CAM_update_ld_ROB_index <= '0;
			ldu_mq_CAM_update_stamo_mdp_info <= '0;
			ldu_mq_CAM_update_stamo_ROB_index <= '0;

		    // ldu_cq commit update
		        // implied no dep
		        // incorporates ldu_mq commit update
			ldu_cq_commit_update_valid <= '0;
			ldu_cq_commit_update_mdp_info <= '0;
			ldu_cq_commit_update_ROB_index <= '0;

		    // stamofu_cq CAM update bank 0
		        // implied dep
		        // incorporates stamofu_mq CAM update
			stamofu_cq_CAM_bank0_update_valid <= '0;
			stamofu_cq_CAM_bank0_update_ld_mdp_info <= '0;
			stamofu_cq_CAM_bank0_update_ld_ROB_index <= '0;
			stamofu_cq_CAM_bank0_update_stamo_mdp_info <= '0;
			stamofu_cq_CAM_bank0_update_stamo_ROB_index <= '0;

		    // stamofu_cq CAM update bank 1
		        // implied dep
		        // incorporates stamofu_mq CAM update
			stamofu_cq_CAM_bank1_update_valid <= '0;
			stamofu_cq_CAM_bank1_update_ld_mdp_info <= '0;
			stamofu_cq_CAM_bank1_update_ld_ROB_index <= '0;
			stamofu_cq_CAM_bank1_update_stamo_mdp_info <= '0;
			stamofu_cq_CAM_bank1_update_stamo_ROB_index <= '0;

		    // stamofu_cq commit update
		        // implied no dep
		        // incorporates stamofu_mq commit update
			stamofu_cq_commit_update_valid <= '0;
			stamofu_cq_commit_update_mdp_info <= '0;
			stamofu_cq_commit_update_ROB_index <= '0;

		    // mdp update to rob
			last_rob_mdp_update_valid <= '0;
			last_rob_mdp_update_mdp_info <= '0;
			last_rob_mdp_update_ROB_index <= '0;
        end
        else begin

		    // ldu_cq CAM update
		        // implied dep
			ldu_cq_CAM_update_valid <= next_ldu_cq_CAM_update_valid;
			ldu_cq_CAM_update_ld_mdp_info <= next_ldu_cq_CAM_update_ld_mdp_info;
			ldu_cq_CAM_update_ld_ROB_index <= next_ldu_cq_CAM_update_ld_ROB_index;
			ldu_cq_CAM_update_stamo_mdp_info <= next_ldu_cq_CAM_update_stamo_mdp_info;
			ldu_cq_CAM_update_stamo_ROB_index <= next_ldu_cq_CAM_update_stamo_ROB_index;

		    // ldu_mq CAM update
		        // implied dep
			ldu_mq_CAM_update_valid <= next_ldu_mq_CAM_update_valid;
			ldu_mq_CAM_update_ld_mdp_info <= next_ldu_mq_CAM_update_ld_mdp_info;
			ldu_mq_CAM_update_ld_ROB_index <= next_ldu_mq_CAM_update_ld_ROB_index;
			ldu_mq_CAM_update_stamo_mdp_info <= next_ldu_mq_CAM_update_stamo_mdp_info;
			ldu_mq_CAM_update_stamo_ROB_index <= next_ldu_mq_CAM_update_stamo_ROB_index;

		    // ldu_cq commit update
		        // implied no dep
		        // incorporates ldu_mq commit update
			ldu_cq_commit_update_valid <= next_ldu_cq_commit_update_valid;
			ldu_cq_commit_update_mdp_info <= next_ldu_cq_commit_update_mdp_info;
			ldu_cq_commit_update_ROB_index <= next_ldu_cq_commit_update_ROB_index;

		    // stamofu_cq CAM update bank 0
		        // implied dep
		        // incorporates stamofu_mq CAM update
			stamofu_cq_CAM_bank0_update_valid <= next_stamofu_cq_CAM_bank0_update_valid;
			stamofu_cq_CAM_bank0_update_ld_mdp_info <= next_stamofu_cq_CAM_bank0_update_ld_mdp_info;
			stamofu_cq_CAM_bank0_update_ld_ROB_index <= next_stamofu_cq_CAM_bank0_update_ld_ROB_index;
			stamofu_cq_CAM_bank0_update_stamo_mdp_info <= next_stamofu_cq_CAM_bank0_update_stamo_mdp_info;
			stamofu_cq_CAM_bank0_update_stamo_ROB_index <= next_stamofu_cq_CAM_bank0_update_stamo_ROB_index;

		    // stamofu_cq CAM update bank 1
		        // implied dep
		        // incorporates stamofu_mq CAM update
			stamofu_cq_CAM_bank1_update_valid <= next_stamofu_cq_CAM_bank1_update_valid;
			stamofu_cq_CAM_bank1_update_ld_mdp_info <= next_stamofu_cq_CAM_bank1_update_ld_mdp_info;
			stamofu_cq_CAM_bank1_update_ld_ROB_index <= next_stamofu_cq_CAM_bank1_update_ld_ROB_index;
			stamofu_cq_CAM_bank1_update_stamo_mdp_info <= next_stamofu_cq_CAM_bank1_update_stamo_mdp_info;
			stamofu_cq_CAM_bank1_update_stamo_ROB_index <= next_stamofu_cq_CAM_bank1_update_stamo_ROB_index;

		    // stamofu_cq commit update
		        // implied no dep
		        // incorporates stamofu_mq commit update
			stamofu_cq_commit_update_valid <= next_stamofu_cq_commit_update_valid;
			stamofu_cq_commit_update_mdp_info <= next_stamofu_cq_commit_update_mdp_info;
			stamofu_cq_commit_update_ROB_index <= next_stamofu_cq_commit_update_ROB_index;

		    // mdp update to rob
			last_rob_mdp_update_valid <= rob_mdp_update_valid;
			last_rob_mdp_update_mdp_info <= rob_mdp_update_mdp_info;
			last_rob_mdp_update_ROB_index <= rob_mdp_update_ROB_index;
        end
    end

endmodule