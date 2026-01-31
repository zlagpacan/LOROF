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
	input corep::pc38_t next_link_pc38,

    // pc_gen return control
	input logic next_ret_valid,

	output logic last_ret_fallback,
	output corep::pc38_t last_ret_pc38,
	output corep::ras_idx_t last_ret_ras_idx,
	output corep::ras_cnt_t last_ret_ras_cnt,

    // update control
	input logic next_update_valid,
	input corep::ras_idx_t next_update_ras_idx,
	input corep::ras_cnt_t next_update_ras_cnt
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // pc_gen link control
	logic link_valid;
	corep::pc38_t link_pc38;

    // pc_gen return control
	logic ret_valid;

	logic ret_fallback;
	corep::pc38_t ret_pc38;
	corep::ras_idx_t ret_ras_idx;
	corep::ras_cnt_t ret_ras_cnt;

    // update control
	logic update_valid;
	corep::ras_idx_t update_ras_idx;
	corep::ras_cnt_t update_ras_cnt;

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

			last_ret_fallback <= '0;
			last_ret_pc38 <= '0;
			last_ret_ras_idx <= '0;
			last_ret_ras_cnt <= '0;

		    // update control
			update_valid <= '0;
			update_ras_idx <= '0;
			update_ras_cnt <= '0;
        end
        else begin


		    // pc_gen link control
			link_valid <= next_link_valid;
			link_pc38 <= next_link_pc38;

		    // pc_gen return control
			ret_valid <= next_ret_valid;

			last_ret_fallback <= ret_fallback;
			last_ret_pc38 <= ret_pc38;
			last_ret_ras_idx <= ret_ras_idx;
			last_ret_ras_cnt <= ret_ras_cnt;

		    // update control
			update_valid <= next_update_valid;
			update_ras_idx <= next_update_ras_idx;
			update_ras_cnt <= next_update_ras_cnt;
        end
    end

endmodule