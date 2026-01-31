/*
    Filename: btb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around btb module. 
    Spec: LOROF/spec/design/btb.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module btb_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // arch state
	input corep::asid_t next_arch_asid,

    // read req stage
	input logic next_read_req_valid,
	input corep::fetch_idx_t next_read_req_fetch_idx,

    // read resp stage
	input corep::pc38_t next_read_resp_pc38,

	output logic last_read_resp_hit,
	output corep::btb_way_t last_read_resp_hit_way,
	output corep::fetch_lane_t last_read_resp_hit_lane,
	output logic last_read_resp_double_hit,
	output corep::btb_info_t last_read_resp_btb_info,

    // update
	input logic next_update_valid,
	input corep::pc38_t next_update_pc38,
	input corep::btb_info_t next_update_btb_info,
	input logic next_update_hit,
	input corep::btb_way_t next_update_hit_way
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // arch state
	corep::asid_t arch_asid;

    // read req stage
	logic read_req_valid;
	corep::fetch_idx_t read_req_fetch_idx;

    // read resp stage
	corep::pc38_t read_resp_pc38;

	logic read_resp_hit;
	corep::btb_way_t read_resp_hit_way;
	corep::fetch_lane_t read_resp_hit_lane;
	logic read_resp_double_hit;
	corep::btb_info_t read_resp_btb_info;

    // update
	logic update_valid;
	corep::pc38_t update_pc38;
	corep::btb_info_t update_btb_info;
	logic update_hit;
	corep::btb_way_t update_hit_way;

    // ----------------------------------------------------------------
    // Module Instantiation:

	btb #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // arch state
			arch_asid <= '0;

		    // read req stage
			read_req_valid <= '0;
			read_req_fetch_idx <= '0;

		    // read resp stage
			read_resp_pc38 <= '0;

			last_read_resp_hit <= '0;
			last_read_resp_hit_way <= '0;
			last_read_resp_hit_lane <= '0;
			last_read_resp_double_hit <= '0;
			last_read_resp_btb_info <= '0;

		    // update
			update_valid <= '0;
			update_pc38 <= '0;
			update_btb_info <= '0;
			update_hit <= '0;
			update_hit_way <= '0;
        end
        else begin


		    // arch state
			arch_asid <= next_arch_asid;

		    // read req stage
			read_req_valid <= next_read_req_valid;
			read_req_fetch_idx <= next_read_req_fetch_idx;

		    // read resp stage
			read_resp_pc38 <= next_read_resp_pc38;

			last_read_resp_hit <= read_resp_hit;
			last_read_resp_hit_way <= read_resp_hit_way;
			last_read_resp_hit_lane <= read_resp_hit_lane;
			last_read_resp_double_hit <= read_resp_double_hit;
			last_read_resp_btb_info <= read_resp_btb_info;

		    // update
			update_valid <= next_update_valid;
			update_pc38 <= next_update_pc38;
			update_btb_info <= next_update_btb_info;
			update_hit <= next_update_hit;
			update_hit_way <= next_update_hit_way;
        end
    end

endmodule