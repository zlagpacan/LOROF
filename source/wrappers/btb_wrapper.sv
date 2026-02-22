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


    // read req stage
	input logic next_read_req_valid,
	input corep::fetch_idx_t next_read_req_fetch_idx,
	input corep::asid_t next_read_req_asid,

    // read resp0 stage
	input logic next_read_resp0_valid,
	input corep::pc38_t next_read_resp0_pc38,

    // read resp1 stage
	output logic last_read_resp1_hit,
	output logic last_read_resp1_double_hit,
	output corep::btb_way_t last_read_resp1_hit_way,

	output corep::fetch_lane_t last_read_resp1_hit_lane_way0,
	output corep::fetch_lane_t last_read_resp1_hit_lane_way1,
	output corep::btb_info_t last_read_resp1_btb_info_way0,
	output corep::btb_info_t last_read_resp1_btb_info_way1,

    // update
	input logic next_update_valid,
	input corep::pc38_t next_update_pc38,
	input corep::asid_t next_update_asid,
	input corep::btb_info_t next_update_btb_info,
	input logic next_update_hit,
	input corep::btb_way_t next_update_hit_way
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // read req stage
	logic read_req_valid;
	corep::fetch_idx_t read_req_fetch_idx;
	corep::asid_t read_req_asid;

    // read resp0 stage
	logic read_resp0_valid;
	corep::pc38_t read_resp0_pc38;

    // read resp1 stage
	logic read_resp1_hit;
	logic read_resp1_double_hit;
	corep::btb_way_t read_resp1_hit_way;

	corep::fetch_lane_t read_resp1_hit_lane_way0;
	corep::fetch_lane_t read_resp1_hit_lane_way1;
	corep::btb_info_t read_resp1_btb_info_way0;
	corep::btb_info_t read_resp1_btb_info_way1;

    // update
	logic update_valid;
	corep::pc38_t update_pc38;
	corep::asid_t update_asid;
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


		    // read req stage
			read_req_valid <= '0;
			read_req_fetch_idx <= '0;
			read_req_asid <= '0;

		    // read resp0 stage
			read_resp0_valid <= '0;
			read_resp0_pc38 <= '0;

		    // read resp1 stage
			last_read_resp1_hit <= '0;
			last_read_resp1_double_hit <= '0;
			last_read_resp1_hit_way <= '0;

			last_read_resp1_hit_lane_way0 <= '0;
			last_read_resp1_hit_lane_way1 <= '0;
			last_read_resp1_btb_info_way0 <= '0;
			last_read_resp1_btb_info_way1 <= '0;

		    // update
			update_valid <= '0;
			update_pc38 <= '0;
			update_asid <= '0;
			update_btb_info <= '0;
			update_hit <= '0;
			update_hit_way <= '0;
        end
        else begin


		    // read req stage
			read_req_valid <= next_read_req_valid;
			read_req_fetch_idx <= next_read_req_fetch_idx;
			read_req_asid <= next_read_req_asid;

		    // read resp0 stage
			read_resp0_valid <= next_read_resp0_valid;
			read_resp0_pc38 <= next_read_resp0_pc38;

		    // read resp1 stage
			last_read_resp1_hit <= read_resp1_hit;
			last_read_resp1_double_hit <= read_resp1_double_hit;
			last_read_resp1_hit_way <= read_resp1_hit_way;

			last_read_resp1_hit_lane_way0 <= read_resp1_hit_lane_way0;
			last_read_resp1_hit_lane_way1 <= read_resp1_hit_lane_way1;
			last_read_resp1_btb_info_way0 <= read_resp1_btb_info_way0;
			last_read_resp1_btb_info_way1 <= read_resp1_btb_info_way1;

		    // update
			update_valid <= next_update_valid;
			update_pc38 <= next_update_pc38;
			update_asid <= next_update_asid;
			update_btb_info <= next_update_btb_info;
			update_hit <= next_update_hit;
			update_hit_way <= next_update_hit_way;
        end
    end

endmodule