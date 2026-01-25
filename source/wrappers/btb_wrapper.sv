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
	input corep::ASID_t next_arch_asid,

    // read req stage
	input logic next_read_req_valid,
	input corep::fetch_idx_t next_read_req_fetch_index,

    // read resp stage
	input corep::PC38_t next_read_resp_pc38,

	output corep::BTB_info_t [corep::FETCH_LANES-1:0] last_resp_resp_btb_info_by_lane,
	output logic [corep::FETCH_LANES-1:0] last_read_resp_hit_by_lane,
	output corep::BTB_way_idx_t [corep::FETCH_LANES-1:0] last_read_resp_hit_way_by_lane,

    // update
	input logic next_update_valid,
	input corep::PC38_t next_update_pc38,
	input corep::BTB_info_t next_update_btb_info,
	input logic next_update_hit,
	input corep::BTB_way_idx_t next_update_hit_way
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // arch state
	corep::ASID_t arch_asid;

    // read req stage
	logic read_req_valid;
	corep::fetch_idx_t read_req_fetch_index;

    // read resp stage
	corep::PC38_t read_resp_pc38;

	corep::BTB_info_t [corep::FETCH_LANES-1:0] resp_resp_btb_info_by_lane;
	logic [corep::FETCH_LANES-1:0] read_resp_hit_by_lane;
	corep::BTB_way_idx_t [corep::FETCH_LANES-1:0] read_resp_hit_way_by_lane;

    // update
	logic update_valid;
	corep::PC38_t update_pc38;
	corep::BTB_info_t update_btb_info;
	logic update_hit;
	corep::BTB_way_idx_t update_hit_way;

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
			read_req_fetch_index <= '0;

		    // read resp stage
			read_resp_pc38 <= '0;

			last_resp_resp_btb_info_by_lane <= '0;
			last_read_resp_hit_by_lane <= '0;
			last_read_resp_hit_way_by_lane <= '0;

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
			read_req_fetch_index <= next_read_req_fetch_index;

		    // read resp stage
			read_resp_pc38 <= next_read_resp_pc38;

			last_resp_resp_btb_info_by_lane <= resp_resp_btb_info_by_lane;
			last_read_resp_hit_by_lane <= read_resp_hit_by_lane;
			last_read_resp_hit_way_by_lane <= read_resp_hit_way_by_lane;

		    // update
			update_valid <= next_update_valid;
			update_pc38 <= next_update_pc38;
			update_btb_info <= next_update_btb_info;
			update_hit <= next_update_hit;
			update_hit_way <= next_update_hit_way;
        end
    end

endmodule