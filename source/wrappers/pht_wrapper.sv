/*
    Filename: pht_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around pht module. 
    Spec: LOROF/spec/design/pht.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module pht_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // read req stage
	input logic next_read_req_valid,
	input corep::fetch_idx_t next_read_req_fetch_idx,
	input corep::gh_t next_read_req_gh,
	input corep::asid_t next_read_req_asid,

    // read resp stage
	input corep::fetch_lane_t next_read_resp_redirect_lane,

	output logic last_read_resp_taken,

    // update
	input logic next_update_valid,
	input corep::pc38_t next_update_pc38,
	input corep::gh_t next_update_gh,
	input corep::asid_t next_update_asid,
	input logic next_update_taken
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // read req stage
	logic read_req_valid;
	corep::fetch_idx_t read_req_fetch_idx;
	corep::gh_t read_req_gh;
	corep::asid_t read_req_asid;

    // read resp stage
	corep::fetch_lane_t read_resp_redirect_lane;

	logic read_resp_taken;

    // update
	logic update_valid;
	corep::pc38_t update_pc38;
	corep::gh_t update_gh;
	corep::asid_t update_asid;
	logic update_taken;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pht #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // read req stage
			read_req_valid <= '0;
			read_req_fetch_idx <= '0;
			read_req_gh <= '0;
			read_req_asid <= '0;

		    // read resp stage
			read_resp_redirect_lane <= '0;

			last_read_resp_taken <= '0;

		    // update
			update_valid <= '0;
			update_pc38 <= '0;
			update_gh <= '0;
			update_asid <= '0;
			update_taken <= '0;
        end
        else begin


		    // read req stage
			read_req_valid <= next_read_req_valid;
			read_req_fetch_idx <= next_read_req_fetch_idx;
			read_req_gh <= next_read_req_gh;
			read_req_asid <= next_read_req_asid;

		    // read resp stage
			read_resp_redirect_lane <= next_read_resp_redirect_lane;

			last_read_resp_taken <= read_resp_taken;

		    // update
			update_valid <= next_update_valid;
			update_pc38 <= next_update_pc38;
			update_gh <= next_update_gh;
			update_asid <= next_update_asid;
			update_taken <= next_update_taken;
        end
    end

endmodule