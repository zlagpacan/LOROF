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


    // arch state
	input corep::ASID_t next_arch_asid,

    // read req stage
	input logic next_read_req_valid,
	input corep::fetch_idx_t next_read_req_fetch_index,
	input corep::GH_t next_read_req_gh,

    // read resp stage
	input corep::fetch_lane_t next_read_resp_redirect_lane,

	output logic last_read_resp_taken,

    // update
	input logic next_update_valid,
	input corep::PC38_t next_update_pc38,
	input corep::GH_t next_update_gh,
	input logic next_update_taken
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // arch state
	corep::ASID_t arch_asid;

    // read req stage
	logic read_req_valid;
	corep::fetch_idx_t read_req_fetch_index;
	corep::GH_t read_req_gh;

    // read resp stage
	corep::fetch_lane_t read_resp_redirect_lane;

	logic read_resp_taken;

    // update
	logic update_valid;
	corep::PC38_t update_pc38;
	corep::GH_t update_gh;
	logic update_taken;

    // ----------------------------------------------------------------
    // Module Instantiation:

	pht #(
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
			read_req_gh <= '0;

		    // read resp stage
			read_resp_redirect_lane <= '0;

			last_read_resp_taken <= '0;

		    // update
			update_valid <= '0;
			update_pc38 <= '0;
			update_gh <= '0;
			update_taken <= '0;
        end
        else begin


		    // arch state
			arch_asid <= next_arch_asid;

		    // read req stage
			read_req_valid <= next_read_req_valid;
			read_req_fetch_index <= next_read_req_fetch_index;
			read_req_gh <= next_read_req_gh;

		    // read resp stage
			read_resp_redirect_lane <= next_read_resp_redirect_lane;

			last_read_resp_taken <= read_resp_taken;

		    // update
			update_valid <= next_update_valid;
			update_pc38 <= next_update_pc38;
			update_gh <= next_update_gh;
			update_taken <= next_update_taken;
        end
    end

endmodule