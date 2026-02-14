/*
    Filename: mdpt_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around mdpt module. 
    Spec: LOROF/spec/design/mdpt.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module mdpt_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // read req stage
	input logic next_read_req_valid,
	input corep::fetch_idx_t next_read_req_fetch_idx,
	input corep::asid_t next_read_req_asid,

    // read resp stage
	output corep::mdpt_set_t last_read_resp_mdp_by_lane,

    // update
	input logic next_update_valid,
	input corep::pc38_t next_update_pc38,
	input corep::asid_t next_update_asid,
	input corep::mdp_t next_update_mdp
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // read req stage
	logic read_req_valid;
	corep::fetch_idx_t read_req_fetch_idx;
	corep::asid_t read_req_asid;

    // read resp stage
	corep::mdpt_set_t read_resp_mdp_by_lane;

    // update
	logic update_valid;
	corep::pc38_t update_pc38;
	corep::asid_t update_asid;
	corep::mdp_t update_mdp;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mdpt #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // read req stage
			read_req_valid <= '0;
			read_req_fetch_idx <= '0;
			read_req_asid <= '0;

		    // read resp stage
			last_read_resp_mdp_by_lane <= '0;

		    // update
			update_valid <= '0;
			update_pc38 <= '0;
			update_asid <= '0;
			update_mdp <= '0;
        end
        else begin


		    // read req stage
			read_req_valid <= next_read_req_valid;
			read_req_fetch_idx <= next_read_req_fetch_idx;
			read_req_asid <= next_read_req_asid;

		    // read resp stage
			last_read_resp_mdp_by_lane <= read_resp_mdp_by_lane;

		    // update
			update_valid <= next_update_valid;
			update_pc38 <= next_update_pc38;
			update_asid <= next_update_asid;
			update_mdp <= next_update_mdp;
        end
    end

endmodule