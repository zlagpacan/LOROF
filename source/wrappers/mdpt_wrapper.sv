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


    // arch state
	input corep::asid_t next_arch_asid,

    // read req stage
	input logic next_read_req_valid,
	input corep::fetch_idx_t next_read_req_fetch_idx,

    // read resp stage
	output corep::mdpt_set_t last_read_resp_mdp_by_lane,

    // update
	input logic next_update_valid,
	input corep::pc38_t next_update_pc38,
	input corep::mdp_t next_update_mdp
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // arch state
	corep::asid_t arch_asid;

    // read req stage
	logic read_req_valid;
	corep::fetch_idx_t read_req_fetch_idx;

    // read resp stage
	corep::mdpt_set_t read_resp_mdp_by_lane;

    // update
	logic update_valid;
	corep::pc38_t update_pc38;
	corep::mdp_t update_mdp;

    // ----------------------------------------------------------------
    // Module Instantiation:

	mdpt #(
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
			last_read_resp_mdp_by_lane <= '0;

		    // update
			update_valid <= '0;
			update_pc38 <= '0;
			update_mdp <= '0;
        end
        else begin


		    // arch state
			arch_asid <= next_arch_asid;

		    // read req stage
			read_req_valid <= next_read_req_valid;
			read_req_fetch_idx <= next_read_req_fetch_idx;

		    // read resp stage
			last_read_resp_mdp_by_lane <= read_resp_mdp_by_lane;

		    // update
			update_valid <= next_update_valid;
			update_pc38 <= next_update_pc38;
			update_mdp <= next_update_mdp;
        end
    end

endmodule