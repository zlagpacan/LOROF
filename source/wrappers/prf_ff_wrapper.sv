/*
    Filename: prf_ff_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around prf_ff module. 
    Spec: LOROF/spec/design/prf_ff.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf_ff_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // read req info by read requester
	input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] next_read_req_PR_by_rr,

    // read resp info by read requestor
	output logic [PRF_RR_COUNT-1:0][31:0] last_read_resp_data_by_rr,

    // writeback info by write requestor
	input logic [PRF_WR_COUNT-1:0] next_WB_valid_by_wr,
	input logic [PRF_WR_COUNT-1:0][31:0] next_WB_data_by_wr,
	input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] next_WB_PR_by_wr
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // read req info by read requester
	logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] read_req_PR_by_rr;

    // read resp info by read requestor
	logic [PRF_RR_COUNT-1:0][31:0] read_resp_data_by_rr;

    // writeback info by write requestor
	logic [PRF_WR_COUNT-1:0] WB_valid_by_wr;
	logic [PRF_WR_COUNT-1:0][31:0] WB_data_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] WB_PR_by_wr;

    // ----------------------------------------------------------------
    // Module Instantiation:

    prf_ff WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // read req info by read requester
			read_req_PR_by_rr <= '0;

		    // read resp info by read requestor
			last_read_resp_data_by_rr <= '0;

		    // writeback info by write requestor
			WB_valid_by_wr <= '0;
			WB_data_by_wr <= '0;
			WB_PR_by_wr <= '0;
        end
        else begin


		    // read req info by read requester
			read_req_PR_by_rr <= next_read_req_PR_by_rr;

		    // read resp info by read requestor
			last_read_resp_data_by_rr <= read_resp_data_by_rr;

		    // writeback info by write requestor
			WB_valid_by_wr <= next_WB_valid_by_wr;
			WB_data_by_wr <= next_WB_data_by_wr;
			WB_PR_by_wr <= next_WB_PR_by_wr;
        end
    end

endmodule