/*
    Filename: prf_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around prf module. 
    Spec: LOROF/spec/design/prf.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter PR_COUNT = core_types_pkg::PR_COUNT;
parameter LOG_PR_COUNT = $clog2(PR_COUNT);
parameter PRF_BANK_COUNT = core_types_pkg::PRF_BANK_COUNT;
parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT);
parameter PRF_RR_COUNT = core_types_pkg::PRF_RR_COUNT;
parameter PRF_WR_COUNT = core_types_pkg::PRF_WR_COUNT;
parameter USE_BRAM = 1'b0;

module prf_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // read req info by read requester
	input logic [PRF_RR_COUNT-1:0] next_read_req_valid_by_rr,
	input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] next_read_req_PR_by_rr,

    // read resp info by read requestor
	output logic [PRF_RR_COUNT-1:0] last_read_resp_ack_by_rr,
	output logic [PRF_RR_COUNT-1:0] last_read_resp_port_by_rr,

    // read data by bank
	output logic [PRF_BANK_COUNT-1:0][1:0][31:0] last_read_data_by_bank_by_port,

    // writeback info by write requestor
	input logic [PRF_WR_COUNT-1:0] next_WB_valid_by_wr,
	input logic [PRF_WR_COUNT-1:0] next_WB_send_complete_by_wr,
	input logic [PRF_WR_COUNT-1:0][31:0] next_WB_data_by_wr,
	input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] next_WB_PR_by_wr,
	input logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0] next_WB_ROB_index_by_wr,

    // writeback feedback by write requestor
	output logic [PRF_WR_COUNT-1:0] last_WB_ready_by_wr,

    // writeback bus by bank
	output logic [PRF_BANK_COUNT-1:0] last_WB_bus_valid_by_bank,
	output logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] last_WB_bus_upper_PR_by_bank,

    // forward data by bank
	output logic [PRF_BANK_COUNT-1:0][31:0] last_forward_data_bus_by_bank,

    // complete bus by bank
	output logic [PRF_BANK_COUNT-1:0] last_complete_bus_valid_by_bank,
	output logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] last_complete_bus_ROB_index_by_bank
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // read req info by read requester
	logic [PRF_RR_COUNT-1:0] read_req_valid_by_rr;
	logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] read_req_PR_by_rr;

    // read resp info by read requestor
	logic [PRF_RR_COUNT-1:0] read_resp_ack_by_rr;
	logic [PRF_RR_COUNT-1:0] read_resp_port_by_rr;

    // read data by bank
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] read_data_by_bank_by_port;

    // writeback info by write requestor
	logic [PRF_WR_COUNT-1:0] WB_valid_by_wr;
	logic [PRF_WR_COUNT-1:0] WB_send_complete_by_wr;
	logic [PRF_WR_COUNT-1:0][31:0] WB_data_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] WB_PR_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0] WB_ROB_index_by_wr;

    // writeback feedback by write requestor
	logic [PRF_WR_COUNT-1:0] WB_ready_by_wr;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // forward data by bank
	logic [PRF_BANK_COUNT-1:0][31:0] forward_data_bus_by_bank;

    // complete bus by bank
	logic [PRF_BANK_COUNT-1:0] complete_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] complete_bus_ROB_index_by_bank;

    // ----------------------------------------------------------------
    // Module Instantiation:

	prf #(
		.PR_COUNT(PR_COUNT),
		.LOG_PR_COUNT(LOG_PR_COUNT),
		.PRF_BANK_COUNT(PRF_BANK_COUNT),
		.LOG_PRF_BANK_COUNT(LOG_PRF_BANK_COUNT),
		.PRF_RR_COUNT(PRF_RR_COUNT),
		.PRF_WR_COUNT(PRF_WR_COUNT),
		.USE_BRAM(USE_BRAM)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // read req info by read requester
			read_req_valid_by_rr <= '0;
			read_req_PR_by_rr <= '0;

		    // read resp info by read requestor
			last_read_resp_ack_by_rr <= '0;
			last_read_resp_port_by_rr <= '0;

		    // read data by bank
			last_read_data_by_bank_by_port <= '0;

		    // writeback info by write requestor
			WB_valid_by_wr <= '0;
			WB_send_complete_by_wr <= '0;
			WB_data_by_wr <= '0;
			WB_PR_by_wr <= '0;
			WB_ROB_index_by_wr <= '0;

		    // writeback feedback by write requestor
			last_WB_ready_by_wr <= '0;

		    // writeback bus by bank
			last_WB_bus_valid_by_bank <= '0;
			last_WB_bus_upper_PR_by_bank <= '0;

		    // forward data by bank
			last_forward_data_bus_by_bank <= '0;

		    // complete bus by bank
			last_complete_bus_valid_by_bank <= '0;
			last_complete_bus_ROB_index_by_bank <= '0;
        end
        else begin


		    // read req info by read requester
			read_req_valid_by_rr <= next_read_req_valid_by_rr;
			read_req_PR_by_rr <= next_read_req_PR_by_rr;

		    // read resp info by read requestor
			last_read_resp_ack_by_rr <= read_resp_ack_by_rr;
			last_read_resp_port_by_rr <= read_resp_port_by_rr;

		    // read data by bank
			last_read_data_by_bank_by_port <= read_data_by_bank_by_port;

		    // writeback info by write requestor
			WB_valid_by_wr <= next_WB_valid_by_wr;
			WB_send_complete_by_wr <= next_WB_send_complete_by_wr;
			WB_data_by_wr <= next_WB_data_by_wr;
			WB_PR_by_wr <= next_WB_PR_by_wr;
			WB_ROB_index_by_wr <= next_WB_ROB_index_by_wr;

		    // writeback feedback by write requestor
			last_WB_ready_by_wr <= WB_ready_by_wr;

		    // writeback bus by bank
			last_WB_bus_valid_by_bank <= WB_bus_valid_by_bank;
			last_WB_bus_upper_PR_by_bank <= WB_bus_upper_PR_by_bank;

		    // forward data by bank
			last_forward_data_bus_by_bank <= forward_data_bus_by_bank;

		    // complete bus by bank
			last_complete_bus_valid_by_bank <= complete_bus_valid_by_bank;
			last_complete_bus_ROB_index_by_bank <= complete_bus_ROB_index_by_bank;
        end
    end

endmodule