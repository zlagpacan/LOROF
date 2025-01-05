/*
    Filename: prf_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around prf module. 
    Spec: LOROF/spec/design/prf.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // reg read req by read requester
	input logic [PRF_RR_COUNT-1:0] next_reg_read_req_valid_by_rr,
	input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] next_reg_read_req_PR_by_rr,

    // reg read info by read requestor
	output logic [PRF_RR_COUNT-1:0] last_reg_read_ack_by_rr,
	output logic [PRF_RR_COUNT-1:0] last_reg_read_port_by_rr,

    // reg read data by bank
	output logic [PRF_BANK_COUNT-1:0][1:0][31:0] last_reg_read_data_by_bank_by_port,

    // writeback data by write requestor
	input logic [PRF_WR_COUNT-1:0] next_WB_valid_by_wr,
	input logic [PRF_WR_COUNT-1:0][31:0] next_WB_data_by_wr,
	input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] next_WB_PR_by_wr,
	input logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0] next_WB_ROB_index_by_wr,

    // writeback backpressure by write requestor
	output logic [PRF_WR_COUNT-1:0] last_WB_ready_by_wr,

    // writeback bus by bank
	output logic [PRF_BANK_COUNT-1:0] last_WB_bus_valid_by_bank,
	output logic [PRF_BANK_COUNT-1:0][31:0] last_WB_bus_data_by_bank,
	output logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] last_WB_bus_upper_PR_by_bank,
	output logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] last_WB_bus_ROB_index_by_bank,

    // forward data from PRF
	output logic [PRF_BANK_COUNT-1:0][31:0] last_forward_data_by_bank
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // reg read req by read requester
	logic [PRF_RR_COUNT-1:0] reg_read_req_valid_by_rr;
	logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] reg_read_req_PR_by_rr;

    // reg read info by read requestor
	logic [PRF_RR_COUNT-1:0] reg_read_ack_by_rr;
	logic [PRF_RR_COUNT-1:0] reg_read_port_by_rr;

    // reg read data by bank
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port;

    // writeback data by write requestor
	logic [PRF_WR_COUNT-1:0] WB_valid_by_wr;
	logic [PRF_WR_COUNT-1:0][31:0] WB_data_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] WB_PR_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0] WB_ROB_index_by_wr;

    // writeback backpressure by write requestor
	logic [PRF_WR_COUNT-1:0] WB_ready_by_wr;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][31:0] WB_bus_data_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] WB_bus_ROB_index_by_bank;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank;

    // ----------------------------------------------------------------
    // Module Instantiation:

    prf #(.USE_BRAM(1'b1)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // reg read req by read requester
			reg_read_req_valid_by_rr <= '0;
			reg_read_req_PR_by_rr <= '0;

		    // reg read info by read requestor
			last_reg_read_ack_by_rr <= '0;
			last_reg_read_port_by_rr <= '0;

		    // reg read data by bank
			last_reg_read_data_by_bank_by_port <= '0;

		    // writeback data by write requestor
			WB_valid_by_wr <= '0;
			WB_data_by_wr <= '0;
			WB_PR_by_wr <= '0;
			WB_ROB_index_by_wr <= '0;

		    // writeback backpressure by write requestor
			last_WB_ready_by_wr <= '1;

		    // writeback bus by bank
			last_WB_bus_valid_by_bank <= '0;
			last_WB_bus_data_by_bank <= '0;
			last_WB_bus_upper_PR_by_bank <= '0;
			last_WB_bus_ROB_index_by_bank <= '0;

		    // forward data from PRF
			last_forward_data_by_bank <= '0;
        end
        else begin


		    // reg read req by read requester
			reg_read_req_valid_by_rr <= next_reg_read_req_valid_by_rr;
			reg_read_req_PR_by_rr <= next_reg_read_req_PR_by_rr;

		    // reg read info by read requestor
			last_reg_read_ack_by_rr <= reg_read_ack_by_rr;
			last_reg_read_port_by_rr <= reg_read_port_by_rr;

		    // reg read data by bank
			last_reg_read_data_by_bank_by_port <= reg_read_data_by_bank_by_port;

		    // writeback data by write requestor
			WB_valid_by_wr <= next_WB_valid_by_wr;
			WB_data_by_wr <= next_WB_data_by_wr;
			WB_PR_by_wr <= next_WB_PR_by_wr;
			WB_ROB_index_by_wr <= next_WB_ROB_index_by_wr;

		    // writeback backpressure by write requestor
			last_WB_ready_by_wr <= WB_ready_by_wr;

		    // writeback bus by bank
			last_WB_bus_valid_by_bank <= WB_bus_valid_by_bank;
			last_WB_bus_data_by_bank <= WB_bus_data_by_bank;
			last_WB_bus_upper_PR_by_bank <= WB_bus_upper_PR_by_bank;
			last_WB_bus_ROB_index_by_bank <= WB_bus_ROB_index_by_bank;

		    // forward data from PRF
			last_forward_data_by_bank <= forward_data_by_bank;
        end
    end

endmodule