/*
    Filename: operand_collector_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around operand_collector module. 
    Spec: LOROF/spec/design/operand_collector.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module operand_collector_wrapper #(
	parameter OC_ENTRIES = 3,
	parameter LOG_OC_ENTRIES = $clog2(OC_ENTRIES),
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // issue info
	input logic next_enq_valid,
	input logic next_enq_is_reg,
	input logic next_enq_is_bus_forward,
	input logic next_enq_is_fast_forward,
	input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] next_enq_fast_forward_pipe,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_enq_bank,

    // reg read data from PRF
	input logic next_reg_read_resp_valid,
	input logic [31:0] next_reg_read_resp_data,

    // bus forward data from PRF
	input logic [PRF_BANK_COUNT-1:0][31:0] next_bus_forward_data_by_bank,

    // fast forward data
	input logic [FAST_FORWARD_PIPE_COUNT-1:0] next_fast_forward_data_valid_by_pipe,
	input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] next_fast_forward_data_by_pipe,

    // operand collection control
	output logic last_operand_notif_valid,
	input logic next_operand_notif_ack,
	output logic [31:0] last_operand_data,
	input logic next_operand_data_ack
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // issue info
	logic enq_valid;
	logic enq_is_reg;
	logic enq_is_bus_forward;
	logic enq_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] enq_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] enq_bank;

    // reg read data from PRF
	logic reg_read_resp_valid;
	logic [31:0] reg_read_resp_data;

    // bus forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] bus_forward_data_by_bank;

    // fast forward data
	logic [FAST_FORWARD_PIPE_COUNT-1:0] fast_forward_data_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] fast_forward_data_by_pipe;

    // operand collection control
	logic operand_notif_valid;
	logic operand_notif_ack;
	logic [31:0] operand_data;
	logic operand_data_ack;

    // ----------------------------------------------------------------
    // Module Instantiation:

	operand_collector #(
		.OC_ENTRIES(OC_ENTRIES),
		.LOG_OC_ENTRIES(LOG_OC_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // issue info
			enq_valid <= '0;
			enq_is_reg <= '0;
			enq_is_bus_forward <= '0;
			enq_is_fast_forward <= '0;
			enq_fast_forward_pipe <= '0;
			enq_bank <= '0;

		    // reg read data from PRF
			reg_read_resp_valid <= '0;
			reg_read_resp_data <= '0;

		    // bus forward data from PRF
			bus_forward_data_by_bank <= '0;

		    // fast forward data
			fast_forward_data_valid_by_pipe <= '0;
			fast_forward_data_by_pipe <= '0;

		    // operand collection control
			last_operand_notif_valid <= '0;
			operand_notif_ack <= '0;
			last_operand_data <= '0;
			operand_data_ack <= '0;
        end
        else begin

		    // issue info
			enq_valid <= next_enq_valid;
			enq_is_reg <= next_enq_is_reg;
			enq_is_bus_forward <= next_enq_is_bus_forward;
			enq_is_fast_forward <= next_enq_is_fast_forward;
			enq_fast_forward_pipe <= next_enq_fast_forward_pipe;
			enq_bank <= next_enq_bank;

		    // reg read data from PRF
			reg_read_resp_valid <= next_reg_read_resp_valid;
			reg_read_resp_data <= next_reg_read_resp_data;

		    // bus forward data from PRF
			bus_forward_data_by_bank <= next_bus_forward_data_by_bank;

		    // fast forward data
			fast_forward_data_valid_by_pipe <= next_fast_forward_data_valid_by_pipe;
			fast_forward_data_by_pipe <= next_fast_forward_data_by_pipe;

		    // operand collection control
			last_operand_notif_valid <= operand_notif_valid;
			operand_notif_ack <= next_operand_notif_ack;
			last_operand_data <= operand_data;
			operand_data_ack <= next_operand_data_ack;
        end
    end

endmodule