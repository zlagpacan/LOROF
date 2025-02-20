/*
    Filename: alu_pipeline_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around alu_pipeline module. 
    Spec: LOROF/spec/design/alu_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_pipeline_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // ALU op issue from ALU IQ
	input logic next_valid_in,
	input logic [3:0] next_op_in,
	input logic next_is_imm_in,
	input logic [31:0] next_imm_in,
	input logic next_A_unneeded_in,
	input logic next_A_forward_in,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_A_bank_in,
	input logic next_B_forward_in,
	input logic [LOG_PRF_BANK_COUNT-1:0] next_B_bank_in,
	input logic [LOG_PR_COUNT-1:0] next_dest_PR_in,

    // reg read info and data from PRF
	input logic next_A_reg_read_valid_in,
	input logic next_B_reg_read_valid_in,
	input logic [PRF_BANK_COUNT-1:0][31:0] next_reg_read_data_by_bank_in,

    // forward data from PRF
	input logic [PRF_BANK_COUNT-1:0][31:0] next_forward_data_by_bank_in,

    // ready feedback to ALU IQ
	output logic last_ready_out,

    // writeback data to PRF
	output logic last_WB_valid_out,
	output logic [31:0] last_WB_data_out,
	output logic [LOG_PR_COUNT-1:0] last_WB_PR_out
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // ALU op issue from ALU IQ
	logic valid_in;
	logic [3:0] op_in;
	logic is_imm_in;
	logic [31:0] imm_in;
	logic A_unneeded_in;
	logic A_forward_in;
	logic [LOG_PRF_BANK_COUNT-1:0] A_bank_in;
	logic B_forward_in;
	logic [LOG_PRF_BANK_COUNT-1:0] B_bank_in;
	logic [LOG_PR_COUNT-1:0] dest_PR_in;

    // reg read info and data from PRF
	logic A_reg_read_valid_in;
	logic B_reg_read_valid_in;
	logic [PRF_BANK_COUNT-1:0][31:0] reg_read_data_by_bank_in;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank_in;

    // ready feedback to ALU IQ
	logic ready_out;

    // writeback data to PRF
	logic WB_valid_out;
	logic [31:0] WB_data_out;
	logic [LOG_PR_COUNT-1:0] WB_PR_out;

    // ----------------------------------------------------------------
    // Module Instantiation:

    alu_pipeline WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // ALU op issue from ALU IQ
			valid_in <= 1'b0;
			op_in <= 4'b0000;
			is_imm_in <= 1'b0;
			imm_in <= 32'h0;
			A_unneeded_in <= 1'b0;
			A_forward_in <= 1'b0;
			A_bank_in <= 2'h0;
			B_forward_in <= 1'b0;
			B_bank_in <= 2'h0;
			dest_PR_in <= 6'h0;

		    // reg read info and data from PRF
			A_reg_read_valid_in <= 1'b0;
			B_reg_read_valid_in <= 1'b0;
			reg_read_data_by_bank_in <= {32'h0, 32'h0, 32'h0, 32'h0};

		    // forward data from PRF
			forward_data_by_bank_in <= {32'h0, 32'h0, 32'h0, 32'h0};

		    // ready feedback to ALU IQ
			last_ready_out <= 1'b1;

		    // writeback data to PRF
			last_WB_valid_out <= 1'b0;
			last_WB_data_out <= 32'h0;
			last_WB_PR_out <= 6'h0;
        end
        else begin


		    // ALU op issue from ALU IQ
			valid_in <= next_valid_in;
			op_in <= next_op_in;
			is_imm_in <= next_is_imm_in;
			imm_in <= next_imm_in;
			A_unneeded_in <= next_A_unneeded_in;
			A_forward_in <= next_A_forward_in;
			A_bank_in <= next_A_bank_in;
			B_forward_in <= next_B_forward_in;
			B_bank_in <= next_B_bank_in;
			dest_PR_in <= next_dest_PR_in;

		    // reg read info and data from PRF
			A_reg_read_valid_in <= next_A_reg_read_valid_in;
			B_reg_read_valid_in <= next_B_reg_read_valid_in;
			reg_read_data_by_bank_in <= next_reg_read_data_by_bank_in;

		    // forward data from PRF
			forward_data_by_bank_in <= next_forward_data_by_bank_in;

		    // ready feedback to ALU IQ
			last_ready_out <= ready_out;

		    // writeback data to PRF
			last_WB_valid_out <= WB_valid_out;
			last_WB_data_out <= WB_data_out;
			last_WB_PR_out <= WB_PR_out;
        end
    end

endmodule