/*
    Filename: fpu_top_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fpu_top module. 
    Spec: LOROF/spec/design/fpu_top.md
*/

`timescale 1ns/100ps

`include "fpp.vh"

module fpu_top_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

    // Input instruction and transaction metadata
	input logic next_in_valid,
	output logic last_in_ready,
	input logic [4:0] next_in_opcode5,
	input logic [4:0] next_in_funct5_op,
	input logic next_in_fmt,
	input logic [4:0] next_in_rs2,
	input logic [2:0] next_in_funct3,
	input fpp::fp_tag_t next_in_fp_tag,
	input logic [2:0] next_in_fcsr_rm,

    // Decoded operands, with single precision values already NaN-box checked
	input fpp::double_t next_in_A_d,
	input fpp::single_t next_in_A_s_boxed,
	input fpp::double_t next_in_B_d,
	input fpp::single_t next_in_B_s_boxed,
	input fpp::double_t next_in_C_d,
	input fpp::single_t next_in_C_s_boxed,

    // Unified result interface
	output logic last_out_valid,
	input logic next_out_ready,
	output fpp::fp_tag_t last_out_fp_tag,
	output fpp::double_t last_out_result_d,
	output fpp::fpu_except_t last_out_except
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // Input instruction and transaction metadata
	logic in_valid;
	logic in_ready;
	logic [4:0] in_opcode5;
	logic [4:0] in_funct5_op;
	logic in_fmt;
	logic [4:0] in_rs2;
	logic [2:0] in_funct3;
	fpp::fp_tag_t in_fp_tag;
	logic [2:0] in_fcsr_rm;

    // Decoded operands, with single precision values already NaN-box checked
	fpp::double_t in_A_d;
	fpp::single_t in_A_s_boxed;
	fpp::double_t in_B_d;
	fpp::single_t in_B_s_boxed;
	fpp::double_t in_C_d;
	fpp::single_t in_C_s_boxed;

    // Unified result interface
	logic out_valid;
	logic out_ready;
	fpp::fp_tag_t out_fp_tag;
	fpp::double_t out_result_d;
	fpp::fpu_except_t out_except;

    // ----------------------------------------------------------------
    // Module Instantiation:

	fpu_top #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // Input instruction and transaction metadata
			in_valid <= '0;
			last_in_ready <= '0;
			in_opcode5 <= '0;
			in_funct5_op <= '0;
			in_fmt <= '0;
			in_rs2 <= '0;
			in_funct3 <= '0;
			in_fp_tag <= '0;
			in_fcsr_rm <= '0;

		    // Decoded operands, with single precision values already NaN-box checked
			in_A_d <= '0;
			in_A_s_boxed <= '0;
			in_B_d <= '0;
			in_B_s_boxed <= '0;
			in_C_d <= '0;
			in_C_s_boxed <= '0;

		    // Unified result interface
			last_out_valid <= '0;
			out_ready <= '0;
			last_out_fp_tag <= '0;
			last_out_result_d <= '0;
			last_out_except <= '0;
        end
        else begin

		    // Input instruction and transaction metadata
			in_valid <= next_in_valid;
			last_in_ready <= in_ready;
			in_opcode5 <= next_in_opcode5;
			in_funct5_op <= next_in_funct5_op;
			in_fmt <= next_in_fmt;
			in_rs2 <= next_in_rs2;
			in_funct3 <= next_in_funct3;
			in_fp_tag <= next_in_fp_tag;
			in_fcsr_rm <= next_in_fcsr_rm;

		    // Decoded operands, with single precision values already NaN-box checked
			in_A_d <= next_in_A_d;
			in_A_s_boxed <= next_in_A_s_boxed;
			in_B_d <= next_in_B_d;
			in_B_s_boxed <= next_in_B_s_boxed;
			in_C_d <= next_in_C_d;
			in_C_s_boxed <= next_in_C_s_boxed;

		    // Unified result interface
			last_out_valid <= out_valid;
			out_ready <= next_out_ready;
			last_out_fp_tag <= out_fp_tag;
			last_out_result_d <= out_result_d;
			last_out_except <= out_except;
        end
    end

endmodule