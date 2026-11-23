/*
    Filename: fpu_convert_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fpu_convert module. 
    Spec: LOROF/spec/design/fpu_convert.md
*/

`timescale 1ns/100ps

`include "fpp.vh"

module fpu_convert_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

    // input control
	input logic next_in_valid,
	input fpp::fp_tag_t next_in_fp_tag,

	output logic last_in_ready,

    // instr components
	input logic [6:0] next_in_funct7,
	input logic [4:0] next_in_funct5,
	input logic [2:0] next_in_instr_rm,
	input logic [2:0] next_in_fcsr_rm,

    // fp input
	input fpp::double_t next_in_A_d,
	input fpp::single_t next_in_A_s_boxed,

    // output control
	output logic last_out_valid,
	output fpp::fp_tag_t last_out_fp_tag,

	input logic next_out_ready,

    // fp output
	output fpp::double_t last_out_result_d,
	output fpp::fpu_except_t last_out_except
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // input control
	logic in_valid;
	fpp::fp_tag_t in_fp_tag;

	logic in_ready;

    // instr components
	logic [6:0] in_funct7;
	logic [4:0] in_funct5;
	logic [2:0] in_instr_rm;
	logic [2:0] in_fcsr_rm;

    // fp input
	fpp::double_t in_A_d;
	fpp::single_t in_A_s_boxed;

    // output control
	logic out_valid;
	fpp::fp_tag_t out_fp_tag;

	logic out_ready;

    // fp output
	fpp::double_t out_result_d;
	fpp::fpu_except_t out_except;

    // ----------------------------------------------------------------
    // Module Instantiation:

	fpu_convert #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // input control
			in_valid <= '0;
			in_fp_tag <= '0;

			last_in_ready <= '0;

		    // instr components
			in_funct7 <= '0;
			in_funct5 <= '0;
			in_instr_rm <= '0;
			in_fcsr_rm <= '0;

		    // fp input
			in_A_d <= '0;
			in_A_s_boxed <= '0;

		    // output control
			last_out_valid <= '0;
			last_out_fp_tag <= '0;

			out_ready <= '0;

		    // fp output
			last_out_result_d <= '0;
			last_out_except <= '0;
        end
        else begin

		    // input control
			in_valid <= next_in_valid;
			in_fp_tag <= next_in_fp_tag;

			last_in_ready <= in_ready;

		    // instr components
			in_funct7 <= next_in_funct7;
			in_funct5 <= next_in_funct5;
			in_instr_rm <= next_in_instr_rm;
			in_fcsr_rm <= next_in_fcsr_rm;

		    // fp input
			in_A_d <= next_in_A_d;
			in_A_s_boxed <= next_in_A_s_boxed;

		    // output control
			last_out_valid <= out_valid;
			last_out_fp_tag <= out_fp_tag;

			out_ready <= next_out_ready;

		    // fp output
			last_out_result_d <= out_result_d;
			last_out_except <= out_except;
        end
    end

endmodule