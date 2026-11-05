/*
    Filename: fpu_easy_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fpu_easy module. 
    Spec: LOROF/spec/design/fpu_easy.md
*/

`timescale 1ns/100ps

`include "fpp.vh"

module fpu_easy_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,
    // fully comb

    // instr components
	input logic [6:0] next_funct7,
	input logic [2:0] next_funct3,

    // operands
	input fpp::double_t next_A_d,
	input fpp::double_t next_B_d,

	input fpp::single_t next_A_s_boxed,
	input fpp::single_t next_B_s_boxed,

    // outputs
	output fpp::double_t last_result_d,
	output fpp::fpu_except_t last_except
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
    // fully comb

    // instr components
	logic [6:0] funct7;
	logic [2:0] funct3;

    // operands
	fpp::double_t A_d;
	fpp::double_t B_d;

	fpp::single_t A_s_boxed;
	fpp::single_t B_s_boxed;

    // outputs
	fpp::double_t result_d;
	fpp::fpu_except_t except;

    // ----------------------------------------------------------------
    // Module Instantiation:

	fpu_easy #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
		    // fully comb

		    // instr components
			funct7 <= '0;
			funct3 <= '0;

		    // operands
			A_d <= '0;
			B_d <= '0;

			A_s_boxed <= '0;
			B_s_boxed <= '0;

		    // outputs
			last_result_d <= '0;
			last_except <= '0;
        end
        else begin
		    // fully comb

		    // instr components
			funct7 <= next_funct7;
			funct3 <= next_funct3;

		    // operands
			A_d <= next_A_d;
			B_d <= next_B_d;

			A_s_boxed <= next_A_s_boxed;
			B_s_boxed <= next_B_s_boxed;

		    // outputs
			last_result_d <= result_d;
			last_except <= except;
        end
    end

endmodule