/*
    Filename: ar_dep_check_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ar_dep_check module. 
    Spec: LOROF/spec/design/ar_dep_check.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ar_dep_check_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // inputs by way
	input logic [3:0] next_valid_by_way,
	input logic [3:0][4:0] next_A_AR_by_way,
	input logic [3:0][4:0] next_B_AR_by_way,
	input logic [3:0][4:0] next_dest_AR_by_way,

    // outputs by way
	output logic [3:0] last_A_PR_dep_by_way,
	output logic [3:0][1:0] last_A_PR_sel_by_way,
	output logic [3:0] last_B_PR_dep_by_way,
	output logic [3:0][1:0] last_B_PR_sel_by_way
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // inputs by way
	logic [3:0] valid_by_way;
	logic [3:0][4:0] A_AR_by_way;
	logic [3:0][4:0] B_AR_by_way;
	logic [3:0][4:0] dest_AR_by_way;

    // outputs by way
	logic [3:0] A_PR_dep_by_way;
	logic [3:0][1:0] A_PR_sel_by_way;
	logic [3:0] B_PR_dep_by_way;
	logic [3:0][1:0] B_PR_sel_by_way;

    // ----------------------------------------------------------------
    // Module Instantiation:

    ar_dep_check WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // inputs by way
			valid_by_way <= '0;
			A_AR_by_way <= '0;
			B_AR_by_way <= '0;
			dest_AR_by_way <= '0;

		    // outputs by way
			last_A_PR_dep_by_way <= '0;
			last_A_PR_sel_by_way <= '0;
			last_B_PR_dep_by_way <= '0;
			last_B_PR_sel_by_way <= '0;
        end
        else begin

		    // inputs by way
			valid_by_way <= next_valid_by_way;
			A_AR_by_way <= next_A_AR_by_way;
			B_AR_by_way <= next_B_AR_by_way;
			dest_AR_by_way <= next_dest_AR_by_way;

		    // outputs by way
			last_A_PR_dep_by_way <= A_PR_dep_by_way;
			last_A_PR_sel_by_way <= A_PR_sel_by_way;
			last_B_PR_dep_by_way <= B_PR_dep_by_way;
			last_B_PR_sel_by_way <= B_PR_sel_by_way;
        end
    end

endmodule