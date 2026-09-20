/*
    Filename: rat_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around rat module. 
    Spec: LOROF/spec/design/rat.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module rat_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

    // rat reads
	input corep::ar6_t [3:0] next_A_ar6_by_way,
	output corep::pr_t [3:0] last_A_pr_by_way,

	input corep::ar6_t [3:0] next_B_ar6_by_way,
	output corep::pr_t [3:0] last_B_pr_by_way,

	input corep::ar5_t [3:0] next_C_ar5_by_way,
	output corep::pr_t [3:0] last_C_pr_by_way,

    // rat writes
	input logic [3:0] next_dest_write_valid_by_way,
	input corep::ar6_t [3:0] next_dest_ar6_by_way,
	output corep::pr_t [3:0] last_dest_old_pr_by_way,
	input corep::pr_t [3:0] next_dest_new_pr_by_way,

    // instr yields
	input logic [3:0] next_instr_valid_by_way,
	input logic [3:0] next_instr_has_freg_by_way,
	output logic [3:0] last_instr_yield_by_way,

    // decode_unit control
	input logic [3:0] next_perform_rename_by_way,

    // checkpoint save
	output corep::rat_t last_save_irat,
	output corep::rat_t last_save_frat,

    // checkpoint restore
	input logic next_restore_valid,
	input corep::rat_t next_restore_irat,
	input corep::rat_t next_restore_frat
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // rat reads
	corep::ar6_t [3:0] A_ar6_by_way;
	corep::pr_t [3:0] A_pr_by_way;

	corep::ar6_t [3:0] B_ar6_by_way;
	corep::pr_t [3:0] B_pr_by_way;

	corep::ar5_t [3:0] C_ar5_by_way;
	corep::pr_t [3:0] C_pr_by_way;

    // rat writes
	logic [3:0] dest_write_valid_by_way;
	corep::ar6_t [3:0] dest_ar6_by_way;
	corep::pr_t [3:0] dest_old_pr_by_way;
	corep::pr_t [3:0] dest_new_pr_by_way;

    // instr yields
	logic [3:0] instr_valid_by_way;
	logic [3:0] instr_has_freg_by_way;
	logic [3:0] instr_yield_by_way;

    // decode_unit control
	logic [3:0] perform_rename_by_way;

    // checkpoint save
	corep::rat_t save_irat;
	corep::rat_t save_frat;

    // checkpoint restore
	logic restore_valid;
	corep::rat_t restore_irat;
	corep::rat_t restore_frat;

    // ----------------------------------------------------------------
    // Module Instantiation:

	rat #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // rat reads
			A_ar6_by_way <= '0;
			last_A_pr_by_way <= '0;

			B_ar6_by_way <= '0;
			last_B_pr_by_way <= '0;

			C_ar5_by_way <= '0;
			last_C_pr_by_way <= '0;

		    // rat writes
			dest_write_valid_by_way <= '0;
			dest_ar6_by_way <= '0;
			last_dest_old_pr_by_way <= '0;
			dest_new_pr_by_way <= '0;

		    // instr yields
			instr_valid_by_way <= '0;
			instr_has_freg_by_way <= '0;
			last_instr_yield_by_way <= '0;

		    // decode_unit control
			perform_rename_by_way <= '0;

		    // checkpoint save
			last_save_irat <= '0;
			last_save_frat <= '0;

		    // checkpoint restore
			restore_valid <= '0;
			restore_irat <= '0;
			restore_frat <= '0;
        end
        else begin

		    // rat reads
			A_ar6_by_way <= next_A_ar6_by_way;
			last_A_pr_by_way <= A_pr_by_way;

			B_ar6_by_way <= next_B_ar6_by_way;
			last_B_pr_by_way <= B_pr_by_way;

			C_ar5_by_way <= next_C_ar5_by_way;
			last_C_pr_by_way <= C_pr_by_way;

		    // rat writes
			dest_write_valid_by_way <= next_dest_write_valid_by_way;
			dest_ar6_by_way <= next_dest_ar6_by_way;
			last_dest_old_pr_by_way <= dest_old_pr_by_way;
			dest_new_pr_by_way <= next_dest_new_pr_by_way;

		    // instr yields
			instr_valid_by_way <= next_instr_valid_by_way;
			instr_has_freg_by_way <= next_instr_has_freg_by_way;
			last_instr_yield_by_way <= instr_yield_by_way;

		    // decode_unit control
			perform_rename_by_way <= next_perform_rename_by_way;

		    // checkpoint save
			last_save_irat <= save_irat;
			last_save_frat <= save_frat;

		    // checkpoint restore
			restore_valid <= next_restore_valid;
			restore_irat <= next_restore_irat;
			restore_frat <= next_restore_frat;
        end
    end

endmodule