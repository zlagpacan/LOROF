/*
    Filename: map_table_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around map_table module. 
    Spec: LOROF/spec/design/map_table.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module map_table_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,

    // reg reads
	input corep::ar6_t [3:0] next_A_ar6_by_way,
	output corep::pr_t [3:0] last_A_pr_by_way,

	input corep::ar6_t [3:0] next_B_ar6_by_way,
	output corep::pr_t [3:0] last_B_pr_by_way,

	input corep::ar5_t [3:0] next_C_far_by_way,
	output corep::pr_t [3:0] last_C_pr_by_way,

    // reg writes
	input logic [3:0] next_dest_write_valid_by_way,
	input corep::ar6_t [3:0] next_dest_ar6_by_way,
	output corep::pr_t [3:0] last_dest_old_pr_by_way,
	input corep::pr_t [3:0] next_dest_new_pr_by_way,

    // checkpoint save
	output corep::map_table_t last_save_map_table,

    // checkpoint restore
	input logic next_restore_valid,
	input corep::map_table_t next_restore_map_table
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // reg reads
	corep::ar6_t [3:0] A_ar6_by_way;
	corep::pr_t [3:0] A_pr_by_way;

	corep::ar6_t [3:0] B_ar6_by_way;
	corep::pr_t [3:0] B_pr_by_way;

	corep::ar5_t [3:0] C_far_by_way;
	corep::pr_t [3:0] C_pr_by_way;

    // reg writes
	logic [3:0] dest_write_valid_by_way;
	corep::ar6_t [3:0] dest_ar6_by_way;
	corep::pr_t [3:0] dest_old_pr_by_way;
	corep::pr_t [3:0] dest_new_pr_by_way;

    // checkpoint save
	corep::map_table_t save_map_table;

    // checkpoint restore
	logic restore_valid;
	corep::map_table_t restore_map_table;

    // ----------------------------------------------------------------
    // Module Instantiation:

	map_table #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // reg reads
			A_ar6_by_way <= '0;
			last_A_pr_by_way <= '0;

			B_ar6_by_way <= '0;
			last_B_pr_by_way <= '0;

			C_far_by_way <= '0;
			last_C_pr_by_way <= '0;

		    // reg writes
			dest_write_valid_by_way <= '0;
			dest_ar6_by_way <= '0;
			last_dest_old_pr_by_way <= '0;
			dest_new_pr_by_way <= '0;

		    // checkpoint save
			last_save_map_table <= '0;

		    // checkpoint restore
			restore_valid <= '0;
			restore_map_table <= '0;
        end
        else begin

		    // reg reads
			A_ar6_by_way <= next_A_ar6_by_way;
			last_A_pr_by_way <= A_pr_by_way;

			B_ar6_by_way <= next_B_ar6_by_way;
			last_B_pr_by_way <= B_pr_by_way;

			C_far_by_way <= next_C_far_by_way;
			last_C_pr_by_way <= C_pr_by_way;

		    // reg writes
			dest_write_valid_by_way <= next_dest_write_valid_by_way;
			dest_ar6_by_way <= next_dest_ar6_by_way;
			last_dest_old_pr_by_way <= dest_old_pr_by_way;
			dest_new_pr_by_way <= next_dest_new_pr_by_way;

		    // checkpoint save
			last_save_map_table <= save_map_table;

		    // checkpoint restore
			restore_valid <= next_restore_valid;
			restore_map_table <= next_restore_map_table;
        end
    end

endmodule