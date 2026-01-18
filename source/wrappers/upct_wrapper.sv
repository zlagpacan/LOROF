/*
    Filename: upct_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around upct module. 
    Spec: LOROF/spec/design/upct.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module upct_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // pc_gen read in
	input logic next_pc_gen_read_valid,
	input corep::UPCT_idx_t next_pc_gen_read_index,

    // pc_gen read out
	output corep::UPC_t last_pc_gen_read_upc,

    // update in
	input logic next_update_valid,
	input corep::UPC_t next_update_upc,

    // update out
	output corep::UPCT_idx_t last_update_upct_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // pc_gen read in
	logic pc_gen_read_valid;
	corep::UPCT_idx_t pc_gen_read_index;

    // pc_gen read out
	corep::UPC_t pc_gen_read_upc;

    // update in
	logic update_valid;
	corep::UPC_t update_upc;

    // update out
	corep::UPCT_idx_t update_upct_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

	upct #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // pc_gen read in
			pc_gen_read_valid <= '0;
			pc_gen_read_index <= '0;

		    // pc_gen read out
			last_pc_gen_read_upc <= '0;

		    // update in
			update_valid <= '0;
			update_upc <= '0;

		    // update out
			last_update_upct_index <= '0;
        end
        else begin


		    // pc_gen read in
			pc_gen_read_valid <= next_pc_gen_read_valid;
			pc_gen_read_index <= next_pc_gen_read_index;

		    // pc_gen read out
			last_pc_gen_read_upc <= pc_gen_read_upc;

		    // update in
			update_valid <= next_update_valid;
			update_upc <= next_update_upc;

		    // update out
			last_update_upct_index <= update_upct_index;
        end
    end

endmodule