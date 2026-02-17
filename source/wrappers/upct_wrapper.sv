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


    // read in
	input logic next_read_valid,
	input corep::upct_idx_t next_read_idx_way0,
	input corep::upct_idx_t next_read_idx_way1,
	input corep::upct_idx_t next_read_idx_touch,

    // read out
	output corep::upc_t last_read_upc_way0,
	output corep::upc_t last_read_upc_way1,

    // update in
	input logic next_update_valid,
	input corep::upc_t next_update_upc,

    // update out
	output corep::upct_idx_t last_update_upct_idx
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // read in
	logic read_valid;
	corep::upct_idx_t read_idx_way0;
	corep::upct_idx_t read_idx_way1;
	corep::upct_idx_t read_idx_touch;

    // read out
	corep::upc_t read_upc_way0;
	corep::upc_t read_upc_way1;

    // update in
	logic update_valid;
	corep::upc_t update_upc;

    // update out
	corep::upct_idx_t update_upct_idx;

    // ----------------------------------------------------------------
    // Module Instantiation:

	upct #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // read in
			read_valid <= '0;
			read_idx_way0 <= '0;
			read_idx_way1 <= '0;
			read_idx_touch <= '0;

		    // read out
			last_read_upc_way0 <= '0;
			last_read_upc_way1 <= '0;

		    // update in
			update_valid <= '0;
			update_upc <= '0;

		    // update out
			last_update_upct_idx <= '0;
        end
        else begin


		    // read in
			read_valid <= next_read_valid;
			read_idx_way0 <= next_read_idx_way0;
			read_idx_way1 <= next_read_idx_way1;
			read_idx_touch <= next_read_idx_touch;

		    // read out
			last_read_upc_way0 <= read_upc_way0;
			last_read_upc_way1 <= read_upc_way1;

		    // update in
			update_valid <= next_update_valid;
			update_upc <= next_update_upc;

		    // update out
			last_update_upct_idx <= update_upct_idx;
        end
    end

endmodule