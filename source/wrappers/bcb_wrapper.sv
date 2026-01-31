/*
    Filename: bcb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bcb module. 
    Spec: LOROF/spec/design/bcb.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module bcb_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // save control
	input logic next_save_valid,
	input corep::BTB_info_t next_save_bcb_info,

	output corep::BCB_idx_t last_save_bcb_index,

    // restore control
	input corep::BCB_idx_t next_restore_bcb_index,

	output corep::BTB_info_t last_restore_bcb_info
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // save control
	logic save_valid;
	corep::BTB_info_t save_bcb_info;

	corep::BCB_idx_t save_bcb_index;

    // restore control
	corep::BCB_idx_t restore_bcb_index;

	corep::BTB_info_t restore_bcb_info;

    // ----------------------------------------------------------------
    // Module Instantiation:

	bcb #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // save control
			save_valid <= '0;
			save_bcb_info <= '0;

			last_save_bcb_index <= '0;

		    // restore control
			restore_bcb_index <= '0;

			last_restore_bcb_info <= '0;
        end
        else begin


		    // save control
			save_valid <= next_save_valid;
			save_bcb_info <= next_save_bcb_info;

			last_save_bcb_index <= save_bcb_index;

		    // restore control
			restore_bcb_index <= next_restore_bcb_index;

			last_restore_bcb_info <= restore_bcb_info;
        end
    end

endmodule