/*
    Filename: ibtb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ibtb module. 
    Spec: LOROF/spec/design/ibtb.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module ibtb_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // arch state
	input corep::ASID_t next_arch_asid,

    // read
	input corep::PC38_t next_read_src_pc38,
	input corep::IBTB_GH_t next_read_ibtb_gh,

	output corep::PC38_t last_read_tgt_pc38,

    // update
	input logic next_update_valid,
	input corep::PC38_t next_update_src_pc38,
	input corep::PC38_t next_update_ibtb_gh,
	input corep::PC38_t next_update_tgt_pc38
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // arch state
	corep::ASID_t arch_asid;

    // read
	corep::PC38_t read_src_pc38;
	corep::IBTB_GH_t read_ibtb_gh;

	corep::PC38_t read_tgt_pc38;

    // update
	logic update_valid;
	corep::PC38_t update_src_pc38;
	corep::PC38_t update_ibtb_gh;
	corep::PC38_t update_tgt_pc38;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ibtb #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // arch state
			arch_asid <= '0;

		    // read
			read_src_pc38 <= '0;
			read_ibtb_gh <= '0;

			last_read_tgt_pc38 <= '0;

		    // update
			update_valid <= '0;
			update_src_pc38 <= '0;
			update_ibtb_gh <= '0;
			update_tgt_pc38 <= '0;
        end
        else begin


		    // arch state
			arch_asid <= next_arch_asid;

		    // read
			read_src_pc38 <= next_read_src_pc38;
			read_ibtb_gh <= next_read_ibtb_gh;

			last_read_tgt_pc38 <= read_tgt_pc38;

		    // update
			update_valid <= next_update_valid;
			update_src_pc38 <= next_update_src_pc38;
			update_ibtb_gh <= next_update_ibtb_gh;
			update_tgt_pc38 <= next_update_tgt_pc38;
        end
    end

endmodule