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
	input corep::asid_t next_arch_asid,

    // read
	input corep::pc38_t next_read_src_pc38,
	input corep::ibtb_gh_t next_read_ibtb_gh,

	output corep::ibtb_info_t last_read_tgt_ibtb_info,

    // update
	input logic next_update_valid,
	input corep::pc38_t next_update_src_pc38,
	input corep::pc38_t next_update_ibtb_gh,
	input corep::ibtb_info_t next_update_tgt_ibtb_info
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // arch state
	corep::asid_t arch_asid;

    // read
	corep::pc38_t read_src_pc38;
	corep::ibtb_gh_t read_ibtb_gh;

	corep::ibtb_info_t read_tgt_ibtb_info;

    // update
	logic update_valid;
	corep::pc38_t update_src_pc38;
	corep::pc38_t update_ibtb_gh;
	corep::ibtb_info_t update_tgt_ibtb_info;

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

			last_read_tgt_ibtb_info <= '0;

		    // update
			update_valid <= '0;
			update_src_pc38 <= '0;
			update_ibtb_gh <= '0;
			update_tgt_ibtb_info <= '0;
        end
        else begin


		    // arch state
			arch_asid <= next_arch_asid;

		    // read
			read_src_pc38 <= next_read_src_pc38;
			read_ibtb_gh <= next_read_ibtb_gh;

			last_read_tgt_ibtb_info <= read_tgt_ibtb_info;

		    // update
			update_valid <= next_update_valid;
			update_src_pc38 <= next_update_src_pc38;
			update_ibtb_gh <= next_update_ibtb_gh;
			update_tgt_ibtb_info <= next_update_tgt_ibtb_info;
        end
    end

endmodule