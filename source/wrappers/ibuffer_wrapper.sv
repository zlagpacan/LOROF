/*
    Filename: ibuffer_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around ibuffer module. 
    Spec: LOROF/spec/design/ibuffer.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module ibuffer_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // enq
	input logic next_enq_valid,
	input corep::ibuffer_enq_info_t next_enq_info,
	input logic next_enq_fetch_hit_valid,
	input corep::fetch16B_t next_enq_fetch_hit_fetch16B,

    // enq feedback
	output logic last_enq_ready,
	output corep::fmid_t last_enq_fmid,

    // fetch miss return
	input logic next_fetch_miss_return_valid,
	input corep::fmid_t next_fetch_miss_return_fmid,
	input corep::fetch16B_t next_fetch_miss_return_fetch16B,

    // deq
	output logic last_deq_valid,
	output corep::ibuffer_deq_entry_t [3:0] last_deq_entry_by_way,

    // def feedback
	input logic next_deq_ready,

    // restart
	input logic next_restart_valid
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // enq
	logic enq_valid;
	corep::ibuffer_enq_info_t enq_info;
	logic enq_fetch_hit_valid;
	corep::fetch16B_t enq_fetch_hit_fetch16B;

    // enq feedback
	logic enq_ready;
	corep::fmid_t enq_fmid;

    // fetch miss return
	logic fetch_miss_return_valid;
	corep::fmid_t fetch_miss_return_fmid;
	corep::fetch16B_t fetch_miss_return_fetch16B;

    // deq
	logic deq_valid;
	corep::ibuffer_deq_entry_t [3:0] deq_entry_by_way;

    // def feedback
	logic deq_ready;

    // restart
	logic restart_valid;

    // ----------------------------------------------------------------
    // Module Instantiation:

	ibuffer #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // enq
			enq_valid <= '0;
			enq_info <= '0;
			enq_fetch_hit_valid <= '0;
			enq_fetch_hit_fetch16B <= '0;

		    // enq feedback
			last_enq_ready <= '0;
			last_enq_fmid <= '0;

		    // fetch miss return
			fetch_miss_return_valid <= '0;
			fetch_miss_return_fmid <= '0;
			fetch_miss_return_fetch16B <= '0;

		    // deq
			last_deq_valid <= '0;
			last_deq_entry_by_way <= '0;

		    // def feedback
			deq_ready <= '0;

		    // restart
			restart_valid <= '0;
        end
        else begin


		    // enq
			enq_valid <= next_enq_valid;
			enq_info <= next_enq_info;
			enq_fetch_hit_valid <= next_enq_fetch_hit_valid;
			enq_fetch_hit_fetch16B <= next_enq_fetch_hit_fetch16B;

		    // enq feedback
			last_enq_ready <= enq_ready;
			last_enq_fmid <= enq_fmid;

		    // fetch miss return
			fetch_miss_return_valid <= next_fetch_miss_return_valid;
			fetch_miss_return_fmid <= next_fetch_miss_return_fmid;
			fetch_miss_return_fetch16B <= next_fetch_miss_return_fetch16B;

		    // deq
			last_deq_valid <= deq_valid;
			last_deq_entry_by_way <= deq_entry_by_way;

		    // def feedback
			deq_ready <= next_deq_ready;

		    // restart
			restart_valid <= next_restart_valid;
        end
    end

endmodule