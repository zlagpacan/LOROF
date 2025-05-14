/*
    Filename: stamofu_aq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around stamofu_aq module. 
    Spec: LOROF/spec/design/stamofu_aq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stamofu_aq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to acquire queue
	input logic next_stamofu_aq_enq_valid,
	input logic next_stamofu_aq_enq_mem_aq,
	input logic next_stamofu_aq_enq_io_aq,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_aq_enq_ROB_index,

    // acquire queue enqueue feedback
	output logic last_stamofu_aq_enq_ready,

    // op update
	input logic next_stamofu_aq_update_valid,
	input logic next_stamofu_aq_update_mem_aq,
	input logic next_stamofu_aq_update_io_aq,
	input logic [LOG_ROB_ENTRIES-1:0] next_stamofu_aq_update_ROB_index,

    // op dequeue from acquire queue
	input logic next_stamofu_aq_deq_valid,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_aq_deq_ROB_index,

    // ROB info and kill
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_abs_head_index,
	input logic next_rob_kill_valid,
	input logic [LOG_ROB_ENTRIES-1:0] next_rob_kill_rel_kill_younger_index,

    // acquire advertisement
	output logic last_stamofu_aq_mem_aq_active,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_aq_mem_aq_oldest_abs_ROB_index,
	output logic last_stamofu_aq_io_aq_active,
	output logic [LOG_ROB_ENTRIES-1:0] last_stamofu_aq_io_aq_oldest_abs_ROB_index
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // op enqueue to acquire queue
	logic stamofu_aq_enq_valid;
	logic stamofu_aq_enq_mem_aq;
	logic stamofu_aq_enq_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_enq_ROB_index;

    // acquire queue enqueue feedback
	logic stamofu_aq_enq_ready;

    // op update
	logic stamofu_aq_update_valid;
	logic stamofu_aq_update_mem_aq;
	logic stamofu_aq_update_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_update_ROB_index;

    // op dequeue from acquire queue
	logic stamofu_aq_deq_valid;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_deq_ROB_index;

    // ROB info and kill
	logic [LOG_ROB_ENTRIES-1:0] rob_abs_head_index;
	logic rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] rob_kill_rel_kill_younger_index;

    // acquire advertisement
	logic stamofu_aq_mem_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_mem_aq_oldest_abs_ROB_index;
	logic stamofu_aq_io_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] stamofu_aq_io_aq_oldest_abs_ROB_index;

    // ----------------------------------------------------------------
    // Module Instantiation:

    stamofu_aq #(.STAMOFU_AQ_ENTRIES(STAMOFU_AQ_ENTRIES)) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // op enqueue to acquire queue
			stamofu_aq_enq_valid <= '0;
			stamofu_aq_enq_mem_aq <= '0;
			stamofu_aq_enq_io_aq <= '0;
			stamofu_aq_enq_ROB_index <= '0;

		    // acquire queue enqueue feedback
			last_stamofu_aq_enq_ready <= '0;

		    // op update
			stamofu_aq_update_valid <= '0;
			stamofu_aq_update_mem_aq <= '0;
			stamofu_aq_update_io_aq <= '0;
			stamofu_aq_update_ROB_index <= '0;

		    // op dequeue from acquire queue
			stamofu_aq_deq_valid <= '0;
			last_stamofu_aq_deq_ROB_index <= '0;

		    // ROB info and kill
			rob_abs_head_index <= '0;
			rob_kill_valid <= '0;
			rob_kill_rel_kill_younger_index <= '0;

		    // acquire advertisement
			last_stamofu_aq_mem_aq_active <= '0;
			last_stamofu_aq_mem_aq_oldest_abs_ROB_index <= '0;
			last_stamofu_aq_io_aq_active <= '0;
			last_stamofu_aq_io_aq_oldest_abs_ROB_index <= '0;
        end
        else begin

		    // op enqueue to acquire queue
			stamofu_aq_enq_valid <= next_stamofu_aq_enq_valid;
			stamofu_aq_enq_mem_aq <= next_stamofu_aq_enq_mem_aq;
			stamofu_aq_enq_io_aq <= next_stamofu_aq_enq_io_aq;
			stamofu_aq_enq_ROB_index <= next_stamofu_aq_enq_ROB_index;

		    // acquire queue enqueue feedback
			last_stamofu_aq_enq_ready <= stamofu_aq_enq_ready;

		    // op update
			stamofu_aq_update_valid <= next_stamofu_aq_update_valid;
			stamofu_aq_update_mem_aq <= next_stamofu_aq_update_mem_aq;
			stamofu_aq_update_io_aq <= next_stamofu_aq_update_io_aq;
			stamofu_aq_update_ROB_index <= next_stamofu_aq_update_ROB_index;

		    // op dequeue from acquire queue
			stamofu_aq_deq_valid <= next_stamofu_aq_deq_valid;
			last_stamofu_aq_deq_ROB_index <= stamofu_aq_deq_ROB_index;

		    // ROB info and kill
			rob_abs_head_index <= next_rob_abs_head_index;
			rob_kill_valid <= next_rob_kill_valid;
			rob_kill_rel_kill_younger_index <= next_rob_kill_rel_kill_younger_index;

		    // acquire advertisement
			last_stamofu_aq_mem_aq_active <= stamofu_aq_mem_aq_active;
			last_stamofu_aq_mem_aq_oldest_abs_ROB_index <= stamofu_aq_mem_aq_oldest_abs_ROB_index;
			last_stamofu_aq_io_aq_active <= stamofu_aq_io_aq_active;
			last_stamofu_aq_io_aq_oldest_abs_ROB_index <= stamofu_aq_io_aq_oldest_abs_ROB_index;
        end
    end

endmodule