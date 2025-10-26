/*
    Filename: stamofu_aq_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_aq module. 
    Spec: LOROF/spec/design/stamofu_aq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stamofu_aq_tb ();

    // ----------------------------------------------------------------
    // TB setup:

    // parameters
    parameter PERIOD = 10;

    // TB signals:
    logic CLK = 1'b1, nRST;
    string test_case;
    string sub_test_case;
    int test_num = 0;
    int num_errors = 0;
    logic tb_error = 1'b0;

    // clock gen
    always begin #(PERIOD/2); CLK = ~CLK; end

    // ----------------------------------------------------------------
    // DUT signals:

    // op enqueue to acquire queue
	logic tb_stamofu_aq_enq_valid;
	logic tb_stamofu_aq_enq_mem_aq;
	logic tb_stamofu_aq_enq_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_enq_ROB_index;

    // acquire queue enqueue feedback
	logic DUT_stamofu_aq_enq_ready, expected_stamofu_aq_enq_ready;

    // op update bank 0
	logic tb_stamofu_aq_update_bank0_valid;
	logic tb_stamofu_aq_update_bank0_mem_aq;
	logic tb_stamofu_aq_update_bank0_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_update_bank0_ROB_index;

    // op update bank 1
	logic tb_stamofu_aq_update_bank1_valid;
	logic tb_stamofu_aq_update_bank1_mem_aq;
	logic tb_stamofu_aq_update_bank1_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_aq_update_bank1_ROB_index;

    // op dequeue from acquire queue
	logic tb_stamofu_aq_deq_valid;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_aq_deq_ROB_index, expected_stamofu_aq_deq_ROB_index;

    // ROB info and kill
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_abs_head_index;
	logic tb_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_rel_kill_younger_index;

    // acquire advertisement
	logic DUT_stamofu_aq_mem_aq_active, expected_stamofu_aq_mem_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_aq_mem_aq_oldest_abs_ROB_index, expected_stamofu_aq_mem_aq_oldest_abs_ROB_index;
	logic DUT_stamofu_aq_io_aq_active, expected_stamofu_aq_io_aq_active;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_aq_io_aq_oldest_abs_ROB_index, expected_stamofu_aq_io_aq_oldest_abs_ROB_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_aq #(
		.STAMOFU_AQ_ENTRIES(4)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to acquire queue
		.stamofu_aq_enq_valid(tb_stamofu_aq_enq_valid),
		.stamofu_aq_enq_mem_aq(tb_stamofu_aq_enq_mem_aq),
		.stamofu_aq_enq_io_aq(tb_stamofu_aq_enq_io_aq),
		.stamofu_aq_enq_ROB_index(tb_stamofu_aq_enq_ROB_index),

	    // acquire queue enqueue feedback
		.stamofu_aq_enq_ready(DUT_stamofu_aq_enq_ready),

	    // op update bank 0
		.stamofu_aq_update_bank0_valid(tb_stamofu_aq_update_bank0_valid),
		.stamofu_aq_update_bank0_mem_aq(tb_stamofu_aq_update_bank0_mem_aq),
		.stamofu_aq_update_bank0_io_aq(tb_stamofu_aq_update_bank0_io_aq),
		.stamofu_aq_update_bank0_ROB_index(tb_stamofu_aq_update_bank0_ROB_index),

	    // op update bank 1
		.stamofu_aq_update_bank1_valid(tb_stamofu_aq_update_bank1_valid),
		.stamofu_aq_update_bank1_mem_aq(tb_stamofu_aq_update_bank1_mem_aq),
		.stamofu_aq_update_bank1_io_aq(tb_stamofu_aq_update_bank1_io_aq),
		.stamofu_aq_update_bank1_ROB_index(tb_stamofu_aq_update_bank1_ROB_index),

	    // op dequeue from acquire queue
		.stamofu_aq_deq_valid(tb_stamofu_aq_deq_valid),
		.stamofu_aq_deq_ROB_index(DUT_stamofu_aq_deq_ROB_index),

	    // ROB info and kill
		.rob_abs_head_index(tb_rob_abs_head_index),
		.rob_kill_valid(tb_rob_kill_valid),
		.rob_kill_rel_kill_younger_index(tb_rob_kill_rel_kill_younger_index),

	    // acquire advertisement
		.stamofu_aq_mem_aq_active(DUT_stamofu_aq_mem_aq_active),
		.stamofu_aq_mem_aq_oldest_abs_ROB_index(DUT_stamofu_aq_mem_aq_oldest_abs_ROB_index),
		.stamofu_aq_io_aq_active(DUT_stamofu_aq_io_aq_active),
		.stamofu_aq_io_aq_oldest_abs_ROB_index(DUT_stamofu_aq_io_aq_oldest_abs_ROB_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_stamofu_aq_enq_ready !== DUT_stamofu_aq_enq_ready) begin
			$display("TB ERROR: expected_stamofu_aq_enq_ready (%h) != DUT_stamofu_aq_enq_ready (%h)",
				expected_stamofu_aq_enq_ready, DUT_stamofu_aq_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_deq_ROB_index !== DUT_stamofu_aq_deq_ROB_index) begin
			$display("TB ERROR: expected_stamofu_aq_deq_ROB_index (%h) != DUT_stamofu_aq_deq_ROB_index (%h)",
				expected_stamofu_aq_deq_ROB_index, DUT_stamofu_aq_deq_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_mem_aq_active !== DUT_stamofu_aq_mem_aq_active) begin
			$display("TB ERROR: expected_stamofu_aq_mem_aq_active (%h) != DUT_stamofu_aq_mem_aq_active (%h)",
				expected_stamofu_aq_mem_aq_active, DUT_stamofu_aq_mem_aq_active);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_mem_aq_oldest_abs_ROB_index !== DUT_stamofu_aq_mem_aq_oldest_abs_ROB_index) begin
			$display("TB ERROR: expected_stamofu_aq_mem_aq_oldest_abs_ROB_index (%h) != DUT_stamofu_aq_mem_aq_oldest_abs_ROB_index (%h)",
				expected_stamofu_aq_mem_aq_oldest_abs_ROB_index, DUT_stamofu_aq_mem_aq_oldest_abs_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_io_aq_active !== DUT_stamofu_aq_io_aq_active) begin
			$display("TB ERROR: expected_stamofu_aq_io_aq_active (%h) != DUT_stamofu_aq_io_aq_active (%h)",
				expected_stamofu_aq_io_aq_active, DUT_stamofu_aq_io_aq_active);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_io_aq_oldest_abs_ROB_index !== DUT_stamofu_aq_io_aq_oldest_abs_ROB_index) begin
			$display("TB ERROR: expected_stamofu_aq_io_aq_oldest_abs_ROB_index (%h) != DUT_stamofu_aq_io_aq_oldest_abs_ROB_index (%h)",
				expected_stamofu_aq_io_aq_oldest_abs_ROB_index, DUT_stamofu_aq_io_aq_oldest_abs_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

        #(PERIOD / 10);
        tb_error = 1'b0;
    end
    endtask

    // ----------------------------------------------------------------
    // initial block:

    initial begin

        // ------------------------------------------------------------
        // reset:
        test_case = "reset";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        // inputs:
        sub_test_case = "assert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b0;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h0;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b0;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		expected_stamofu_aq_io_aq_active = 1'b0;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h0;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b0;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		expected_stamofu_aq_io_aq_active = 1'b0;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;

		check_outputs();

        // ------------------------------------------------------------
        // sequence:
        test_case = "sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 2 mem+io",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tmem aq: i",
			"\n\t\tio aq: i",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b1;
		tb_stamofu_aq_enq_io_aq = 1'b1;
		tb_stamofu_aq_enq_ROB_index = 7'h2;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h0;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b0;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		expected_stamofu_aq_io_aq_active = 1'b0;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 3 mem",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v 2 mem+io",
			"\n\t\tmem aq: i",
			"\n\t\tio aq: i",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b1;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h3;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h2;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b0;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		expected_stamofu_aq_io_aq_active = 1'b0;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 7 io",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v 3 mem",
			"\n\t\t\t", "0: v 2 mem+io",
			"\n\t\tmem aq: v 2",
			"\n\t\tio aq: v 2",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b1;
		tb_stamofu_aq_enq_ROB_index = 7'h7;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h2;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h2;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v A mem+io",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 7 io",
			"\n\t\t\t", "1: v 3 mem",
			"\n\t\t\t", "0: v 2 mem+io",
			"\n\t\tmem aq: v 2",
			"\n\t\tio aq: v 2",
			"\n\t\tUpdate: v 2 io",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b1;
		tb_stamofu_aq_enq_io_aq = 1'b1;
		tb_stamofu_aq_enq_ROB_index = 7'hA;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b1;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h2;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h2;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h2;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v C mem",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v A mem+io",
			"\n\t\t\t", "2: v 7 io",
			"\n\t\t\t", "1: v 3 mem",
			"\n\t\t\t", "0: v 2 mem+io",
			"\n\t\tmem aq: v 2",
			"\n\t\tio aq: v 2",
			"\n\t\tUpdate: v 2 io",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b1;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'hC;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b1;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b1;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h2;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b0;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h2;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h2;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v C mem",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v A mem+io",
			"\n\t\t\t", "2: v 7 io",
			"\n\t\t\t", "1: v 3 mem",
			"\n\t\t\t", "0: v 2 io (deq)",
			"\n\t\tmem aq: v 2",
			"\n\t\tio aq: v 2",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b1;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'hC;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b1;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h2;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b0;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h2;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h2;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v C mem",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v A mem+io",
			"\n\t\t\t", "1: v 7 io",
			"\n\t\t\t", "0: v 3 mem",
			"\n\t\tmem aq: v 3",
			"\n\t\tio aq: v 2",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b1;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'hC;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b1;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h2;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h3;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h3;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i D io",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v C mem",
			"\n\t\t\t", "2: v A mem+io",
			"\n\t\t\t", "1: v 7 io",
			"\n\t\t\t", "0: v 3 mem (deq)",
			"\n\t\tmem aq: v 3",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b1;
		tb_stamofu_aq_enq_ROB_index = 7'hD;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b1;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h2;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b0;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h3;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h3;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i D io",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: vK C mem",
			"\n\t\t\t", "1: vK A mem+io",
			"\n\t\t\t", "0: v 7 io",
			"\n\t\tmem aq: v 3",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: v >7"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b1;
		tb_stamofu_aq_enq_ROB_index = 7'hD;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b1;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h2;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h3;
		tb_rob_kill_valid = 1'b1;
		tb_rob_kill_rel_kill_younger_index = 7'h4;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h7;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h3;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v D io",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: k C mem",
			"\n\t\t\t", "1: k A mem+io",
			"\n\t\t\t", "0: v 7 io",
			"\n\t\tmem aq: v A",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b1;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b1;
		tb_stamofu_aq_enq_ROB_index = 7'hD;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b1;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h2;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h7;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'hA;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v D io",
			"\n\t\t\t", "2: k C mem",
			"\n\t\t\t", "1: k A mem+io",
			"\n\t\t\t", "0: v 7 io",
			"\n\t\tmem aq: i",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: v D mem+io",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b1;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b1;
		tb_stamofu_aq_update_bank1_io_aq = 1'b1;
		tb_stamofu_aq_update_bank1_ROB_index = 7'hD;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b0;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h7;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b0;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h7;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v D mem+io",
			"\n\t\t\t", "2: k C mem",
			"\n\t\t\t", "1: k A mem+io",
			"\n\t\t\t", "0: v 7 io",
			"\n\t\tmem aq: i",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b0;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b0;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h7;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b0;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h7;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v D mem+io",
			"\n\t\t\t", "2: k C mem",
			"\n\t\t\t", "1: k A mem+io",
			"\n\t\t\t", "0: v 7 io (deq)",
			"\n\t\tmem aq: v D",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b0;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h7;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'hD;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v D mem+io",
			"\n\t\t\t", "1: k C mem",
			"\n\t\t\t", "0: k A mem+io (deq)",
			"\n\t\tmem aq: v D",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'hA;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'hD;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v D mem+io",
			"\n\t\t\t", "0: k C mem (deq)",
			"\n\t\tmem aq: v D",
			"\n\t\tio aq: v D",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'hC;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'hD;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'hD;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v D mem+io (deq)",
			"\n\t\tmem aq: v D",
			"\n\t\tio aq: v D",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'hD;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'hD;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'hD;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tmem aq: i",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h0;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b1;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'hD;
		expected_stamofu_aq_io_aq_active = 1'b1;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'hD;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tmem aq: i",
			"\n\t\tio aq: v 7",
			"\n\t\tUpdate: i",
			"\n\t\tKill: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to acquire queue
		tb_stamofu_aq_enq_valid = 1'b0;
		tb_stamofu_aq_enq_mem_aq = 1'b0;
		tb_stamofu_aq_enq_io_aq = 1'b0;
		tb_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // op update bank 0
		tb_stamofu_aq_update_bank0_valid = 1'b0;
		tb_stamofu_aq_update_bank0_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank0_io_aq = 1'b0;
		tb_stamofu_aq_update_bank0_ROB_index = 7'h0;
	    // op update bank 1
		tb_stamofu_aq_update_bank1_valid = 1'b0;
		tb_stamofu_aq_update_bank1_mem_aq = 1'b0;
		tb_stamofu_aq_update_bank1_io_aq = 1'b0;
		tb_stamofu_aq_update_bank1_ROB_index = 7'h0;
	    // op dequeue from acquire queue
		tb_stamofu_aq_deq_valid = 1'b1;
	    // ROB info and kill
		tb_rob_abs_head_index = 7'h0;
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;
	    // acquire advertisement

		@(negedge CLK);

		// outputs:

	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		expected_stamofu_aq_enq_ready = 1'b1;
	    // op update
	    // op dequeue from acquire queue
		expected_stamofu_aq_deq_ROB_index = 7'h0;
	    // ROB info and kill
	    // acquire advertisement
		expected_stamofu_aq_mem_aq_active = 1'b0;
		expected_stamofu_aq_mem_aq_oldest_abs_ROB_index = 7'h0;
		expected_stamofu_aq_io_aq_active = 1'b0;
		expected_stamofu_aq_io_aq_oldest_abs_ROB_index = 7'h0;

		check_outputs();

        // ------------------------------------------------------------
        // finish:
        @(posedge CLK); #(PERIOD/10);
        
        test_case = "finish";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        $display();
        if (num_errors) begin
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule