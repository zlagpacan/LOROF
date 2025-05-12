/*
    Filename: ldu_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for ldu_iq module. 
    Spec: LOROF/spec/design/ldu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ldu_iq_tb ();

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

    // op enqueue to issue queue
	logic tb_ldu_iq_enq_valid;
	logic [3:0] tb_ldu_iq_enq_op;
	logic [11:0] tb_ldu_iq_enq_imm12;
	logic [LOG_PR_COUNT-1:0] tb_ldu_iq_enq_A_PR;
	logic tb_ldu_iq_enq_A_ready;
	logic tb_ldu_iq_enq_A_is_zero;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic DUT_ldu_iq_enq_ready, expected_ldu_iq_enq_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // pipeline issue
	logic DUT_issue_valid, expected_issue_valid;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic [11:0] DUT_issue_imm12, expected_issue_imm12;
	logic DUT_issue_A_forward, expected_issue_A_forward;
	logic DUT_issue_A_is_zero, expected_issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_A_bank, expected_issue_A_bank;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_issue_cq_index, expected_issue_cq_index;

    // reg read req to PRF
	logic DUT_PRF_req_A_valid, expected_PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_A_PR, expected_PRF_req_A_PR;

    // pipeline feedback
	logic tb_pipeline_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ldu_iq #(
		.LDU_IQ_ENTRIES(4)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to issue queue
		.ldu_iq_enq_valid(tb_ldu_iq_enq_valid),
		.ldu_iq_enq_op(tb_ldu_iq_enq_op),
		.ldu_iq_enq_imm12(tb_ldu_iq_enq_imm12),
		.ldu_iq_enq_A_PR(tb_ldu_iq_enq_A_PR),
		.ldu_iq_enq_A_ready(tb_ldu_iq_enq_A_ready),
		.ldu_iq_enq_A_is_zero(tb_ldu_iq_enq_A_is_zero),
		.ldu_iq_enq_cq_index(tb_ldu_iq_enq_cq_index),

	    // issue queue enqueue feedback
		.ldu_iq_enq_ready(DUT_ldu_iq_enq_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // pipeline issue
		.issue_valid(DUT_issue_valid),
		.issue_op(DUT_issue_op),
		.issue_imm12(DUT_issue_imm12),
		.issue_A_forward(DUT_issue_A_forward),
		.issue_A_is_zero(DUT_issue_A_is_zero),
		.issue_A_bank(DUT_issue_A_bank),
		.issue_cq_index(DUT_issue_cq_index),

	    // reg read req to PRF
		.PRF_req_A_valid(DUT_PRF_req_A_valid),
		.PRF_req_A_PR(DUT_PRF_req_A_PR),

	    // pipeline feedback
		.pipeline_ready(tb_pipeline_ready)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ldu_iq_enq_ready !== DUT_ldu_iq_enq_ready) begin
			$display("TB ERROR: expected_ldu_iq_enq_ready (%h) != DUT_ldu_iq_enq_ready (%h)",
				expected_ldu_iq_enq_ready, DUT_ldu_iq_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_valid !== DUT_issue_valid) begin
			$display("TB ERROR: expected_issue_valid (%h) != DUT_issue_valid (%h)",
				expected_issue_valid, DUT_issue_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_op !== DUT_issue_op) begin
			$display("TB ERROR: expected_issue_op (%h) != DUT_issue_op (%h)",
				expected_issue_op, DUT_issue_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_imm12 !== DUT_issue_imm12) begin
			$display("TB ERROR: expected_issue_imm12 (%h) != DUT_issue_imm12 (%h)",
				expected_issue_imm12, DUT_issue_imm12);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_forward !== DUT_issue_A_forward) begin
			$display("TB ERROR: expected_issue_A_forward (%h) != DUT_issue_A_forward (%h)",
				expected_issue_A_forward, DUT_issue_A_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_is_zero !== DUT_issue_A_is_zero) begin
			$display("TB ERROR: expected_issue_A_is_zero (%h) != DUT_issue_A_is_zero (%h)",
				expected_issue_A_is_zero, DUT_issue_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_bank !== DUT_issue_A_bank) begin
			$display("TB ERROR: expected_issue_A_bank (%h) != DUT_issue_A_bank (%h)",
				expected_issue_A_bank, DUT_issue_A_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_cq_index !== DUT_issue_cq_index) begin
			$display("TB ERROR: expected_issue_cq_index (%h) != DUT_issue_cq_index (%h)",
				expected_issue_cq_index, DUT_issue_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_req_A_valid !== DUT_PRF_req_A_valid) begin
			$display("TB ERROR: expected_PRF_req_A_valid (%h) != DUT_PRF_req_A_valid (%h)",
				expected_PRF_req_A_valid, DUT_PRF_req_A_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_req_A_PR !== DUT_PRF_req_A_PR) begin
			$display("TB ERROR: expected_PRF_req_A_PR (%h) != DUT_PRF_req_A_PR (%h)",
				expected_PRF_req_A_PR, DUT_PRF_req_A_PR);
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
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b0;
		tb_ldu_iq_enq_op = 4'b0000;
		tb_ldu_iq_enq_imm12 = 12'h0;
		tb_ldu_iq_enq_A_PR = 7'h0;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b0;
		tb_ldu_iq_enq_op = 4'b0000;
		tb_ldu_iq_enq_imm12 = 12'h0;
		tb_ldu_iq_enq_A_PR = 7'h0;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

        // ------------------------------------------------------------
        // sequence:
        test_case = "sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b0;
		tb_ldu_iq_enq_op = 4'b0000;
		tb_ldu_iq_enq_imm12 = 12'h0;
		tb_ldu_iq_enq_A_PR = 7'h0;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 0 zero",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0000;
		tb_ldu_iq_enq_imm12 = 12'h000;
		tb_ldu_iq_enq_A_PR = 7'h0;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b1;
		tb_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 1 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v 0 zero",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: v 0 zero"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0001;
		tb_ldu_iq_enq_imm12 = 12'h111;
		tb_ldu_iq_enq_A_PR = 7'h1;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 1;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b1;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 2 r",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v 1 n",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0010;
		tb_ldu_iq_enq_imm12 = 12'h222;
		tb_ldu_iq_enq_A_PR = 7'h2;
		tb_ldu_iq_enq_A_ready = 1'b1;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 2;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 3 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v 2 r",
			"\n\t\t\t", "0: v 1 nF",
			"\n\t\tWB bus: v 1",
			"\n\t\tIssue: v 1 nF"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0011;
		tb_ldu_iq_enq_imm12 = 12'h333;
		tb_ldu_iq_enq_A_PR = 7'h3;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 3;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0010;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0001;
		expected_issue_imm12 = 12'h111;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h1;
		expected_issue_cq_index = 1;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h1;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 4 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v 3 nR",
			"\n\t\t\t", "0: v 2 r",
			"\n\t\tWB bus: v 3",
			"\n\t\tIssue: i (pipeline not ready)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0100;
		tb_ldu_iq_enq_imm12 = 12'h444;
		tb_ldu_iq_enq_A_PR = 7'h4;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 4;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 5 r",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 4 n",
			"\n\t\t\t", "1: v 3 r",
			"\n\t\t\t", "0: v 2 r",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: i (pipeline not ready)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0101;
		tb_ldu_iq_enq_imm12 = 12'h555;
		tb_ldu_iq_enq_A_PR = 7'h5;
		tb_ldu_iq_enq_A_ready = 1'b1;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 5;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i 6 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v 5 r",
			"\n\t\t\t", "2: v 4 n",
			"\n\t\t\t", "1: v 3 r",
			"\n\t\t\t", "0: v 2 r",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: v 2 r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b0;
		tb_ldu_iq_enq_op = 4'b0110;
		tb_ldu_iq_enq_imm12 = 12'h666;
		tb_ldu_iq_enq_A_PR = 7'h6;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 6;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b0;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0010;
		expected_issue_imm12 = 12'h222;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h2;
		expected_issue_cq_index = 2;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h2;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 6 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 5 r",
			"\n\t\t\t", "1: v 4 n",
			"\n\t\t\t", "0: v 3 r",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: v 3 r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0110;
		tb_ldu_iq_enq_imm12 = 12'h666;
		tb_ldu_iq_enq_A_PR = 7'h6;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 6;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0011;
		expected_issue_imm12 = 12'h333;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h3;
		expected_issue_cq_index = 3;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h3;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 7 r",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 6 n",
			"\n\t\t\t", "1: v 5 r",
			"\n\t\t\t", "0: v 4 n",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: v 5 r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b0111;
		tb_ldu_iq_enq_imm12 = 12'h777;
		tb_ldu_iq_enq_A_PR = 7'h7;
		tb_ldu_iq_enq_A_ready = 1'b1;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 7;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0101;
		expected_issue_imm12 = 12'h555;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h1;
		expected_issue_cq_index = 5;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h5;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v 8 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 7 r",
			"\n\t\t\t", "1: v 6 nF",
			"\n\t\t\t", "0: v 4 n",
			"\n\t\tWB bus: v 6",
			"\n\t\tIssue: v 6 nF"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b1;
		tb_ldu_iq_enq_op = 4'b1000;
		tb_ldu_iq_enq_imm12 = 12'h888;
		tb_ldu_iq_enq_A_PR = 7'h8;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 8;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0100;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h1, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0110;
		expected_issue_imm12 = 12'h666;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h2;
		expected_issue_cq_index = 6;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h6;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i 9 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 8 n",
			"\n\t\t\t", "1: v 7 r",
			"\n\t\t\t", "0: v 4 n",
			"\n\t\tWB bus: i",
			"\n\t\tIssue: v 7 r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b0;
		tb_ldu_iq_enq_op = 4'b1001;
		tb_ldu_iq_enq_imm12 = 12'h999;
		tb_ldu_iq_enq_A_PR = 7'h9;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 9;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h1, 5'h0, 5'h0};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0111;
		expected_issue_imm12 = 12'h777;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h3;
		expected_issue_cq_index = 7;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h7;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i 9 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: in",
			"\n\t\t\t", "1: v 8 n",
			"\n\t\t\t", "0: v 4 nF",
			"\n\t\tWB bus: v 4",
			"\n\t\tIssue: v 4 nF"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_ldu_iq_enq_valid = 1'b0;
		tb_ldu_iq_enq_op = 4'b1001;
		tb_ldu_iq_enq_imm12 = 12'h999;
		tb_ldu_iq_enq_A_PR = 7'h9;
		tb_ldu_iq_enq_A_ready = 1'b0;
		tb_ldu_iq_enq_A_is_zero = 1'b0;
		tb_ldu_iq_enq_cq_index = 9;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0001;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h1, 5'h0, 5'h1};
	    // pipeline issue
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_ldu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0100;
		expected_issue_imm12 = 12'h444;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h4;
		expected_issue_cq_index = 4;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h4;
	    // pipeline feedback

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