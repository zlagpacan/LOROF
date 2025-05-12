/*
    Filename: stamofu_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_iq module. 
    Spec: LOROF/spec/design/stamofu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stamofu_iq_tb ();

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
	logic tb_stamofu_iq_enq_valid;
	logic tb_stamofu_iq_enq_is_store;
	logic tb_stamofu_iq_enq_is_amo;
	logic tb_stamofu_iq_enq_is_fence;
	logic [3:0] tb_stamofu_iq_enq_op;
	logic [11:0] tb_stamofu_iq_enq_imm12;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_iq_enq_mdp_info;
	logic tb_stamofu_iq_enq_mem_aq;
	logic tb_stamofu_iq_enq_io_aq;
	logic [LOG_PR_COUNT-1:0] tb_stamofu_iq_enq_A_PR;
	logic tb_stamofu_iq_enq_A_ready;
	logic tb_stamofu_iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] tb_stamofu_iq_enq_B_PR;
	logic tb_stamofu_iq_enq_B_ready;
	logic tb_stamofu_iq_enq_B_is_zero;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_iq_enq_ROB_index;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic DUT_stamofu_iq_enq_ready, expected_stamofu_iq_enq_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // pipeline issue 
	logic DUT_issue_valid, expected_issue_valid;
	logic DUT_issue_is_store, expected_issue_is_store;
	logic DUT_issue_is_amo, expected_issue_is_amo;
	logic DUT_issue_is_fence, expected_issue_is_fence;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic [11:0] DUT_issue_imm12, expected_issue_imm12;
	logic [MDPT_INFO_WIDTH-1:0] DUT_issue_mdp_info, expected_issue_mdp_info;
	logic DUT_issue_mem_aq, expected_issue_mem_aq;
	logic DUT_issue_io_aq, expected_issue_io_aq;
	logic DUT_issue_A_forward, expected_issue_A_forward;
	logic DUT_issue_A_is_zero, expected_issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_A_bank, expected_issue_A_bank;
	logic DUT_issue_B_forward, expected_issue_B_forward;
	logic DUT_issue_B_is_zero, expected_issue_B_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_B_bank, expected_issue_B_bank;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_ROB_index, expected_issue_ROB_index;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_issue_cq_index, expected_issue_cq_index;

    // reg read req to PRF
	logic DUT_PRF_req_A_valid, expected_PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_A_PR, expected_PRF_req_A_PR;
	logic DUT_PRF_req_B_valid, expected_PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_B_PR, expected_PRF_req_B_PR;

    // pipeline feedback
	logic tb_pipeline_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_iq #(
		.STAMOFU_IQ_ENTRIES(4)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to issue queue
		.stamofu_iq_enq_valid(tb_stamofu_iq_enq_valid),
		.stamofu_iq_enq_is_store(tb_stamofu_iq_enq_is_store),
		.stamofu_iq_enq_is_amo(tb_stamofu_iq_enq_is_amo),
		.stamofu_iq_enq_is_fence(tb_stamofu_iq_enq_is_fence),
		.stamofu_iq_enq_op(tb_stamofu_iq_enq_op),
		.stamofu_iq_enq_imm12(tb_stamofu_iq_enq_imm12),
		.stamofu_iq_enq_mdp_info(tb_stamofu_iq_enq_mdp_info),
		.stamofu_iq_enq_mem_aq(tb_stamofu_iq_enq_mem_aq),
		.stamofu_iq_enq_io_aq(tb_stamofu_iq_enq_io_aq),
		.stamofu_iq_enq_A_PR(tb_stamofu_iq_enq_A_PR),
		.stamofu_iq_enq_A_ready(tb_stamofu_iq_enq_A_ready),
		.stamofu_iq_enq_A_is_zero(tb_stamofu_iq_enq_A_is_zero),
		.stamofu_iq_enq_B_PR(tb_stamofu_iq_enq_B_PR),
		.stamofu_iq_enq_B_ready(tb_stamofu_iq_enq_B_ready),
		.stamofu_iq_enq_B_is_zero(tb_stamofu_iq_enq_B_is_zero),
		.stamofu_iq_enq_ROB_index(tb_stamofu_iq_enq_ROB_index),
		.stamofu_iq_enq_cq_index(tb_stamofu_iq_enq_cq_index),

	    // issue queue enqueue feedback
		.stamofu_iq_enq_ready(DUT_stamofu_iq_enq_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // pipeline issue 
		.issue_valid(DUT_issue_valid),
		.issue_is_store(DUT_issue_is_store),
		.issue_is_amo(DUT_issue_is_amo),
		.issue_is_fence(DUT_issue_is_fence),
		.issue_op(DUT_issue_op),
		.issue_imm12(DUT_issue_imm12),
		.issue_mdp_info(DUT_issue_mdp_info),
		.issue_mem_aq(DUT_issue_mem_aq),
		.issue_io_aq(DUT_issue_io_aq),
		.issue_A_forward(DUT_issue_A_forward),
		.issue_A_is_zero(DUT_issue_A_is_zero),
		.issue_A_bank(DUT_issue_A_bank),
		.issue_B_forward(DUT_issue_B_forward),
		.issue_B_is_zero(DUT_issue_B_is_zero),
		.issue_B_bank(DUT_issue_B_bank),
		.issue_ROB_index(DUT_issue_ROB_index),
		.issue_cq_index(DUT_issue_cq_index),

	    // reg read req to PRF
		.PRF_req_A_valid(DUT_PRF_req_A_valid),
		.PRF_req_A_PR(DUT_PRF_req_A_PR),
		.PRF_req_B_valid(DUT_PRF_req_B_valid),
		.PRF_req_B_PR(DUT_PRF_req_B_PR),

	    // pipeline feedback
		.pipeline_ready(tb_pipeline_ready)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_stamofu_iq_enq_ready !== DUT_stamofu_iq_enq_ready) begin
			$display("TB ERROR: expected_stamofu_iq_enq_ready (%h) != DUT_stamofu_iq_enq_ready (%h)",
				expected_stamofu_iq_enq_ready, DUT_stamofu_iq_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_valid !== DUT_issue_valid) begin
			$display("TB ERROR: expected_issue_valid (%h) != DUT_issue_valid (%h)",
				expected_issue_valid, DUT_issue_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_is_store !== DUT_issue_is_store) begin
			$display("TB ERROR: expected_issue_is_store (%h) != DUT_issue_is_store (%h)",
				expected_issue_is_store, DUT_issue_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_is_amo !== DUT_issue_is_amo) begin
			$display("TB ERROR: expected_issue_is_amo (%h) != DUT_issue_is_amo (%h)",
				expected_issue_is_amo, DUT_issue_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_is_fence !== DUT_issue_is_fence) begin
			$display("TB ERROR: expected_issue_is_fence (%h) != DUT_issue_is_fence (%h)",
				expected_issue_is_fence, DUT_issue_is_fence);
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

		if (expected_issue_mdp_info !== DUT_issue_mdp_info) begin
			$display("TB ERROR: expected_issue_mdp_info (%h) != DUT_issue_mdp_info (%h)",
				expected_issue_mdp_info, DUT_issue_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mem_aq !== DUT_issue_mem_aq) begin
			$display("TB ERROR: expected_issue_mem_aq (%h) != DUT_issue_mem_aq (%h)",
				expected_issue_mem_aq, DUT_issue_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_io_aq !== DUT_issue_io_aq) begin
			$display("TB ERROR: expected_issue_io_aq (%h) != DUT_issue_io_aq (%h)",
				expected_issue_io_aq, DUT_issue_io_aq);
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

		if (expected_issue_B_forward !== DUT_issue_B_forward) begin
			$display("TB ERROR: expected_issue_B_forward (%h) != DUT_issue_B_forward (%h)",
				expected_issue_B_forward, DUT_issue_B_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_is_zero !== DUT_issue_B_is_zero) begin
			$display("TB ERROR: expected_issue_B_is_zero (%h) != DUT_issue_B_is_zero (%h)",
				expected_issue_B_is_zero, DUT_issue_B_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_bank !== DUT_issue_B_bank) begin
			$display("TB ERROR: expected_issue_B_bank (%h) != DUT_issue_B_bank (%h)",
				expected_issue_B_bank, DUT_issue_B_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ROB_index !== DUT_issue_ROB_index) begin
			$display("TB ERROR: expected_issue_ROB_index (%h) != DUT_issue_ROB_index (%h)",
				expected_issue_ROB_index, DUT_issue_ROB_index);
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

		if (expected_PRF_req_B_valid !== DUT_PRF_req_B_valid) begin
			$display("TB ERROR: expected_PRF_req_B_valid (%h) != DUT_PRF_req_B_valid (%h)",
				expected_PRF_req_B_valid, DUT_PRF_req_B_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_req_B_PR !== DUT_PRF_req_B_PR) begin
			$display("TB ERROR: expected_PRF_req_B_PR (%h) != DUT_PRF_req_B_PR (%h)",
				expected_PRF_req_B_PR, DUT_PRF_req_B_PR);
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
		tb_stamofu_iq_enq_valid = 1'b0;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h0;
		tb_stamofu_iq_enq_mdp_info = 8'h0;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h0;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h0;
		tb_stamofu_iq_enq_cq_index = 0;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_mdp_info = 8'h0;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b0;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h0;
		tb_stamofu_iq_enq_mdp_info = 8'h0;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h0;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h0;
		tb_stamofu_iq_enq_cq_index = 0;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_mdp_info = 8'h0;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;
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
			"\n\t\tWB bus: ",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b0;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h0;
		tb_stamofu_iq_enq_mdp_info = 8'h0;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h0;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h0;
		tb_stamofu_iq_enq_cq_index = 0;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_mdp_info = 8'h0;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v s 0 z,z",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tWB bus: ",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b1;
		tb_stamofu_iq_enq_is_store = 1'b1;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h000;
		tb_stamofu_iq_enq_mdp_info = 8'h00;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b1;
		tb_stamofu_iq_enq_B_PR = 7'h00;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b1;
		tb_stamofu_iq_enq_ROB_index = 7'h00;
		tb_stamofu_iq_enq_cq_index = 0;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_mdp_info = 8'h0;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v a 1 n,r",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v s 0 z,z (pipeline not ready)",
			"\n\t\tWB bus: ",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b1;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b1;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0001;
		tb_stamofu_iq_enq_imm12 = 12'h111;
		tb_stamofu_iq_enq_mdp_info = 8'h11;
		tb_stamofu_iq_enq_mem_aq = 1'b1;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h1;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h11;
		tb_stamofu_iq_enq_B_ready = 1'b1;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h11;
		tb_stamofu_iq_enq_cq_index = 1;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h0;
		expected_issue_mdp_info = 8'h0;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h0;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v f 2 n,n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v a 1 nF,r",
			"\n\t\t\t", "0: v s 0 z,z",
			"\n\t\tWB bus: 1",
			"\n\t\tIssue: v s 0 z,z"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b1;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b1;
		tb_stamofu_iq_enq_op = 4'b0010;
		tb_stamofu_iq_enq_imm12 = 12'h222;
		tb_stamofu_iq_enq_mdp_info = 8'h22;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b1;
		tb_stamofu_iq_enq_A_PR = 7'h2;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h22;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h22;
		tb_stamofu_iq_enq_cq_index = 2;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b1;
		expected_issue_is_store = 1'b1;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h000;
		expected_issue_mdp_info = 8'h00;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b1;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b1;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h00;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h00;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v s 3 r,n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v f 2 n,nR",
			"\n\t\t\t", "0: v a 1 r,r",
			"\n\t\tWB bus: 22",
			"\n\t\tIssue: i (pipeline not ready)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b1;
		tb_stamofu_iq_enq_is_store = 1'b1;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0011;
		tb_stamofu_iq_enq_imm12 = 12'h333;
		tb_stamofu_iq_enq_mdp_info = 8'h33;
		tb_stamofu_iq_enq_mem_aq = 1'b1;
		tb_stamofu_iq_enq_io_aq = 1'b1;
		tb_stamofu_iq_enq_A_PR = 7'h3;
		tb_stamofu_iq_enq_A_ready = 1'b1;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h33;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h33;
		tb_stamofu_iq_enq_cq_index = 3;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0100;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h8, 5'h0, 5'h0};
	    // pipeline issue 
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h000;
		expected_issue_mdp_info = 8'h00;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h00;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h00;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v a 4 r,r",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v s 3 r,n",
			"\n\t\t\t", "1: v f 2 n,r",
			"\n\t\t\t", "0: v a 1 r,r",
			"\n\t\tWB bus: ",
			"\n\t\tIssue: i (pipeline not ready)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b1;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b1;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0100;
		tb_stamofu_iq_enq_imm12 = 12'h444;
		tb_stamofu_iq_enq_mdp_info = 8'h44;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h4;
		tb_stamofu_iq_enq_A_ready = 1'b1;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h44;
		tb_stamofu_iq_enq_B_ready = 1'b1;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h44;
		tb_stamofu_iq_enq_cq_index = 4;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h000;
		expected_issue_mdp_info = 8'h00;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h00;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h00;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v f 5 n,n (fail)",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v a 4 r,r",
			"\n\t\t\t", "2: v s 3 r,n",
			"\n\t\t\t", "1: v f 2 n,r",
			"\n\t\t\t", "0: v a 1 r,r",
			"\n\t\tWB bus: ",
			"\n\t\tIssue: v a 1 r,r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b1;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b1;
		tb_stamofu_iq_enq_op = 4'b0101;
		tb_stamofu_iq_enq_imm12 = 12'h555;
		tb_stamofu_iq_enq_mdp_info = 8'h55;
		tb_stamofu_iq_enq_mem_aq = 1'b1;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h5;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h55;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h55;
		tb_stamofu_iq_enq_cq_index = 5;
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
		expected_stamofu_iq_enq_ready = 1'b0;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b1;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b1;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0001;
		expected_issue_imm12 = 12'h111;
		expected_issue_mdp_info = 8'h11;
		expected_issue_mem_aq = 1'b1;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h1;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h1;
		expected_issue_ROB_index = 7'h11;
		expected_issue_cq_index = 1;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h1;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h11;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: v f 5 n,n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v a 4 r,r",
			"\n\t\t\t", "1: v s 3 r,n",
			"\n\t\t\t", "0: v f 2 n,r",
			"\n\t\tWB bus: ",
			"\n\t\tIssue: v a 4 r,r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b1;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b1;
		tb_stamofu_iq_enq_op = 4'b0101;
		tb_stamofu_iq_enq_imm12 = 12'h555;
		tb_stamofu_iq_enq_mdp_info = 8'h55;
		tb_stamofu_iq_enq_mem_aq = 1'b1;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h5;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h55;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h55;
		tb_stamofu_iq_enq_cq_index = 5;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b1;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b1;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0100;
		expected_issue_imm12 = 12'h444;
		expected_issue_mdp_info = 8'h44;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h44;
		expected_issue_cq_index = 4;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h4;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h44;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 5 n,n",
			"\n\t\t\t", "1: v s 3 r,nR",
			"\n\t\t\t", "0: v f 2 nF,r",
			"\n\t\tWB bus: 2, 33",
			"\n\t\tIssue: v f 2 nF,r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b0;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h000;
		tb_stamofu_iq_enq_mdp_info = 8'h00;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h00;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h00;
		tb_stamofu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1100;
		tb_WB_bus_upper_PR_by_bank = {5'hC, 5'h0, 5'h0, 5'h0};
	    // pipeline issue 
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b1;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b1;
		expected_issue_op = 4'b0010;
		expected_issue_imm12 = 12'h222;
		expected_issue_mdp_info = 8'h22;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b1;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h2;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h2;
		expected_issue_ROB_index = 7'h22;
		expected_issue_cq_index = 2;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h2;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h22;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v f 5 nR,n",
			"\n\t\t\t", "0: v s 3 r,r",
			"\n\t\tWB bus: 5",
			"\n\t\tIssue: v s 3 r,r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b0;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h000;
		tb_stamofu_iq_enq_mdp_info = 8'h00;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h00;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h00;
		tb_stamofu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0010;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h1, 5'h0};
	    // pipeline issue 
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b1;
		expected_issue_is_store = 1'b1;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0011;
		expected_issue_imm12 = 12'h333;
		expected_issue_mdp_info = 8'h33;
		expected_issue_mem_aq = 1'b1;
		expected_issue_io_aq = 1'b1;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h3;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h3;
		expected_issue_ROB_index = 7'h33;
		expected_issue_cq_index = 3;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h3;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h33;
	    // pipeline feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tEnqueue: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v f 5 r,nF",
			"\n\t\tWB bus: 55",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b0;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h000;
		tb_stamofu_iq_enq_mdp_info = 8'h00;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h00;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h00;
		tb_stamofu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0010;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h15, 5'h0};
	    // pipeline issue 
	    // reg read req to PRF
	    // pipeline feedback
		tb_pipeline_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b1;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b1;
		expected_issue_op = 4'b0101;
		expected_issue_imm12 = 12'h555;
		expected_issue_mdp_info = 8'h55;
		expected_issue_mem_aq = 1'b1;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h1;
		expected_issue_B_forward = 1'b1;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h1;
		expected_issue_ROB_index = 7'h55;
		expected_issue_cq_index = 5;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h5;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h55;
	    // pipeline feedback

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
			"\n\t\tWB bus: ",
			"\n\t\tIssue: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_stamofu_iq_enq_valid = 1'b0;
		tb_stamofu_iq_enq_is_store = 1'b0;
		tb_stamofu_iq_enq_is_amo = 1'b0;
		tb_stamofu_iq_enq_is_fence = 1'b0;
		tb_stamofu_iq_enq_op = 4'b0000;
		tb_stamofu_iq_enq_imm12 = 12'h000;
		tb_stamofu_iq_enq_mdp_info = 8'h00;
		tb_stamofu_iq_enq_mem_aq = 1'b0;
		tb_stamofu_iq_enq_io_aq = 1'b0;
		tb_stamofu_iq_enq_A_PR = 7'h0;
		tb_stamofu_iq_enq_A_ready = 1'b0;
		tb_stamofu_iq_enq_A_is_zero = 1'b0;
		tb_stamofu_iq_enq_B_PR = 7'h00;
		tb_stamofu_iq_enq_B_ready = 1'b0;
		tb_stamofu_iq_enq_B_is_zero = 1'b0;
		tb_stamofu_iq_enq_ROB_index = 7'h00;
		tb_stamofu_iq_enq_cq_index = 0;
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
		expected_stamofu_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // pipeline issue 
		expected_issue_valid = 1'b0;
		expected_issue_is_store = 1'b0;
		expected_issue_is_amo = 1'b0;
		expected_issue_is_fence = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_imm12 = 12'h000;
		expected_issue_mdp_info = 8'h00;
		expected_issue_mem_aq = 1'b0;
		expected_issue_io_aq = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_ROB_index = 7'h00;
		expected_issue_cq_index = 0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;
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