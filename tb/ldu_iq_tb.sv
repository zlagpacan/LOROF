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
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "default";
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