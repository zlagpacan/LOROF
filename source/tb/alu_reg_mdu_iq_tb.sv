/*
    Filename: alu_reg_mdu_iq.sv
    Author: zlagpacan
    Description: Testbench for alu_reg_mdu_iq module. 
    Spec: LOROF/spec/design/alu_reg_mdu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module alu_reg_mdu_iq_tb ();

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
	logic tb_iq_enq_valid;
	logic tb_iq_enq_is_alu_reg;
	logic tb_iq_enq_is_mdu;
	logic [3:0] tb_iq_enq_op;
	logic [LOG_PR_COUNT-1:0] tb_iq_enq_A_PR;
	logic tb_iq_enq_A_ready;
	logic tb_iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] tb_iq_enq_B_PR;
	logic tb_iq_enq_B_ready;
	logic tb_iq_enq_B_is_zero;
	logic [LOG_PR_COUNT-1:0] tb_iq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_iq_enq_ROB_index;

    // issue queue enqueue feedback
	logic DUT_iq_enq_ready, expected_iq_enq_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // ALU reg pipeline issue
	logic DUT_alu_reg_issue_valid, expected_alu_reg_issue_valid;

    // MDU pipeline issue
	logic DUT_mdu_issue_valid, expected_mdu_issue_valid;

    // shared issue info
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic DUT_issue_A_forward, expected_issue_A_forward;
	logic DUT_issue_A_is_zero, expected_issue_A_is_zero;
	logic [LOG_PR_COUNT-1:0] DUT_issue_A_PR, expected_issue_A_PR;
	logic DUT_issue_B_forward, expected_issue_B_forward;
	logic DUT_issue_B_is_zero, expected_issue_B_is_zero;
	logic [LOG_PR_COUNT-1:0] DUT_issue_B_PR, expected_issue_B_PR;
	logic [LOG_PR_COUNT-1:0] DUT_issue_dest_PR, expected_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_ROB_index, expected_issue_ROB_index;

    // ALU reg pipeline feedback
	logic tb_alu_reg_issue_ready;

    // MDU pipeline feedback
	logic tb_mdu_issue_ready;

    // reg read req to PRF
	logic DUT_PRF_req_A_valid, expected_PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_A_PR, expected_PRF_req_A_PR;
	logic DUT_PRF_req_B_valid, expected_PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_B_PR, expected_PRF_req_B_PR;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_reg_mdu_iq #(
		.ALU_REG_MDU_IQ_ENTRIES(8)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to issue queue
		.iq_enq_valid(tb_iq_enq_valid),
		.iq_enq_is_alu_reg(tb_iq_enq_is_alu_reg),
		.iq_enq_is_mdu(tb_iq_enq_is_mdu),
		.iq_enq_op(tb_iq_enq_op),
		.iq_enq_A_PR(tb_iq_enq_A_PR),
		.iq_enq_A_ready(tb_iq_enq_A_ready),
		.iq_enq_A_is_zero(tb_iq_enq_A_is_zero),
		.iq_enq_B_PR(tb_iq_enq_B_PR),
		.iq_enq_B_ready(tb_iq_enq_B_ready),
		.iq_enq_B_is_zero(tb_iq_enq_B_is_zero),
		.iq_enq_dest_PR(tb_iq_enq_dest_PR),
		.iq_enq_ROB_index(tb_iq_enq_ROB_index),

	    // issue queue enqueue feedback
		.iq_enq_ready(DUT_iq_enq_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // ALU reg pipeline issue
		.alu_reg_issue_valid(DUT_alu_reg_issue_valid),

	    // MDU pipeline issue
		.mdu_issue_valid(DUT_mdu_issue_valid),

	    // shared issue info
		.issue_op(DUT_issue_op),
		.issue_A_forward(DUT_issue_A_forward),
		.issue_A_is_zero(DUT_issue_A_is_zero),
		.issue_A_PR(DUT_issue_A_PR),
		.issue_B_forward(DUT_issue_B_forward),
		.issue_B_is_zero(DUT_issue_B_is_zero),
		.issue_B_PR(DUT_issue_B_PR),
		.issue_dest_PR(DUT_issue_dest_PR),
		.issue_ROB_index(DUT_issue_ROB_index),

	    // ALU reg pipeline feedback
		.alu_reg_issue_ready(tb_alu_reg_issue_ready),

	    // MDU pipeline feedback
		.mdu_issue_ready(tb_mdu_issue_ready),

	    // reg read req to PRF
		.PRF_req_A_valid(DUT_PRF_req_A_valid),
		.PRF_req_A_PR(DUT_PRF_req_A_PR),
		.PRF_req_B_valid(DUT_PRF_req_B_valid),
		.PRF_req_B_PR(DUT_PRF_req_B_PR)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_iq_enq_ready !== DUT_iq_enq_ready) begin
			$display("TB ERROR: expected_iq_enq_ready (%h) != DUT_iq_enq_ready (%h)",
				expected_iq_enq_ready, DUT_iq_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_alu_reg_issue_valid !== DUT_alu_reg_issue_valid) begin
			$display("TB ERROR: expected_alu_reg_issue_valid (%h) != DUT_alu_reg_issue_valid (%h)",
				expected_alu_reg_issue_valid, DUT_alu_reg_issue_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_mdu_issue_valid !== DUT_mdu_issue_valid) begin
			$display("TB ERROR: expected_mdu_issue_valid (%h) != DUT_mdu_issue_valid (%h)",
				expected_mdu_issue_valid, DUT_mdu_issue_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_op !== DUT_issue_op) begin
			$display("TB ERROR: expected_issue_op (%h) != DUT_issue_op (%h)",
				expected_issue_op, DUT_issue_op);
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

		if (expected_issue_A_PR !== DUT_issue_A_PR) begin
			$display("TB ERROR: expected_issue_A_PR (%h) != DUT_issue_A_PR (%h)",
				expected_issue_A_PR, DUT_issue_A_PR);
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

		if (expected_issue_B_PR !== DUT_issue_B_PR) begin
			$display("TB ERROR: expected_issue_B_PR (%h) != DUT_issue_B_PR (%h)",
				expected_issue_B_PR, DUT_issue_B_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_dest_PR !== DUT_issue_dest_PR) begin
			$display("TB ERROR: expected_issue_dest_PR (%h) != DUT_issue_dest_PR (%h)",
				expected_issue_dest_PR, DUT_issue_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ROB_index !== DUT_issue_ROB_index) begin
			$display("TB ERROR: expected_issue_ROB_index (%h) != DUT_issue_ROB_index (%h)",
				expected_issue_ROB_index, DUT_issue_ROB_index);
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
		tb_iq_enq_valid = 1'b0;
		tb_iq_enq_is_alu_reg = 1'b0;
		tb_iq_enq_is_mdu = 1'b0;
		tb_iq_enq_op = 4'b0000;
		tb_iq_enq_A_PR = 7'h0;
		tb_iq_enq_A_ready = 1'b0;
		tb_iq_enq_A_is_zero = 1'b0;
		tb_iq_enq_B_PR = 7'h0;
		tb_iq_enq_B_ready = 1'b0;
		tb_iq_enq_B_is_zero = 1'b0;
		tb_iq_enq_dest_PR = 7'h0;
		tb_iq_enq_ROB_index = 7'h0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU reg pipeline issue
	    // MDU pipeline issue
	    // shared issue info
	    // ALU reg pipeline feedback
		tb_alu_reg_issue_ready = 1'b1;
	    // MDU pipeline feedback
		tb_mdu_issue_ready = 1'b1;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // ALU reg pipeline issue
		expected_alu_reg_issue_valid = 1'b0;
	    // MDU pipeline issue
		expected_mdu_issue_valid = 1'b0;
	    // shared issue info
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_PR = 7'h00;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_PR = 7'h00;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // ALU reg pipeline feedback
	    // MDU pipeline feedback
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_iq_enq_valid = 1'b0;
		tb_iq_enq_is_alu_reg = 1'b0;
		tb_iq_enq_is_mdu = 1'b0;
		tb_iq_enq_op = 4'b0000;
		tb_iq_enq_A_PR = 7'h0;
		tb_iq_enq_A_ready = 1'b0;
		tb_iq_enq_A_is_zero = 1'b0;
		tb_iq_enq_B_PR = 7'h0;
		tb_iq_enq_B_ready = 1'b0;
		tb_iq_enq_B_is_zero = 1'b0;
		tb_iq_enq_dest_PR = 7'h0;
		tb_iq_enq_ROB_index = 7'h0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU reg pipeline issue
	    // MDU pipeline issue
	    // shared issue info
	    // ALU reg pipeline feedback
		tb_alu_reg_issue_ready = 1'b1;
	    // MDU pipeline feedback
		tb_mdu_issue_ready = 1'b1;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // ALU reg pipeline issue
		expected_alu_reg_issue_valid = 1'b0;
	    // MDU pipeline issue
		expected_mdu_issue_valid = 1'b0;
	    // shared issue info
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_PR = 7'h00;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_PR = 7'h00;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // ALU reg pipeline feedback
	    // MDU pipeline feedback
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

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
		tb_iq_enq_valid = 1'b0;
		tb_iq_enq_is_alu_reg = 1'b0;
		tb_iq_enq_is_mdu = 1'b0;
		tb_iq_enq_op = 4'b0000;
		tb_iq_enq_A_PR = 7'h0;
		tb_iq_enq_A_ready = 1'b0;
		tb_iq_enq_A_is_zero = 1'b0;
		tb_iq_enq_B_PR = 7'h0;
		tb_iq_enq_B_ready = 1'b0;
		tb_iq_enq_B_is_zero = 1'b0;
		tb_iq_enq_dest_PR = 7'h0;
		tb_iq_enq_ROB_index = 7'h0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU reg pipeline issue
	    // MDU pipeline issue
	    // shared issue info
	    // ALU reg pipeline feedback
		tb_alu_reg_issue_ready = 1'b1;
	    // MDU pipeline feedback
		tb_mdu_issue_ready = 1'b1;
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // ALU reg pipeline issue
		expected_alu_reg_issue_valid = 1'b0;
	    // MDU pipeline issue
		expected_mdu_issue_valid = 1'b0;
	    // shared issue info
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_is_zero = 1'b0;
		expected_issue_A_PR = 7'h00;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_is_zero = 1'b0;
		expected_issue_B_PR = 7'h00;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // ALU reg pipeline feedback
	    // MDU pipeline feedback
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

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