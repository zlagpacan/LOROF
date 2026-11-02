/*
    Filename: alu_reg_mdu_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_reg_mdu_iq module.
    Spec: LOROF/spec/design/alu_reg_mdu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module alu_reg_mdu_iq_tb #(
	parameter ALU_REG_MDU_IQ_ENTRIES = 12,
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) ();

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

    // fast forward notifs
	logic [FAST_FORWARD_PIPE_COUNT-1:0] tb_fast_forward_notif_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0] tb_fast_forward_notif_PR_by_pipe;

    // ALU reg pipeline issue
	logic DUT_alu_reg_issue_valid, expected_alu_reg_issue_valid;

    // MDU pipeline issue
	logic DUT_mdu_issue_valid, expected_mdu_issue_valid;

    // shared issue info
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic DUT_issue_A_is_reg, expected_issue_A_is_reg;
	logic DUT_issue_A_is_bus_forward, expected_issue_A_is_bus_forward;
	logic DUT_issue_A_is_fast_forward, expected_issue_A_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] DUT_issue_A_fast_forward_pipe, expected_issue_A_fast_forward_pipe;
	logic [LOG_PR_COUNT-1:0] DUT_issue_A_PR, expected_issue_A_PR;
	logic DUT_issue_B_is_reg, expected_issue_B_is_reg;
	logic DUT_issue_B_is_bus_forward, expected_issue_B_is_bus_forward;
	logic DUT_issue_B_is_fast_forward, expected_issue_B_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] DUT_issue_B_fast_forward_pipe, expected_issue_B_fast_forward_pipe;
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
		.ALU_REG_MDU_IQ_ENTRIES(ALU_REG_MDU_IQ_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
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

	    // fast forward notifs
		.fast_forward_notif_valid_by_pipe(tb_fast_forward_notif_valid_by_pipe),
		.fast_forward_notif_PR_by_pipe(tb_fast_forward_notif_PR_by_pipe),

	    // ALU reg pipeline issue
		.alu_reg_issue_valid(DUT_alu_reg_issue_valid),

	    // MDU pipeline issue
		.mdu_issue_valid(DUT_mdu_issue_valid),

	    // shared issue info
		.issue_op(DUT_issue_op),
		.issue_A_is_reg(DUT_issue_A_is_reg),
		.issue_A_is_bus_forward(DUT_issue_A_is_bus_forward),
		.issue_A_is_fast_forward(DUT_issue_A_is_fast_forward),
		.issue_A_fast_forward_pipe(DUT_issue_A_fast_forward_pipe),
		.issue_A_PR(DUT_issue_A_PR),
		.issue_B_is_reg(DUT_issue_B_is_reg),
		.issue_B_is_bus_forward(DUT_issue_B_is_bus_forward),
		.issue_B_is_fast_forward(DUT_issue_B_is_fast_forward),
		.issue_B_fast_forward_pipe(DUT_issue_B_fast_forward_pipe),
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

		if (expected_issue_A_is_reg !== DUT_issue_A_is_reg) begin
			$display("TB ERROR: expected_issue_A_is_reg (%h) != DUT_issue_A_is_reg (%h)",
				expected_issue_A_is_reg, DUT_issue_A_is_reg);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_is_bus_forward !== DUT_issue_A_is_bus_forward) begin
			$display("TB ERROR: expected_issue_A_is_bus_forward (%h) != DUT_issue_A_is_bus_forward (%h)",
				expected_issue_A_is_bus_forward, DUT_issue_A_is_bus_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_is_fast_forward !== DUT_issue_A_is_fast_forward) begin
			$display("TB ERROR: expected_issue_A_is_fast_forward (%h) != DUT_issue_A_is_fast_forward (%h)",
				expected_issue_A_is_fast_forward, DUT_issue_A_is_fast_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_fast_forward_pipe !== DUT_issue_A_fast_forward_pipe) begin
			$display("TB ERROR: expected_issue_A_fast_forward_pipe (%h) != DUT_issue_A_fast_forward_pipe (%h)",
				expected_issue_A_fast_forward_pipe, DUT_issue_A_fast_forward_pipe);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_PR !== DUT_issue_A_PR) begin
			$display("TB ERROR: expected_issue_A_PR (%h) != DUT_issue_A_PR (%h)",
				expected_issue_A_PR, DUT_issue_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_is_reg !== DUT_issue_B_is_reg) begin
			$display("TB ERROR: expected_issue_B_is_reg (%h) != DUT_issue_B_is_reg (%h)",
				expected_issue_B_is_reg, DUT_issue_B_is_reg);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_is_bus_forward !== DUT_issue_B_is_bus_forward) begin
			$display("TB ERROR: expected_issue_B_is_bus_forward (%h) != DUT_issue_B_is_bus_forward (%h)",
				expected_issue_B_is_bus_forward, DUT_issue_B_is_bus_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_is_fast_forward !== DUT_issue_B_is_fast_forward) begin
			$display("TB ERROR: expected_issue_B_is_fast_forward (%h) != DUT_issue_B_is_fast_forward (%h)",
				expected_issue_B_is_fast_forward, DUT_issue_B_is_fast_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_fast_forward_pipe !== DUT_issue_B_fast_forward_pipe) begin
			$display("TB ERROR: expected_issue_B_fast_forward_pipe (%h) != DUT_issue_B_fast_forward_pipe (%h)",
				expected_issue_B_fast_forward_pipe, DUT_issue_B_fast_forward_pipe);
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
		tb_iq_enq_valid = '0;
		tb_iq_enq_is_alu_reg = '0;
		tb_iq_enq_is_mdu = '0;
		tb_iq_enq_op = '0;
		tb_iq_enq_A_PR = '0;
		tb_iq_enq_A_ready = '0;
		tb_iq_enq_A_is_zero = '0;
		tb_iq_enq_B_PR = '0;
		tb_iq_enq_B_ready = '0;
		tb_iq_enq_B_is_zero = '0;
		tb_iq_enq_dest_PR = '0;
		tb_iq_enq_ROB_index = '0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // fast forward notifs
		tb_fast_forward_notif_valid_by_pipe = '0;
		tb_fast_forward_notif_PR_by_pipe = '0;
	    // ALU reg pipeline issue
	    // MDU pipeline issue
	    // shared issue info
	    // ALU reg pipeline feedback
		tb_alu_reg_issue_ready = '0;
	    // MDU pipeline feedback
		tb_mdu_issue_ready = '0;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // ALU reg pipeline issue
		expected_alu_reg_issue_valid = '0;
	    // MDU pipeline issue
		expected_mdu_issue_valid = '0;
	    // shared issue info
		expected_issue_op = '0;
		expected_issue_A_is_reg = '0;
		expected_issue_A_is_bus_forward = '0;
		expected_issue_A_is_fast_forward = '0;
		expected_issue_A_fast_forward_pipe = '0;
		expected_issue_A_PR = '0;
		expected_issue_B_is_reg = '0;
		expected_issue_B_is_bus_forward = '0;
		expected_issue_B_is_fast_forward = '0;
		expected_issue_B_fast_forward_pipe = '0;
		expected_issue_B_PR = '0;
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
	    // ALU reg pipeline feedback
	    // MDU pipeline feedback
	    // reg read req to PRF
		expected_PRF_req_A_valid = '0;
		expected_PRF_req_A_PR = '0;
		expected_PRF_req_B_valid = '0;
		expected_PRF_req_B_PR = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op enqueue to issue queue
		tb_iq_enq_valid = '0;
		tb_iq_enq_is_alu_reg = '0;
		tb_iq_enq_is_mdu = '0;
		tb_iq_enq_op = '0;
		tb_iq_enq_A_PR = '0;
		tb_iq_enq_A_ready = '0;
		tb_iq_enq_A_is_zero = '0;
		tb_iq_enq_B_PR = '0;
		tb_iq_enq_B_ready = '0;
		tb_iq_enq_B_is_zero = '0;
		tb_iq_enq_dest_PR = '0;
		tb_iq_enq_ROB_index = '0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // fast forward notifs
		tb_fast_forward_notif_valid_by_pipe = '0;
		tb_fast_forward_notif_PR_by_pipe = '0;
	    // ALU reg pipeline issue
	    // MDU pipeline issue
	    // shared issue info
	    // ALU reg pipeline feedback
		tb_alu_reg_issue_ready = '0;
	    // MDU pipeline feedback
		tb_mdu_issue_ready = '0;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // ALU reg pipeline issue
		expected_alu_reg_issue_valid = '0;
	    // MDU pipeline issue
		expected_mdu_issue_valid = '0;
	    // shared issue info
		expected_issue_op = '0;
		expected_issue_A_is_reg = '0;
		expected_issue_A_is_bus_forward = '0;
		expected_issue_A_is_fast_forward = '0;
		expected_issue_A_fast_forward_pipe = '0;
		expected_issue_A_PR = '0;
		expected_issue_B_is_reg = '0;
		expected_issue_B_is_bus_forward = '0;
		expected_issue_B_is_fast_forward = '0;
		expected_issue_B_fast_forward_pipe = '0;
		expected_issue_B_PR = '0;
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
	    // ALU reg pipeline feedback
	    // MDU pipeline feedback
	    // reg read req to PRF
		expected_PRF_req_A_valid = '0;
		expected_PRF_req_A_PR = '0;
		expected_PRF_req_B_valid = '0;
		expected_PRF_req_B_PR = '0;

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
		tb_iq_enq_valid = '0;
		tb_iq_enq_is_alu_reg = '0;
		tb_iq_enq_is_mdu = '0;
		tb_iq_enq_op = '0;
		tb_iq_enq_A_PR = '0;
		tb_iq_enq_A_ready = '0;
		tb_iq_enq_A_is_zero = '0;
		tb_iq_enq_B_PR = '0;
		tb_iq_enq_B_ready = '0;
		tb_iq_enq_B_is_zero = '0;
		tb_iq_enq_dest_PR = '0;
		tb_iq_enq_ROB_index = '0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // fast forward notifs
		tb_fast_forward_notif_valid_by_pipe = '0;
		tb_fast_forward_notif_PR_by_pipe = '0;
	    // ALU reg pipeline issue
	    // MDU pipeline issue
	    // shared issue info
	    // ALU reg pipeline feedback
		tb_alu_reg_issue_ready = '0;
	    // MDU pipeline feedback
		tb_mdu_issue_ready = '0;
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // ALU reg pipeline issue
		expected_alu_reg_issue_valid = '0;
	    // MDU pipeline issue
		expected_mdu_issue_valid = '0;
	    // shared issue info
		expected_issue_op = '0;
		expected_issue_A_is_reg = '0;
		expected_issue_A_is_bus_forward = '0;
		expected_issue_A_is_fast_forward = '0;
		expected_issue_A_fast_forward_pipe = '0;
		expected_issue_A_PR = '0;
		expected_issue_B_is_reg = '0;
		expected_issue_B_is_bus_forward = '0;
		expected_issue_B_is_fast_forward = '0;
		expected_issue_B_fast_forward_pipe = '0;
		expected_issue_B_PR = '0;
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
	    // ALU reg pipeline feedback
	    // MDU pipeline feedback
	    // reg read req to PRF
		expected_PRF_req_A_valid = '0;
		expected_PRF_req_A_PR = '0;
		expected_PRF_req_B_valid = '0;
		expected_PRF_req_B_PR = '0;

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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule
