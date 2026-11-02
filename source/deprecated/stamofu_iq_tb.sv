/*
    Filename: stamofu_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_iq module. 
    Spec: LOROF/spec/design/stamofu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_iq_tb #(
	parameter STAMOFU_IQ_ENTRIES = 8,
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
	logic tb_stamofu_iq_enq_valid;
	logic tb_stamofu_iq_enq_is_store;
	logic tb_stamofu_iq_enq_is_amo;
	logic tb_stamofu_iq_enq_is_fence;
	logic [3:0] tb_stamofu_iq_enq_op;
	logic [11:0] tb_stamofu_iq_enq_imm12;
	logic [LOG_PR_COUNT-1:0] tb_stamofu_iq_enq_A_PR;
	logic tb_stamofu_iq_enq_A_ready;
	logic tb_stamofu_iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] tb_stamofu_iq_enq_B_PR;
	logic tb_stamofu_iq_enq_B_ready;
	logic tb_stamofu_iq_enq_B_is_zero;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic DUT_stamofu_iq_enq_ready, expected_stamofu_iq_enq_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // fast forward notifs
	logic [FAST_FORWARD_PIPE_COUNT-1:0] tb_fast_forward_notif_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0] tb_fast_forward_notif_PR_by_pipe;

    // pipeline issue 
	logic DUT_issue_valid, expected_issue_valid;
	logic DUT_issue_is_store, expected_issue_is_store;
	logic DUT_issue_is_amo, expected_issue_is_amo;
	logic DUT_issue_is_fence, expected_issue_is_fence;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic [11:0] DUT_issue_imm12, expected_issue_imm12;
	logic DUT_issue_A_is_reg, expected_issue_A_is_reg;
	logic DUT_issue_A_is_bus_forward, expected_issue_A_is_bus_forward;
	logic DUT_issue_A_is_fast_forward, expected_issue_A_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] DUT_issue_A_fast_forward_pipe, expected_issue_A_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_A_bank, expected_issue_A_bank;
	logic DUT_issue_B_is_reg, expected_issue_B_is_reg;
	logic DUT_issue_B_is_bus_forward, expected_issue_B_is_bus_forward;
	logic DUT_issue_B_is_fast_forward, expected_issue_B_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] DUT_issue_B_fast_forward_pipe, expected_issue_B_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_B_bank, expected_issue_B_bank;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_issue_cq_index, expected_issue_cq_index;

    // pipeline feedback
	logic tb_issue_ready;

    // reg read req to PRF
	logic DUT_PRF_req_A_valid, expected_PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_A_PR, expected_PRF_req_A_PR;
	logic DUT_PRF_req_B_valid, expected_PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_B_PR, expected_PRF_req_B_PR;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_iq #(
		.STAMOFU_IQ_ENTRIES(STAMOFU_IQ_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
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
		.stamofu_iq_enq_A_PR(tb_stamofu_iq_enq_A_PR),
		.stamofu_iq_enq_A_ready(tb_stamofu_iq_enq_A_ready),
		.stamofu_iq_enq_A_is_zero(tb_stamofu_iq_enq_A_is_zero),
		.stamofu_iq_enq_B_PR(tb_stamofu_iq_enq_B_PR),
		.stamofu_iq_enq_B_ready(tb_stamofu_iq_enq_B_ready),
		.stamofu_iq_enq_B_is_zero(tb_stamofu_iq_enq_B_is_zero),
		.stamofu_iq_enq_cq_index(tb_stamofu_iq_enq_cq_index),

	    // issue queue enqueue feedback
		.stamofu_iq_enq_ready(DUT_stamofu_iq_enq_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // fast forward notifs
		.fast_forward_notif_valid_by_pipe(tb_fast_forward_notif_valid_by_pipe),
		.fast_forward_notif_PR_by_pipe(tb_fast_forward_notif_PR_by_pipe),

	    // pipeline issue 
		.issue_valid(DUT_issue_valid),
		.issue_is_store(DUT_issue_is_store),
		.issue_is_amo(DUT_issue_is_amo),
		.issue_is_fence(DUT_issue_is_fence),
		.issue_op(DUT_issue_op),
		.issue_imm12(DUT_issue_imm12),
		.issue_A_is_reg(DUT_issue_A_is_reg),
		.issue_A_is_bus_forward(DUT_issue_A_is_bus_forward),
		.issue_A_is_fast_forward(DUT_issue_A_is_fast_forward),
		.issue_A_fast_forward_pipe(DUT_issue_A_fast_forward_pipe),
		.issue_A_bank(DUT_issue_A_bank),
		.issue_B_is_reg(DUT_issue_B_is_reg),
		.issue_B_is_bus_forward(DUT_issue_B_is_bus_forward),
		.issue_B_is_fast_forward(DUT_issue_B_is_fast_forward),
		.issue_B_fast_forward_pipe(DUT_issue_B_fast_forward_pipe),
		.issue_B_bank(DUT_issue_B_bank),
		.issue_cq_index(DUT_issue_cq_index),

	    // pipeline feedback
		.issue_ready(tb_issue_ready),

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

		if (expected_issue_A_bank !== DUT_issue_A_bank) begin
			$display("TB ERROR: expected_issue_A_bank (%h) != DUT_issue_A_bank (%h)",
				expected_issue_A_bank, DUT_issue_A_bank);
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

		if (expected_issue_B_bank !== DUT_issue_B_bank) begin
			$display("TB ERROR: expected_issue_B_bank (%h) != DUT_issue_B_bank (%h)",
				expected_issue_B_bank, DUT_issue_B_bank);
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
		tb_stamofu_iq_enq_valid = '0;
		tb_stamofu_iq_enq_is_store = '0;
		tb_stamofu_iq_enq_is_amo = '0;
		tb_stamofu_iq_enq_is_fence = '0;
		tb_stamofu_iq_enq_op = '0;
		tb_stamofu_iq_enq_imm12 = '0;
		tb_stamofu_iq_enq_A_PR = '0;
		tb_stamofu_iq_enq_A_ready = '0;
		tb_stamofu_iq_enq_A_is_zero = '0;
		tb_stamofu_iq_enq_B_PR = '0;
		tb_stamofu_iq_enq_B_ready = '0;
		tb_stamofu_iq_enq_B_is_zero = '0;
		tb_stamofu_iq_enq_cq_index = '0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // fast forward notifs
		tb_fast_forward_notif_valid_by_pipe = '0;
		tb_fast_forward_notif_PR_by_pipe = '0;
	    // pipeline issue 
	    // pipeline feedback
		tb_issue_ready = '0;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_stamofu_iq_enq_ready  = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // pipeline issue 
		expected_issue_valid = '0;
		expected_issue_is_store = '0;
		expected_issue_is_amo = '0;
		expected_issue_is_fence = '0;
		expected_issue_op = '0;
		expected_issue_imm12 = '0;
		expected_issue_A_is_reg = '0;
		expected_issue_A_is_bus_forward = '0;
		expected_issue_A_is_fast_forward = '0;
		expected_issue_A_fast_forward_pipe = '0;
		expected_issue_A_bank = '0;
		expected_issue_B_is_reg = '0;
		expected_issue_B_is_bus_forward = '0;
		expected_issue_B_is_fast_forward = '0;
		expected_issue_B_fast_forward_pipe = '0;
		expected_issue_B_bank = '0;
		expected_issue_cq_index = '0;
	    // pipeline feedback
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
		tb_stamofu_iq_enq_valid = '0;
		tb_stamofu_iq_enq_is_store = '0;
		tb_stamofu_iq_enq_is_amo = '0;
		tb_stamofu_iq_enq_is_fence = '0;
		tb_stamofu_iq_enq_op = '0;
		tb_stamofu_iq_enq_imm12 = '0;
		tb_stamofu_iq_enq_A_PR = '0;
		tb_stamofu_iq_enq_A_ready = '0;
		tb_stamofu_iq_enq_A_is_zero = '0;
		tb_stamofu_iq_enq_B_PR = '0;
		tb_stamofu_iq_enq_B_ready = '0;
		tb_stamofu_iq_enq_B_is_zero = '0;
		tb_stamofu_iq_enq_cq_index = '0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // fast forward notifs
		tb_fast_forward_notif_valid_by_pipe = '0;
		tb_fast_forward_notif_PR_by_pipe = '0;
	    // pipeline issue 
	    // pipeline feedback
		tb_issue_ready = '0;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_stamofu_iq_enq_ready  = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // pipeline issue 
		expected_issue_valid = '0;
		expected_issue_is_store = '0;
		expected_issue_is_amo = '0;
		expected_issue_is_fence = '0;
		expected_issue_op = '0;
		expected_issue_imm12 = '0;
		expected_issue_A_is_reg = '0;
		expected_issue_A_is_bus_forward = '0;
		expected_issue_A_is_fast_forward = '0;
		expected_issue_A_fast_forward_pipe = '0;
		expected_issue_A_bank = '0;
		expected_issue_B_is_reg = '0;
		expected_issue_B_is_bus_forward = '0;
		expected_issue_B_is_fast_forward = '0;
		expected_issue_B_fast_forward_pipe = '0;
		expected_issue_B_bank = '0;
		expected_issue_cq_index = '0;
	    // pipeline feedback
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
		tb_stamofu_iq_enq_valid = '0;
		tb_stamofu_iq_enq_is_store = '0;
		tb_stamofu_iq_enq_is_amo = '0;
		tb_stamofu_iq_enq_is_fence = '0;
		tb_stamofu_iq_enq_op = '0;
		tb_stamofu_iq_enq_imm12 = '0;
		tb_stamofu_iq_enq_A_PR = '0;
		tb_stamofu_iq_enq_A_ready = '0;
		tb_stamofu_iq_enq_A_is_zero = '0;
		tb_stamofu_iq_enq_B_PR = '0;
		tb_stamofu_iq_enq_B_ready = '0;
		tb_stamofu_iq_enq_B_is_zero = '0;
		tb_stamofu_iq_enq_cq_index = '0;
	    // issue queue enqueue feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // fast forward notifs
		tb_fast_forward_notif_valid_by_pipe = '0;
		tb_fast_forward_notif_PR_by_pipe = '0;
	    // pipeline issue 
	    // pipeline feedback
		tb_issue_ready = '0;
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_stamofu_iq_enq_ready  = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // pipeline issue 
		expected_issue_valid = '0;
		expected_issue_is_store = '0;
		expected_issue_is_amo = '0;
		expected_issue_is_fence = '0;
		expected_issue_op = '0;
		expected_issue_imm12 = '0;
		expected_issue_A_is_reg = '0;
		expected_issue_A_is_bus_forward = '0;
		expected_issue_A_is_fast_forward = '0;
		expected_issue_A_fast_forward_pipe = '0;
		expected_issue_A_bank = '0;
		expected_issue_B_is_reg = '0;
		expected_issue_B_is_bus_forward = '0;
		expected_issue_B_is_fast_forward = '0;
		expected_issue_B_fast_forward_pipe = '0;
		expected_issue_B_bank = '0;
		expected_issue_cq_index = '0;
	    // pipeline feedback
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