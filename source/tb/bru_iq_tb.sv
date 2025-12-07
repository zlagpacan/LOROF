/*
    Filename: bru_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for bru_iq module. 
    Spec: LOROF/spec/design/bru_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module bru_iq_tb #(
	parameter BRU_IQ_ENTRIES = 6,
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
	logic [3:0] tb_iq_enq_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_iq_enq_pred_info;
	logic tb_iq_enq_pred_lru;
	logic tb_iq_enq_is_link_ra;
	logic tb_iq_enq_is_ret_ra;
	logic [31:0] tb_iq_enq_PC;
	logic [31:0] tb_iq_enq_pred_PC;
	logic [19:0] tb_iq_enq_imm20;
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

    // pipeline issue
	logic DUT_issue_valid, expected_issue_valid;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_issue_pred_info, expected_issue_pred_info;
	logic DUT_issue_pred_lru, expected_issue_pred_lru;
	logic DUT_issue_is_link_ra, expected_issue_is_link_ra;
	logic DUT_issue_is_ret_ra, expected_issue_is_ret_ra;
	logic [31:0] DUT_issue_PC, expected_issue_PC;
	logic [31:0] DUT_issue_pred_PC, expected_issue_pred_PC;
	logic [19:0] DUT_issue_imm20, expected_issue_imm20;
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
	logic [LOG_PR_COUNT-1:0] DUT_issue_dest_PR, expected_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_ROB_index, expected_issue_ROB_index;

    // pipeline feedback
	logic tb_issue_ready;

    // reg read req to PRF
	logic DUT_PRF_req_A_valid, expected_PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_A_PR, expected_PRF_req_A_PR;
	logic DUT_PRF_req_B_valid, expected_PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_B_PR, expected_PRF_req_B_PR;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bru_iq #(
		.BRU_IQ_ENTRIES(BRU_IQ_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op enqueue to issue queue
		.iq_enq_valid(tb_iq_enq_valid),
		.iq_enq_op(tb_iq_enq_op),
		.iq_enq_pred_info(tb_iq_enq_pred_info),
		.iq_enq_pred_lru(tb_iq_enq_pred_lru),
		.iq_enq_is_link_ra(tb_iq_enq_is_link_ra),
		.iq_enq_is_ret_ra(tb_iq_enq_is_ret_ra),
		.iq_enq_PC(tb_iq_enq_PC),
		.iq_enq_pred_PC(tb_iq_enq_pred_PC),
		.iq_enq_imm20(tb_iq_enq_imm20),
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

	    // pipeline issue
		.issue_valid(DUT_issue_valid),
		.issue_op(DUT_issue_op),
		.issue_pred_info(DUT_issue_pred_info),
		.issue_pred_lru(DUT_issue_pred_lru),
		.issue_is_link_ra(DUT_issue_is_link_ra),
		.issue_is_ret_ra(DUT_issue_is_ret_ra),
		.issue_PC(DUT_issue_PC),
		.issue_pred_PC(DUT_issue_pred_PC),
		.issue_imm20(DUT_issue_imm20),
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
		.issue_dest_PR(DUT_issue_dest_PR),
		.issue_ROB_index(DUT_issue_ROB_index),

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
		if (expected_iq_enq_ready !== DUT_iq_enq_ready) begin
			$display("TB ERROR: expected_iq_enq_ready (%h) != DUT_iq_enq_ready (%h)",
				expected_iq_enq_ready, DUT_iq_enq_ready);
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

		if (expected_issue_pred_info !== DUT_issue_pred_info) begin
			$display("TB ERROR: expected_issue_pred_info (%h) != DUT_issue_pred_info (%h)",
				expected_issue_pred_info, DUT_issue_pred_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_pred_lru !== DUT_issue_pred_lru) begin
			$display("TB ERROR: expected_issue_pred_lru (%h) != DUT_issue_pred_lru (%h)",
				expected_issue_pred_lru, DUT_issue_pred_lru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_is_link_ra !== DUT_issue_is_link_ra) begin
			$display("TB ERROR: expected_issue_is_link_ra (%h) != DUT_issue_is_link_ra (%h)",
				expected_issue_is_link_ra, DUT_issue_is_link_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_is_ret_ra !== DUT_issue_is_ret_ra) begin
			$display("TB ERROR: expected_issue_is_ret_ra (%h) != DUT_issue_is_ret_ra (%h)",
				expected_issue_is_ret_ra, DUT_issue_is_ret_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_PC !== DUT_issue_PC) begin
			$display("TB ERROR: expected_issue_PC (%h) != DUT_issue_PC (%h)",
				expected_issue_PC, DUT_issue_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_pred_PC !== DUT_issue_pred_PC) begin
			$display("TB ERROR: expected_issue_pred_PC (%h) != DUT_issue_pred_PC (%h)",
				expected_issue_pred_PC, DUT_issue_pred_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_imm20 !== DUT_issue_imm20) begin
			$display("TB ERROR: expected_issue_imm20 (%h) != DUT_issue_imm20 (%h)",
				expected_issue_imm20, DUT_issue_imm20);
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
		tb_iq_enq_op = '0;
		tb_iq_enq_pred_info = '0;
		tb_iq_enq_pred_lru = '0;
		tb_iq_enq_is_link_ra = '0;
		tb_iq_enq_is_ret_ra = '0;
		tb_iq_enq_PC = '0;
		tb_iq_enq_pred_PC = '0;
		tb_iq_enq_imm20 = '0;
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
	    // pipeline issue
	    // pipeline feedback
		tb_issue_ready = '0;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // pipeline issue
		expected_issue_valid = '0;
		expected_issue_op = '0;
		expected_issue_pred_info = '0;
		expected_issue_pred_lru = '0;
		expected_issue_is_link_ra = '0;
		expected_issue_is_ret_ra = '0;
		expected_issue_PC = '0;
		expected_issue_pred_PC = '0;
		expected_issue_imm20 = '0;
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
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
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
		tb_iq_enq_valid = '0;
		tb_iq_enq_op = '0;
		tb_iq_enq_pred_info = '0;
		tb_iq_enq_pred_lru = '0;
		tb_iq_enq_is_link_ra = '0;
		tb_iq_enq_is_ret_ra = '0;
		tb_iq_enq_PC = '0;
		tb_iq_enq_pred_PC = '0;
		tb_iq_enq_imm20 = '0;
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
	    // pipeline issue
	    // pipeline feedback
		tb_issue_ready = '0;
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // pipeline issue
		expected_issue_valid = '0;
		expected_issue_op = '0;
		expected_issue_pred_info = '0;
		expected_issue_pred_lru = '0;
		expected_issue_is_link_ra = '0;
		expected_issue_is_ret_ra = '0;
		expected_issue_PC = '0;
		expected_issue_pred_PC = '0;
		expected_issue_imm20 = '0;
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
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
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
		tb_iq_enq_valid = '0;
		tb_iq_enq_op = '0;
		tb_iq_enq_pred_info = '0;
		tb_iq_enq_pred_lru = '0;
		tb_iq_enq_is_link_ra = '0;
		tb_iq_enq_is_ret_ra = '0;
		tb_iq_enq_PC = '0;
		tb_iq_enq_pred_PC = '0;
		tb_iq_enq_imm20 = '0;
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
	    // pipeline issue
	    // pipeline feedback
		tb_issue_ready = '0;
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		expected_iq_enq_ready = 1'b1;
	    // writeback bus by bank
	    // fast forward notifs
	    // pipeline issue
		expected_issue_valid = '0;
		expected_issue_op = '0;
		expected_issue_pred_info = '0;
		expected_issue_pred_lru = '0;
		expected_issue_is_link_ra = '0;
		expected_issue_is_ret_ra = '0;
		expected_issue_PC = '0;
		expected_issue_pred_PC = '0;
		expected_issue_imm20 = '0;
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
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
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