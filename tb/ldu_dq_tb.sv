/*
    Filename: ldu_dq_tb.sv
    Author: zlagpacan
    Description: Testbench for ldu_dq module. 
    Spec: LOROF/spec/design/ldu_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ldu_dq_tb ();

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

    // op dispatch by way
	logic [3:0] tb_dispatch_attempt_by_way;
	logic [3:0] tb_dispatch_valid_by_way;
	logic [3:0][3:0] tb_dispatch_op_by_way;
	logic [3:0][11:0] tb_dispatch_imm12_by_way;
	logic [3:0][MDPT_INFO_WIDTH-1:0] tb_dispatch_mdp_info_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0] tb_dispatch_A_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // op enqueue to central queue
	logic DUT_ldu_cq_enq_valid, expected_ldu_cq_enq_valid;
	logic [MDPT_INFO_WIDTH-1:0] DUT_ldu_cq_enq_mdp_info, expected_ldu_cq_enq_mdp_info;
	logic [LOG_PR_COUNT-1:0] DUT_ldu_cq_enq_dest_PR, expected_ldu_cq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_ldu_cq_enq_ROB_index, expected_ldu_cq_enq_ROB_index;

    // central queue enqueue feedback
	logic tb_ldu_cq_enq_ready;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_ldu_cq_enq_index;

    // op enqueue to issue queue
	logic DUT_ldu_iq_enq_valid, expected_ldu_iq_enq_valid;
	logic [3:0] DUT_ldu_iq_enq_op, expected_ldu_iq_enq_op;
	logic [11:0] DUT_ldu_iq_enq_imm12, expected_ldu_iq_enq_imm12;
	logic [LOG_PR_COUNT-1:0] DUT_ldu_iq_enq_A_PR, expected_ldu_iq_enq_A_PR;
	logic DUT_ldu_iq_enq_A_ready, expected_ldu_iq_enq_A_ready;
	logic DUT_ldu_iq_enq_A_is_zero, expected_ldu_iq_enq_A_is_zero;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_ldu_iq_enq_cq_index, expected_ldu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic tb_ldu_iq_enq_ready;

    // restart from ROB
	logic tb_rob_restart_valid;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ldu_dq #(
		.LDU_DQ_ENTRIES(4)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op dispatch by way
		.dispatch_attempt_by_way(tb_dispatch_attempt_by_way),
		.dispatch_valid_by_way(tb_dispatch_valid_by_way),
		.dispatch_op_by_way(tb_dispatch_op_by_way),
		.dispatch_imm12_by_way(tb_dispatch_imm12_by_way),
		.dispatch_mdp_info_by_way(tb_dispatch_mdp_info_by_way),
		.dispatch_A_PR_by_way(tb_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_A_is_zero_by_way(tb_dispatch_A_is_zero_by_way),
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // op dispatch feedback
		.dispatch_ack_by_way(DUT_dispatch_ack_by_way),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // op enqueue to central queue
		.ldu_cq_enq_valid(DUT_ldu_cq_enq_valid),
		.ldu_cq_enq_mdp_info(DUT_ldu_cq_enq_mdp_info),
		.ldu_cq_enq_dest_PR(DUT_ldu_cq_enq_dest_PR),
		.ldu_cq_enq_ROB_index(DUT_ldu_cq_enq_ROB_index),

	    // central queue enqueue feedback
		.ldu_cq_enq_ready(tb_ldu_cq_enq_ready),
		.ldu_cq_enq_index(tb_ldu_cq_enq_index),

	    // op enqueue to issue queue
		.ldu_iq_enq_valid(DUT_ldu_iq_enq_valid),
		.ldu_iq_enq_op(DUT_ldu_iq_enq_op),
		.ldu_iq_enq_imm12(DUT_ldu_iq_enq_imm12),
		.ldu_iq_enq_A_PR(DUT_ldu_iq_enq_A_PR),
		.ldu_iq_enq_A_ready(DUT_ldu_iq_enq_A_ready),
		.ldu_iq_enq_A_is_zero(DUT_ldu_iq_enq_A_is_zero),
		.ldu_iq_enq_cq_index(DUT_ldu_iq_enq_cq_index),

	    // issue queue enqueue feedback
		.ldu_iq_enq_ready(tb_ldu_iq_enq_ready),

	    // restart from ROB
		.rob_restart_valid(tb_rob_restart_valid)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_dispatch_ack_by_way !== DUT_dispatch_ack_by_way) begin
			$display("TB ERROR: expected_dispatch_ack_by_way (%h) != DUT_dispatch_ack_by_way (%h)",
				expected_dispatch_ack_by_way, DUT_dispatch_ack_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_enq_valid !== DUT_ldu_cq_enq_valid) begin
			$display("TB ERROR: expected_ldu_cq_enq_valid (%h) != DUT_ldu_cq_enq_valid (%h)",
				expected_ldu_cq_enq_valid, DUT_ldu_cq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_enq_mdp_info !== DUT_ldu_cq_enq_mdp_info) begin
			$display("TB ERROR: expected_ldu_cq_enq_mdp_info (%h) != DUT_ldu_cq_enq_mdp_info (%h)",
				expected_ldu_cq_enq_mdp_info, DUT_ldu_cq_enq_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_enq_dest_PR !== DUT_ldu_cq_enq_dest_PR) begin
			$display("TB ERROR: expected_ldu_cq_enq_dest_PR (%h) != DUT_ldu_cq_enq_dest_PR (%h)",
				expected_ldu_cq_enq_dest_PR, DUT_ldu_cq_enq_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_cq_enq_ROB_index !== DUT_ldu_cq_enq_ROB_index) begin
			$display("TB ERROR: expected_ldu_cq_enq_ROB_index (%h) != DUT_ldu_cq_enq_ROB_index (%h)",
				expected_ldu_cq_enq_ROB_index, DUT_ldu_cq_enq_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_iq_enq_valid !== DUT_ldu_iq_enq_valid) begin
			$display("TB ERROR: expected_ldu_iq_enq_valid (%h) != DUT_ldu_iq_enq_valid (%h)",
				expected_ldu_iq_enq_valid, DUT_ldu_iq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_iq_enq_op !== DUT_ldu_iq_enq_op) begin
			$display("TB ERROR: expected_ldu_iq_enq_op (%h) != DUT_ldu_iq_enq_op (%h)",
				expected_ldu_iq_enq_op, DUT_ldu_iq_enq_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_iq_enq_imm12 !== DUT_ldu_iq_enq_imm12) begin
			$display("TB ERROR: expected_ldu_iq_enq_imm12 (%h) != DUT_ldu_iq_enq_imm12 (%h)",
				expected_ldu_iq_enq_imm12, DUT_ldu_iq_enq_imm12);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_iq_enq_A_PR !== DUT_ldu_iq_enq_A_PR) begin
			$display("TB ERROR: expected_ldu_iq_enq_A_PR (%h) != DUT_ldu_iq_enq_A_PR (%h)",
				expected_ldu_iq_enq_A_PR, DUT_ldu_iq_enq_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_iq_enq_A_ready !== DUT_ldu_iq_enq_A_ready) begin
			$display("TB ERROR: expected_ldu_iq_enq_A_ready (%h) != DUT_ldu_iq_enq_A_ready (%h)",
				expected_ldu_iq_enq_A_ready, DUT_ldu_iq_enq_A_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_iq_enq_A_is_zero !== DUT_ldu_iq_enq_A_is_zero) begin
			$display("TB ERROR: expected_ldu_iq_enq_A_is_zero (%h) != DUT_ldu_iq_enq_A_is_zero (%h)",
				expected_ldu_iq_enq_A_is_zero, DUT_ldu_iq_enq_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ldu_iq_enq_cq_index !== DUT_ldu_iq_enq_cq_index) begin
			$display("TB ERROR: expected_ldu_iq_enq_cq_index (%h) != DUT_ldu_iq_enq_cq_index (%h)",
				expected_ldu_iq_enq_cq_index, DUT_ldu_iq_enq_cq_index);
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
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b0;
		expected_ldu_cq_enq_mdp_info = 8'h0;
		expected_ldu_cq_enq_dest_PR = 7'h0;
		expected_ldu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b0;
		expected_ldu_iq_enq_op = 4'b0000;
		expected_ldu_iq_enq_imm12 = 12'h0;
		expected_ldu_iq_enq_A_PR = 7'h0;
		expected_ldu_iq_enq_A_ready = 1'b0;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b0;
		expected_ldu_cq_enq_mdp_info = 8'h0;
		expected_ldu_cq_enq_dest_PR = 7'h0;
		expected_ldu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b0;
		expected_ldu_iq_enq_op = 4'b0000;
		expected_ldu_iq_enq_imm12 = 12'h0;
		expected_ldu_iq_enq_A_PR = 7'h0;
		expected_ldu_iq_enq_A_ready = 1'b0;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

        // ------------------------------------------------------------
        // sequence:
        test_case = "sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: nop",
			"\n\t\t\t", "2: nop",
			"\n\t\t\t", "1: nop",
			"\n\t\t\t", "0: nop",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: nop",
			"\n\t\t\t", "2: nop",
			"\n\t\t\t", "1: nop",
			"\n\t\t\t", "0: nop"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b0;
		expected_ldu_cq_enq_mdp_info = 8'h0;
		expected_ldu_cq_enq_dest_PR = 7'h0;
		expected_ldu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b0;
		expected_ldu_iq_enq_op = 4'b0000;
		expected_ldu_iq_enq_imm12 = 12'h0;
		expected_ldu_iq_enq_A_PR = 7'h0;
		expected_ldu_iq_enq_A_ready = 1'b0;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 1 r",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v 0 zero",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1101;
		tb_dispatch_valid_by_way = 4'b0101;
		tb_dispatch_op_by_way = {4'b1001, 4'b0001, 4'b1000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h999, 12'h111, 12'h888, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h96, 8'h1e, 8'h87, 8'h0f};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h1, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0100;
		tb_dispatch_A_is_zero_by_way = 4'b0001;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'he1, 7'h0, 7'hf0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'he1, 7'h0, 7'hf0};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b1101;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b0;
		expected_ldu_cq_enq_mdp_info = 8'h0;
		expected_ldu_cq_enq_dest_PR = 7'h0;
		expected_ldu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b0;
		expected_ldu_iq_enq_op = 4'b0000;
		expected_ldu_iq_enq_imm12 = 12'h0;
		expected_ldu_iq_enq_A_PR = 7'h0;
		expected_ldu_iq_enq_A_ready = 1'b0;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v 3 n",
			"\n\t\t\t", "2: v 2 n",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v 1 r",
			"\n\t\t\t", "0: v 0 zero"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1100;
		tb_dispatch_valid_by_way = 4'b1100;
		tb_dispatch_op_by_way = {4'b0011, 4'b0010, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h333, 12'h222, 12'h000, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h3c, 8'h2d, 8'h00, 8'h00};
		tb_dispatch_A_PR_by_way = {7'h3, 7'h2, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0011;
		tb_dispatch_A_is_zero_by_way = 4'b0011;
		tb_dispatch_dest_PR_by_way = {7'hc3, 7'hd2, 7'h00, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'hc3, 7'hd2, 7'h00, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b1100;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b1;
		expected_ldu_cq_enq_mdp_info = 8'h0f;
		expected_ldu_cq_enq_dest_PR = 7'hf0;
		expected_ldu_cq_enq_ROB_index = 7'hf0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b1;
		expected_ldu_iq_enq_op = 4'b0000;
		expected_ldu_iq_enq_imm12 = 12'h0;
		expected_ldu_iq_enq_A_PR = 7'h0;
		expected_ldu_iq_enq_A_ready = 1'b0;
		expected_ldu_iq_enq_A_is_zero = 1'b1;
		expected_ldu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v 5 n",
			"\n\t\t\t", "0: v 4 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 3 nR",
			"\n\t\t\t", "1: v 2 n",
			"\n\t\t\t", "0: v 1 r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0011;
		tb_dispatch_valid_by_way = 4'b0011;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0100};
		tb_dispatch_imm12_by_way = {12'h000, 12'h000, 12'h555, 12'h444};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h00, 8'h5a, 8'h4b};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h5, 7'h4};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h00, 7'ha5, 7'hb4};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h00, 7'ha5, 7'hb4};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 1;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0001;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b1;
		expected_ldu_cq_enq_mdp_info = 8'h1e;
		expected_ldu_cq_enq_dest_PR = 7'he1;
		expected_ldu_cq_enq_ROB_index = 7'he1;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b1;
		expected_ldu_iq_enq_op = 4'b0001;
		expected_ldu_iq_enq_imm12 = 12'h111;
		expected_ldu_iq_enq_A_PR = 7'h1;
		expected_ldu_iq_enq_A_ready = 1'b1;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 1;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v 5 n",
			"\n\t\t\t", "0: i 4 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 4 n",
			"\n\t\t\t", "1: v 3 r",
			"\n\t\t\t", "0: v 2 n (not ready)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0010;
		tb_dispatch_valid_by_way = 4'b0011;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0101, 4'b0100};
		tb_dispatch_imm12_by_way = {12'h000, 12'h000, 12'h555, 12'h444};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h00, 8'h5a, 8'h4b};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h5, 7'h4};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h00, 7'ha5, 7'hb4};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h00, 7'ha5, 7'hb4};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b0;
		tb_ldu_cq_enq_index = 2;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0010;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b0;
		expected_ldu_cq_enq_mdp_info = 8'h2d;
		expected_ldu_cq_enq_dest_PR = 7'hd2;
		expected_ldu_cq_enq_ROB_index = 7'hd2;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b0;
		expected_ldu_iq_enq_op = 4'b0010;
		expected_ldu_iq_enq_imm12 = 12'h222;
		expected_ldu_iq_enq_A_PR = 7'h2;
		expected_ldu_iq_enq_A_ready = 1'b0;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 2;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v 8 n",
			"\n\t\t\t", "2: v 7 n",
			"\n\t\t\t", "1: v 6 r",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v 5 nR",
			"\n\t\t\t", "2: v 4 n",
			"\n\t\t\t", "1: v 3 r",
			"\n\t\t\t", "0: v 2 nR"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1110;
		tb_dispatch_valid_by_way = 4'b1110;
		tb_dispatch_op_by_way = {4'b1000, 4'b0111, 4'b0110, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h888, 12'h777, 12'h666, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h87, 8'h78, 8'h69, 8'h00};
		tb_dispatch_A_PR_by_way = {7'h8, 7'h7, 7'h6, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0010;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0110;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h1, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 2;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b1;
		expected_ldu_cq_enq_mdp_info = 8'h2d;
		expected_ldu_cq_enq_dest_PR = 7'hd2;
		expected_ldu_cq_enq_ROB_index = 7'hd2;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b1;
		expected_ldu_iq_enq_op = 4'b0010;
		expected_ldu_iq_enq_imm12 = 12'h222;
		expected_ldu_iq_enq_A_PR = 7'h2;
		expected_ldu_iq_enq_A_ready = 1'b1;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 2;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v 8 n",
			"\n\t\t\t", "2: v 7 n",
			"\n\t\t\t", "1: v 6 r",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 5 r",
			"\n\t\t\t", "1: v 4 n",
			"\n\t\t\t", "0: v 3 r"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1110;
		tb_dispatch_valid_by_way = 4'b1110;
		tb_dispatch_op_by_way = {4'b1000, 4'b0111, 4'b0110, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h888, 12'h777, 12'h666, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h87, 8'h78, 8'h69, 8'h00};
		tb_dispatch_A_PR_by_way = {7'h8, 7'h7, 7'h6, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0010;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 3;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0010;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b1;
		expected_ldu_cq_enq_mdp_info = 8'h3c;
		expected_ldu_cq_enq_dest_PR = 7'hc3;
		expected_ldu_cq_enq_ROB_index = 7'hc3;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b1;
		expected_ldu_iq_enq_op = 4'b0011;
		expected_ldu_iq_enq_imm12 = 12'h333;
		expected_ldu_iq_enq_A_PR = 7'h3;
		expected_ldu_iq_enq_A_ready = 1'b1;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 3;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v 8 n",
			"\n\t\t\t", "2: v 7 n",
			"\n\t\t\t", "1: i 6 r",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 6 r",
			"\n\t\t\t", "1: v 5 r",
			"\n\t\t\t", "0: v 4 n"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1100;
		tb_dispatch_valid_by_way = 4'b1110;
		tb_dispatch_op_by_way = {4'b1000, 4'b0111, 4'b0110, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h888, 12'h777, 12'h666, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h87, 8'h78, 8'h69, 8'h00};
		tb_dispatch_A_PR_by_way = {7'h8, 7'h7, 7'h6, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0010;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 4;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0100;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b1;
		expected_ldu_cq_enq_mdp_info = 8'h4b;
		expected_ldu_cq_enq_dest_PR = 7'hb4;
		expected_ldu_cq_enq_ROB_index = 7'hb4;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b1;
		expected_ldu_iq_enq_op = 4'b0100;
		expected_ldu_iq_enq_imm12 = 12'h444;
		expected_ldu_iq_enq_A_PR = 7'h4;
		expected_ldu_iq_enq_A_ready = 1'b0;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 4;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v 8 n",
			"\n\t\t\t", "2: i 7 n",
			"\n\t\t\t", "1: i 6 r",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v 7 n",
			"\n\t\t\t", "1: v 6 r",
			"\n\t\t\t", "0: v 5 r (ROB RESTARTING)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1000;
		tb_dispatch_valid_by_way = 4'b1110;
		tb_dispatch_op_by_way = {4'b1000, 4'b0111, 4'b0110, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h888, 12'h777, 12'h666, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h87, 8'h78, 8'h69, 8'h00};
		tb_dispatch_A_PR_by_way = {7'h8, 7'h7, 7'h6, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0010;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h78, 7'h87, 7'h96, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 5;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b1000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b1;
		expected_ldu_cq_enq_mdp_info = 8'h5a;
		expected_ldu_cq_enq_dest_PR = 7'ha5;
		expected_ldu_cq_enq_ROB_index = 7'ha5;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b1;
		expected_ldu_iq_enq_op = 4'b0101;
		expected_ldu_iq_enq_imm12 = 12'h555;
		expected_ldu_iq_enq_A_PR = 7'h5;
		expected_ldu_iq_enq_A_ready = 1'b1;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 5;
	    // issue queue enqueue feedback
	    // restart from ROB

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v C n",
			"\n\t\t\t", "2: v B r",
			"\n\t\t\t", "1: v A n",
			"\n\t\t\t", "0: v 9 n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1111;
		tb_dispatch_valid_by_way = 4'b1111;
		tb_dispatch_op_by_way = {4'b1100, 4'b1011, 4'b1010, 4'b1001};
		tb_dispatch_imm12_by_way = {12'hccc, 12'hbbb, 12'haaa, 12'h999};
		tb_dispatch_mdp_info_by_way = {8'hc3, 8'hb4, 8'ha5, 8'h96};
		tb_dispatch_A_PR_by_way = {7'hc, 7'hb, 7'ha, 7'h9};
		tb_dispatch_A_ready_by_way = 4'b0100;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h3c, 7'h4b, 7'h5a, 7'h69};
		tb_dispatch_ROB_index_by_way = {7'h3c, 7'h4b, 7'h5a, 7'h69};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_ldu_cq_enq_ready = 1'b1;
		tb_ldu_cq_enq_index = 6;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_ldu_iq_enq_ready = 1'b1;
	    // restart from ROB
		tb_rob_restart_valid = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b1111;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_ldu_cq_enq_valid = 1'b0;
		expected_ldu_cq_enq_mdp_info = 8'h5a;
		expected_ldu_cq_enq_dest_PR = 7'ha5;
		expected_ldu_cq_enq_ROB_index = 7'ha5;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_ldu_iq_enq_valid = 1'b0;
		expected_ldu_iq_enq_op = 4'b0101;
		expected_ldu_iq_enq_imm12 = 12'h555;
		expected_ldu_iq_enq_A_PR = 7'h5;
		expected_ldu_iq_enq_A_ready = 1'b1;
		expected_ldu_iq_enq_A_is_zero = 1'b0;
		expected_ldu_iq_enq_cq_index = 6;
	    // issue queue enqueue feedback
	    // restart from ROB

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