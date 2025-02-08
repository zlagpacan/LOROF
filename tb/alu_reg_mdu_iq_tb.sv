/*
    Filename: alu_reg_mdu_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_reg_mdu_iq module. 
    Spec: LOROF/spec/design/alu_reg_mdu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

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


    // op dispatch by way
	logic [3:0] tb_dispatch_attempt_by_way;
	logic [3:0] tb_dispatch_valid_alu_reg_by_way;
	logic [3:0] tb_dispatch_valid_mdu_by_way;
	logic [3:0][3:0] tb_dispatch_op_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_way;
	logic [3:0] tb_dispatch_B_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // ALU op dispatch feedback
	// logic [3:0] DUT_dispatch_ready_advertisement_by_way, expected_dispatch_ready_advertisement_by_way;
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // pipeline feedback
	logic tb_alu_reg_pipeline_ready;
	logic tb_mdu_pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // op issue to ALU Reg-Reg pipeline
	logic DUT_issue_alu_reg_valid, expected_issue_alu_reg_valid;
	logic [3:0] DUT_issue_alu_reg_op, expected_issue_alu_reg_op;
	logic DUT_issue_alu_reg_A_forward, expected_issue_alu_reg_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_alu_reg_A_bank, expected_issue_alu_reg_A_bank;
	logic DUT_issue_alu_reg_B_forward, expected_issue_alu_reg_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_alu_reg_B_bank, expected_issue_alu_reg_B_bank;
	logic [LOG_PR_COUNT-1:0] DUT_issue_alu_reg_dest_PR, expected_issue_alu_reg_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_alu_reg_ROB_index, expected_issue_alu_reg_ROB_index;

    // ALU Reg-Reg pipeline reg read req to PRF
	logic DUT_PRF_alu_reg_req_A_valid, expected_PRF_alu_reg_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_alu_reg_req_A_PR, expected_PRF_alu_reg_req_A_PR;
	logic DUT_PRF_alu_reg_req_B_valid, expected_PRF_alu_reg_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_alu_reg_req_B_PR, expected_PRF_alu_reg_req_B_PR;

    // op issue to Mul-Div pipeline
	logic DUT_issue_mdu_valid, expected_issue_mdu_valid;
	logic [3:0] DUT_issue_mdu_op, expected_issue_mdu_op;
	logic DUT_issue_mdu_A_forward, expected_issue_mdu_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_mdu_A_bank, expected_issue_mdu_A_bank;
	logic DUT_issue_mdu_B_forward, expected_issue_mdu_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_mdu_B_bank, expected_issue_mdu_B_bank;
	logic [LOG_PR_COUNT-1:0] DUT_issue_mdu_dest_PR, expected_issue_mdu_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_mdu_ROB_index, expected_issue_mdu_ROB_index;

    // Mul-Div pipeline reg read req to PRF
	logic DUT_PRF_mdu_req_A_valid, expected_PRF_mdu_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_mdu_req_A_PR, expected_PRF_mdu_req_A_PR;
	logic DUT_PRF_mdu_req_B_valid, expected_PRF_mdu_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_mdu_req_B_PR, expected_PRF_mdu_req_B_PR;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_reg_mdu_iq #(
        .ALU_REG_MDU_IQ_ENTRIES(12)
    ) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // op dispatch by way
		.dispatch_attempt_by_way(tb_dispatch_attempt_by_way),
		.dispatch_valid_alu_reg_by_way(tb_dispatch_valid_alu_reg_by_way),
		.dispatch_valid_mdu_by_way(tb_dispatch_valid_mdu_by_way),
		.dispatch_op_by_way(tb_dispatch_op_by_way),
		.dispatch_A_PR_by_way(tb_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_B_PR_by_way(tb_dispatch_B_PR_by_way),
		.dispatch_B_ready_by_way(tb_dispatch_B_ready_by_way),
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // ALU op dispatch feedback
		// .dispatch_ready_advertisement_by_way(DUT_dispatch_ready_advertisement_by_way),
        .dispatch_ack_by_way(DUT_dispatch_ack_by_way),

	    // pipeline feedback
		.alu_reg_pipeline_ready(tb_alu_reg_pipeline_ready),
		.mdu_pipeline_ready(tb_mdu_pipeline_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // op issue to ALU Reg-Reg pipeline
		.issue_alu_reg_valid(DUT_issue_alu_reg_valid),
		.issue_alu_reg_op(DUT_issue_alu_reg_op),
		.issue_alu_reg_A_forward(DUT_issue_alu_reg_A_forward),
		.issue_alu_reg_A_bank(DUT_issue_alu_reg_A_bank),
		.issue_alu_reg_B_forward(DUT_issue_alu_reg_B_forward),
		.issue_alu_reg_B_bank(DUT_issue_alu_reg_B_bank),
		.issue_alu_reg_dest_PR(DUT_issue_alu_reg_dest_PR),
		.issue_alu_reg_ROB_index(DUT_issue_alu_reg_ROB_index),

	    // ALU Reg-Reg pipeline reg read req to PRF
		.PRF_alu_reg_req_A_valid(DUT_PRF_alu_reg_req_A_valid),
		.PRF_alu_reg_req_A_PR(DUT_PRF_alu_reg_req_A_PR),
		.PRF_alu_reg_req_B_valid(DUT_PRF_alu_reg_req_B_valid),
		.PRF_alu_reg_req_B_PR(DUT_PRF_alu_reg_req_B_PR),

	    // op issue to Mul-Div pipeline
		.issue_mdu_valid(DUT_issue_mdu_valid),
		.issue_mdu_op(DUT_issue_mdu_op),
		.issue_mdu_A_forward(DUT_issue_mdu_A_forward),
		.issue_mdu_A_bank(DUT_issue_mdu_A_bank),
		.issue_mdu_B_forward(DUT_issue_mdu_B_forward),
		.issue_mdu_B_bank(DUT_issue_mdu_B_bank),
		.issue_mdu_dest_PR(DUT_issue_mdu_dest_PR),
		.issue_mdu_ROB_index(DUT_issue_mdu_ROB_index),

	    // Mul-Div pipeline reg read req to PRF
		.PRF_mdu_req_A_valid(DUT_PRF_mdu_req_A_valid),
		.PRF_mdu_req_A_PR(DUT_PRF_mdu_req_A_PR),
		.PRF_mdu_req_B_valid(DUT_PRF_mdu_req_B_valid),
		.PRF_mdu_req_B_PR(DUT_PRF_mdu_req_B_PR)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		// if (expected_dispatch_ready_advertisement_by_way !== DUT_dispatch_ready_advertisement_by_way) begin
		// 	$display("TB ERROR: expected_dispatch_ready_advertisement_by_way (%h) != DUT_dispatch_ready_advertisement_by_way (%h)",
		// 		expected_dispatch_ready_advertisement_by_way, DUT_dispatch_ready_advertisement_by_way);
		// 	num_errors++;
		// 	tb_error = 1'b1;
		// end

		if (expected_dispatch_ack_by_way !== DUT_dispatch_ack_by_way) begin
			$display("TB ERROR: expected_dispatch_ack_by_way (%h) != DUT_dispatch_ack_by_way (%h)",
				expected_dispatch_ack_by_way, DUT_dispatch_ack_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_valid !== DUT_issue_alu_reg_valid) begin
			$display("TB ERROR: expected_issue_alu_reg_valid (%h) != DUT_issue_alu_reg_valid (%h)",
				expected_issue_alu_reg_valid, DUT_issue_alu_reg_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_op !== DUT_issue_alu_reg_op) begin
			$display("TB ERROR: expected_issue_alu_reg_op (%h) != DUT_issue_alu_reg_op (%h)",
				expected_issue_alu_reg_op, DUT_issue_alu_reg_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_A_forward !== DUT_issue_alu_reg_A_forward) begin
			$display("TB ERROR: expected_issue_alu_reg_A_forward (%h) != DUT_issue_alu_reg_A_forward (%h)",
				expected_issue_alu_reg_A_forward, DUT_issue_alu_reg_A_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_A_bank !== DUT_issue_alu_reg_A_bank) begin
			$display("TB ERROR: expected_issue_alu_reg_A_bank (%h) != DUT_issue_alu_reg_A_bank (%h)",
				expected_issue_alu_reg_A_bank, DUT_issue_alu_reg_A_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_B_forward !== DUT_issue_alu_reg_B_forward) begin
			$display("TB ERROR: expected_issue_alu_reg_B_forward (%h) != DUT_issue_alu_reg_B_forward (%h)",
				expected_issue_alu_reg_B_forward, DUT_issue_alu_reg_B_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_B_bank !== DUT_issue_alu_reg_B_bank) begin
			$display("TB ERROR: expected_issue_alu_reg_B_bank (%h) != DUT_issue_alu_reg_B_bank (%h)",
				expected_issue_alu_reg_B_bank, DUT_issue_alu_reg_B_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_dest_PR !== DUT_issue_alu_reg_dest_PR) begin
			$display("TB ERROR: expected_issue_alu_reg_dest_PR (%h) != DUT_issue_alu_reg_dest_PR (%h)",
				expected_issue_alu_reg_dest_PR, DUT_issue_alu_reg_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_reg_ROB_index !== DUT_issue_alu_reg_ROB_index) begin
			$display("TB ERROR: expected_issue_alu_reg_ROB_index (%h) != DUT_issue_alu_reg_ROB_index (%h)",
				expected_issue_alu_reg_ROB_index, DUT_issue_alu_reg_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_alu_reg_req_A_valid !== DUT_PRF_alu_reg_req_A_valid) begin
			$display("TB ERROR: expected_PRF_alu_reg_req_A_valid (%h) != DUT_PRF_alu_reg_req_A_valid (%h)",
				expected_PRF_alu_reg_req_A_valid, DUT_PRF_alu_reg_req_A_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_alu_reg_req_A_PR !== DUT_PRF_alu_reg_req_A_PR) begin
			$display("TB ERROR: expected_PRF_alu_reg_req_A_PR (%h) != DUT_PRF_alu_reg_req_A_PR (%h)",
				expected_PRF_alu_reg_req_A_PR, DUT_PRF_alu_reg_req_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_alu_reg_req_B_valid !== DUT_PRF_alu_reg_req_B_valid) begin
			$display("TB ERROR: expected_PRF_alu_reg_req_B_valid (%h) != DUT_PRF_alu_reg_req_B_valid (%h)",
				expected_PRF_alu_reg_req_B_valid, DUT_PRF_alu_reg_req_B_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_alu_reg_req_B_PR !== DUT_PRF_alu_reg_req_B_PR) begin
			$display("TB ERROR: expected_PRF_alu_reg_req_B_PR (%h) != DUT_PRF_alu_reg_req_B_PR (%h)",
				expected_PRF_alu_reg_req_B_PR, DUT_PRF_alu_reg_req_B_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_valid !== DUT_issue_mdu_valid) begin
			$display("TB ERROR: expected_issue_mdu_valid (%h) != DUT_issue_mdu_valid (%h)",
				expected_issue_mdu_valid, DUT_issue_mdu_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_op !== DUT_issue_mdu_op) begin
			$display("TB ERROR: expected_issue_mdu_op (%h) != DUT_issue_mdu_op (%h)",
				expected_issue_mdu_op, DUT_issue_mdu_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_A_forward !== DUT_issue_mdu_A_forward) begin
			$display("TB ERROR: expected_issue_mdu_A_forward (%h) != DUT_issue_mdu_A_forward (%h)",
				expected_issue_mdu_A_forward, DUT_issue_mdu_A_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_A_bank !== DUT_issue_mdu_A_bank) begin
			$display("TB ERROR: expected_issue_mdu_A_bank (%h) != DUT_issue_mdu_A_bank (%h)",
				expected_issue_mdu_A_bank, DUT_issue_mdu_A_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_B_forward !== DUT_issue_mdu_B_forward) begin
			$display("TB ERROR: expected_issue_mdu_B_forward (%h) != DUT_issue_mdu_B_forward (%h)",
				expected_issue_mdu_B_forward, DUT_issue_mdu_B_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_B_bank !== DUT_issue_mdu_B_bank) begin
			$display("TB ERROR: expected_issue_mdu_B_bank (%h) != DUT_issue_mdu_B_bank (%h)",
				expected_issue_mdu_B_bank, DUT_issue_mdu_B_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_dest_PR !== DUT_issue_mdu_dest_PR) begin
			$display("TB ERROR: expected_issue_mdu_dest_PR (%h) != DUT_issue_mdu_dest_PR (%h)",
				expected_issue_mdu_dest_PR, DUT_issue_mdu_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_mdu_ROB_index !== DUT_issue_mdu_ROB_index) begin
			$display("TB ERROR: expected_issue_mdu_ROB_index (%h) != DUT_issue_mdu_ROB_index (%h)",
				expected_issue_mdu_ROB_index, DUT_issue_mdu_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_mdu_req_A_valid !== DUT_PRF_mdu_req_A_valid) begin
			$display("TB ERROR: expected_PRF_mdu_req_A_valid (%h) != DUT_PRF_mdu_req_A_valid (%h)",
				expected_PRF_mdu_req_A_valid, DUT_PRF_mdu_req_A_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_mdu_req_A_PR !== DUT_PRF_mdu_req_A_PR) begin
			$display("TB ERROR: expected_PRF_mdu_req_A_PR (%h) != DUT_PRF_mdu_req_A_PR (%h)",
				expected_PRF_mdu_req_A_PR, DUT_PRF_mdu_req_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_mdu_req_B_valid !== DUT_PRF_mdu_req_B_valid) begin
			$display("TB ERROR: expected_PRF_mdu_req_B_valid (%h) != DUT_PRF_mdu_req_B_valid (%h)",
				expected_PRF_mdu_req_B_valid, DUT_PRF_mdu_req_B_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_mdu_req_B_PR !== DUT_PRF_mdu_req_B_PR) begin
			$display("TB ERROR: expected_PRF_mdu_req_B_PR (%h) != DUT_PRF_mdu_req_B_PR (%h)",
				expected_PRF_mdu_req_B_PR, DUT_PRF_mdu_req_B_PR);
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
		tb_dispatch_valid_alu_reg_by_way = 4'b0000;
		tb_dispatch_valid_mdu_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'h0, 4'h0, 4'h0, 4'h0};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b0000;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b0;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h0;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h0;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b0;
		expected_issue_mdu_op = 4'h0;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h0;
		expected_issue_mdu_dest_PR = 7'h0;
		expected_issue_mdu_ROB_index = 7'h0;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b0;
		expected_PRF_mdu_req_A_PR = 7'h0;
		expected_PRF_mdu_req_B_valid = 1'b0;
		expected_PRF_mdu_req_B_PR = 7'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_alu_reg_by_way = 4'b0000;
		tb_dispatch_valid_mdu_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'h0, 4'h0, 4'h0, 4'h0};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b0000;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b0;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h0;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h0;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b0;
		expected_issue_mdu_op = 4'h0;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h0;
		expected_issue_mdu_dest_PR = 7'h0;
		expected_issue_mdu_ROB_index = 7'h0;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b0;
		expected_PRF_mdu_req_A_PR = 7'h0;
		expected_PRF_mdu_req_B_valid = 1'b0;
		expected_PRF_mdu_req_B_PR = 7'h0;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: i NOP", "\n\t\t",
            "IQ8: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: i NOP", "\n\t\t",
            "issue ALU Reg-Reg: i NOP", "\n\t\t",
            "issue Mul-Div: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_alu_reg_by_way = 4'b0000;
		tb_dispatch_valid_mdu_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'h0, 4'h0, 4'h0, 4'h0};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b0000;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b0;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h0;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h0;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b0;
		expected_issue_mdu_op = 4'h0;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h0;
		expected_issue_mdu_dest_PR = 7'h0;
		expected_issue_mdu_ROB_index = 7'h0;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b0;
		expected_PRF_mdu_req_A_PR = 7'h0;
		expected_PRF_mdu_req_B_valid = 1'b0;
		expected_PRF_mdu_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 3: ALU1 p9, pA:r, pB:r", "\n\t\t",
            "dispatch2: v 2: MUL1 p6, p7:f, p8:r", "\n\t\t",
            "dispatch1: v 1: MUL0 p3, p4:r, p5:r", "\n\t\t",
            "dispatch0: v 0: ALU0 p0, p1:r, p2:f", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: i NOP", "\n\t\t",
            "IQ8: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: i NOP", "\n\t\t",
            "issue ALU Reg-Reg: i NOP", "\n\t\t",
            "issue Mul-Div: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1111;
		tb_dispatch_valid_alu_reg_by_way = 4'b1001;
		tb_dispatch_valid_mdu_by_way = 4'b0110;
		tb_dispatch_op_by_way = {4'h1, 4'h1, 4'h0, 4'h0};
		tb_dispatch_A_PR_by_way = {7'hA, 7'h7, 7'h4, 7'h1};
		tb_dispatch_A_ready_by_way = 4'b1011;
		tb_dispatch_B_PR_by_way = {7'hB, 7'h8, 7'h5, 7'h2};
		tb_dispatch_B_ready_by_way = 4'b1110;
		tb_dispatch_dest_PR_by_way = {7'h9, 7'h6, 7'h3, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h3, 7'h2, 7'h1, 7'h0};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b1111;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b0;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h0;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h0;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b0;
		expected_issue_mdu_op = 4'h0;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h0;
		expected_issue_mdu_dest_PR = 7'h0;
		expected_issue_mdu_ROB_index = 7'h0;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b0;
		expected_PRF_mdu_req_A_PR = 7'h0;
		expected_PRF_mdu_req_B_valid = 1'b0;
		expected_PRF_mdu_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 6: ALU3 p12, p13:r, p14:r", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "dispatch0: v 4: MUL2 pC, pD:r, pE:r", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: i NOP", "\n\t\t",
            "IQ8: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: i NOP", "\n\t\t",
            "IQ3: v 3: ALU1 p9, pA:r, pB:r", "\n\t\t",
            "IQ2: v 2: MUL1 p6, p7:f, p8:r", "\n\t\t",
            "IQ1: v 1: MUL0 p3, p4:r, p5:r", "\n\t\t",
            "IQ0: v 0: ALU0 p0, p1:r, p2:f", "\n\t\t",
            "issue ALU Reg-Reg: v 3: ALU1 p9, pA:r, pB:r", "\n\t\t",
            "issue Mul-Div: v 1: MUL0 p3, p4:r, p5:r", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1011;
		tb_dispatch_valid_alu_reg_by_way = 4'b1010;
		tb_dispatch_valid_mdu_by_way = 4'b0001;
		tb_dispatch_op_by_way = {4'h3, 4'h0, 4'h2, 4'h2};
		tb_dispatch_A_PR_by_way = {7'h13, 7'h0, 7'h10, 7'hD};
		tb_dispatch_A_ready_by_way = 4'b1001;
		tb_dispatch_B_PR_by_way = {7'h14, 7'h0, 7'h11, 7'hE};
		tb_dispatch_B_ready_by_way = 4'b1001;
		tb_dispatch_dest_PR_by_way = {7'h12, 7'h0, 7'hF, 7'hC};
		tb_dispatch_ROB_index_by_way = {7'h6, 7'h0, 7'h5, 7'h4};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b1011;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b1;
		expected_issue_alu_reg_op = 4'h1;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h2;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h3;
		expected_issue_alu_reg_dest_PR = 7'h9;
		expected_issue_alu_reg_ROB_index = 7'h3;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b1;
		expected_PRF_alu_reg_req_A_PR = 7'hA;
		expected_PRF_alu_reg_req_B_valid = 1'b1;
		expected_PRF_alu_reg_req_B_PR = 7'hB;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b1;
		expected_issue_mdu_op = 4'h0;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h1;
		expected_issue_mdu_dest_PR = 7'h3;
		expected_issue_mdu_ROB_index = 7'h1;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b1;
		expected_PRF_mdu_req_A_PR = 7'h4;
		expected_PRF_mdu_req_B_valid = 1'b1;
		expected_PRF_mdu_req_B_PR = 7'h5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: v 9: MUL4 p1B, p1C:f, p1D:f", "\n\t\t",
            "dispatch1: v 8: MUL3 p18, p19:f, p1A:r", "\n\t\t",
            "dispatch0: v 7: ALU4 p15, p16:r, p17:f", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: i NOP", "\n\t\t",
            "IQ8: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: v 6: ALU3 p12, p13:r, p14:r", "\n\t\t",
            "IQ3: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "IQ2: v 4: MUL2 pC, pD:r, pE:r", "\n\t\t",
            "IQ1: v 2: MUL1 p6, p7:Fr, p8:r", "\n\t\t",
            "IQ0: v 0: ALU0 p0, p1:r, p2:f", "\n\t\t",
            "issue ALU Reg-Reg: v 6: ALU3 p12, p13:r, p14:r", "\n\t\t",
            "issue Mul-Div: i NOP", "\n\t\t",
			"activity: p7 WB, Mul-Div stall", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0111;
		tb_dispatch_valid_alu_reg_by_way = 4'b0001;
		tb_dispatch_valid_mdu_by_way = 4'b0110;
		tb_dispatch_op_by_way = {4'h0, 4'h4, 4'h3, 4'h4};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h1C, 7'h19, 7'h16};
		tb_dispatch_A_ready_by_way = 4'b0001;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h1D, 7'h1A, 7'h17};
		tb_dispatch_B_ready_by_way = 4'b0010;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h1B, 7'h18, 7'h15};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h9, 7'h8, 7'h7};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b0;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1000;
		tb_WB_bus_upper_PR_by_bank = {5'h1, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b0111;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b1;
		expected_issue_alu_reg_op = 4'h3;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h3;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h12;
		expected_issue_alu_reg_ROB_index = 7'h6;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b1;
		expected_PRF_alu_reg_req_A_PR = 7'h13;
		expected_PRF_alu_reg_req_B_valid = 1'b1;
		expected_PRF_alu_reg_req_B_PR = 7'h14;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b0;
		expected_issue_mdu_op = 4'h0;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h0;
		expected_issue_mdu_dest_PR = 7'h0;
		expected_issue_mdu_ROB_index = 7'h0;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b0;
		expected_PRF_mdu_req_A_PR = 7'h0;
		expected_PRF_mdu_req_B_valid = 1'b0;
		expected_PRF_mdu_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v D: ALU7 p27, p28:f, p29:f", "\n\t\t",
            "dispatch2: v C: MUL5 p24, p25:r, p26:f", "\n\t\t",
            "dispatch1: v B: ALU6 p21, p22:f, p23:f", "\n\t\t",
            "dispatch0: v A: ALU5 p1E, p1F:f, p20:r", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: i NOP", "\n\t\t",
            "IQ8: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: v 9: MUL4 p1B, p1C:f, p1D:f", "\n\t\t",
            "IQ5: v 8: MUL3 p18, p19:f, p1A:r", "\n\t\t",
            "IQ4: v 7: ALU4 p15, p16:r, p17:f", "\n\t\t",
            "IQ3: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "IQ2: v 4: MUL2 pC, pD:r, pE:r", "\n\t\t",
            "IQ1: v 2: MUL1 p6, p7:r, p8:r", "\n\t\t",
            "IQ0: v 0: ALU0 p0, p1:r, p2:F", "\n\t\t",
            "issue ALU Reg-Reg: v 0: ALU0 p0, p1:r, p2:F", "\n\t\t",
            "issue Mul-Div: v 2: MUL1 p6, p7:r, p8:r", "\n\t\t",
			"activity: p2 WB", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1111;
		tb_dispatch_valid_alu_reg_by_way = 4'b1011;
		tb_dispatch_valid_mdu_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'h7, 4'h5, 4'h6, 4'h5};
		tb_dispatch_A_PR_by_way = {7'h28, 7'h25, 7'h22, 7'h1F};
		tb_dispatch_A_ready_by_way = 4'b0100;
		tb_dispatch_B_PR_by_way = {7'h29, 7'h26, 7'h23, 7'h20};
		tb_dispatch_B_ready_by_way = 4'b0001;
		tb_dispatch_dest_PR_by_way = {7'h27, 7'h24, 7'h21, 7'h1E};
		tb_dispatch_ROB_index_by_way = {7'hD, 7'hC, 7'hB, 7'hA};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0100;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b1111;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b1;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h1;
		expected_issue_alu_reg_B_forward = 1'b1;
		expected_issue_alu_reg_B_bank = 2'h2;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b1;
		expected_PRF_alu_reg_req_A_PR = 7'h1;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h2;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b1;
		expected_issue_mdu_op = 4'h1;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h3;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h0;
		expected_issue_mdu_dest_PR = 7'h6;
		expected_issue_mdu_ROB_index = 7'h2;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b1;
		expected_PRF_mdu_req_A_PR = 7'h7;
		expected_PRF_mdu_req_B_valid = 1'b1;
		expected_PRF_mdu_req_B_PR = 7'h8;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: vi 11: ALU9 p33, p34:r, p35:r", "\n\t\t",
            "dispatch2: v 10: MUL7 p30, p31:r, p32:f", "\n\t\t",
            "dispatch1: v F: ALU8 p2D, p2E:f, p2F:r", "\n\t\t",
            "dispatch0: v E: MUL6 p2A, p2B:r, p2C:f", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: i NOP", "\n\t\t",
            "IQ8: v D: ALU7 p27, p28:f, p29:f", "\n\t\t",
            "IQ7: v C: MUL5 p24, p25:r, p26:f", "\n\t\t",
            "IQ6: v B: ALU6 p21, p22:f, p23:f", "\n\t\t",
            "IQ5: v A: ALU5 p1E, p1F:F, p20:r", "\n\t\t",
            "IQ4: v 9: MUL4 p1B, p1C:f, p1D:f", "\n\t\t",
            "IQ3: v 8: MUL3 p18, p19:f, p1A:r", "\n\t\t",
            "IQ2: v 7: ALU4 p15, p16:r, p17:f", "\n\t\t",
            "IQ1: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "IQ0: v 4: MUL2 pC, pD:r, pE:r", "\n\t\t",
            "issue ALU Reg-Reg: v A: ALU5 p1E, p1F:F, p20:r", "\n\t\t",
            "issue Mul-Div: v 4: MUL2 pC, pD:r, pE:r", "\n\t\t",
			"activity: p1F WB", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1111;
		tb_dispatch_valid_alu_reg_by_way = 4'b0010;
		tb_dispatch_valid_mdu_by_way = 4'b0101;
		tb_dispatch_op_by_way = {4'h9, 4'h7, 4'h8, 4'h6};
		tb_dispatch_A_PR_by_way = {7'h34, 7'h31, 7'h2E, 7'h2B};
		tb_dispatch_A_ready_by_way = 4'b1101;
		tb_dispatch_B_PR_by_way = {7'h35, 7'h32, 7'h2F, 7'h2C};
		tb_dispatch_B_ready_by_way = 4'b1010;
		tb_dispatch_dest_PR_by_way = {7'h33, 7'h30, 7'h2D, 7'h2A};
		tb_dispatch_ROB_index_by_way = {7'h11, 7'h10, 7'hF, 7'hE};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1000;
		tb_WB_bus_upper_PR_by_bank = {5'h7, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b1111;
		expected_dispatch_ack_by_way = 4'b0111;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b1;
		expected_issue_alu_reg_op = 4'h5;
		expected_issue_alu_reg_A_forward = 1'b1;
		expected_issue_alu_reg_A_bank = 2'h3;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h1E;
		expected_issue_alu_reg_ROB_index = 7'hA;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h1F;
		expected_PRF_alu_reg_req_B_valid = 1'b1;
		expected_PRF_alu_reg_req_B_PR = 7'h20;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b1;
		expected_issue_mdu_op = 4'h2;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h1;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h2;
		expected_issue_mdu_dest_PR = 7'hC;
		expected_issue_mdu_ROB_index = 7'h4;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b1;
		expected_PRF_mdu_req_A_PR = 7'hD;
		expected_PRF_mdu_req_B_valid = 1'b1;
		expected_PRF_mdu_req_B_PR = 7'hE;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 11: ALU9 p33, p34:r, p35:r", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: v 10: MUL7 p30, p31:r, p32:f", "\n\t\t",
            "IQ8: v F: ALU8 p2D, p2E:f, p2F:r", "\n\t\t",
            "IQ7: v E: MUL6 p2A, p2B:r, p2C:f", "\n\t\t",
            "IQ6: v D: ALU7 p27, p28:f, p29:f", "\n\t\t",
            "IQ5: v C: MUL5 p24, p25:r, p26:F", "\n\t\t",
            "IQ4: v B: ALU6 p21, p22:f, p23:f", "\n\t\t",
            "IQ3: v 9: MUL4 p1B, p1C:f, p1D:Fr", "\n\t\t",
            "IQ2: v 8: MUL3 p18, p19:f, p1A:r", "\n\t\t",
            "IQ1: v 7: ALU4 p15, p16:r, p17:f", "\n\t\t",
            "IQ0: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "issue ALU Reg-Reg: ", "\n\t\t",
            "issue Mul-Div: v C: MUL5 p24, p25:r, p26:F", "\n\t\t",
			"activity: p1D, p26 WB", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1000;
		tb_dispatch_valid_alu_reg_by_way = 4'b1000;
		tb_dispatch_valid_mdu_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'h9, 4'h0, 4'h0, 4'h0};
		tb_dispatch_A_PR_by_way = {7'h34, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1000;
		tb_dispatch_B_PR_by_way = {7'h35, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b1000;
		tb_dispatch_dest_PR_by_way = {7'h33, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h11, 7'h0, 7'h0, 7'h0};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0110;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h9, 5'h7, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b0011;
		expected_dispatch_ack_by_way = 4'b1000;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b0;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h0;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h0;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b1;
		expected_issue_mdu_op = 4'h5;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h1;
		expected_issue_mdu_B_forward = 1'b1;
		expected_issue_mdu_B_bank = 2'h2;
		expected_issue_mdu_dest_PR = 7'h24;
		expected_issue_mdu_ROB_index = 7'hC;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b1;
		expected_PRF_mdu_req_A_PR = 7'h25;
		expected_PRF_mdu_req_B_valid = 1'b0;
		expected_PRF_mdu_req_B_PR = 7'h26;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: vi 15: MULA p3F, p40:r, p41:r", "\n\t\t",
            "dispatch2: vi 14: MUL9 p3C, p3D:r, p3E:f", "\n\t\t",
            "dispatch1: v 13: MUL8 p39, p3A:r, p3B:f", "\n\t\t",
            "dispatch0: v 12: ALUA p36, p37:f, p38:r", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: i NOP", "\n\t\t",
            "IQ9: v 11: ALU9 p33, p34:r, p35:r", "\n\t\t",
            "IQ8: v 10: MUL7 p30, p31:r, p32:f", "\n\t\t",
            "IQ7: v F: ALU8 p2D, p2E:f, p2F:r", "\n\t\t",
            "IQ6: v E: MUL6 p2A, p2B:r, p2C:f", "\n\t\t",
            "IQ5: v D: ALU7 p27, p28:f, p29:f", "\n\t\t",
            "IQ4: v B: ALU6 p21, p22:f, p23:f", "\n\t\t",
            "IQ3: v 9: MUL4 p1B, p1C:Fr, p1D:r", "\n\t\t",
            "IQ2: v 8: MUL3 p18, p19:F, p1A:r", "\n\t\t",
            "IQ1: v 7: ALU4 p15, p16:r, p17:f", "\n\t\t",
            "IQ0: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "issue ALU Reg-Reg: i NOP", "\n\t\t",
            "issue Mul-Div: v 8: MUL3 p18, p19:F, p1A:r", "\n\t\t",
			"activity: p19, p1C WB, ALU pipeline stall", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1111;
		tb_dispatch_valid_alu_reg_by_way = 4'b0001;
		tb_dispatch_valid_mdu_by_way = 4'b0110;
		tb_dispatch_op_by_way = {4'hA, 4'h9, 4'h8, 4'hA};
		tb_dispatch_A_PR_by_way = {7'h40, 7'h3D, 7'h3A, 7'h37};
		tb_dispatch_A_ready_by_way = 4'b1110;
		tb_dispatch_B_PR_by_way = {7'h41, 7'h3E, 7'h3B, 7'h38};
		tb_dispatch_B_ready_by_way = 4'b1001;
		tb_dispatch_dest_PR_by_way = {7'h3F, 7'h3C, 7'h39, 7'h36};
		tb_dispatch_ROB_index_by_way = {7'h15, 7'h14, 7'h13, 7'h12};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b0;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0011;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h6, 5'h7};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b0011;
		expected_dispatch_ack_by_way = 4'b0011;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b0;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h0;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h0;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b1;
		expected_issue_mdu_op = 4'h3;
		expected_issue_mdu_A_forward = 1'b1;
		expected_issue_mdu_A_bank = 2'h1;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h2;
		expected_issue_mdu_dest_PR = 7'h18;
		expected_issue_mdu_ROB_index = 7'h8;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b0;
		expected_PRF_mdu_req_A_PR = 7'h19;
		expected_PRF_mdu_req_B_valid = 1'b1;
		expected_PRF_mdu_req_B_PR = 7'h1A;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: vi 15: MULA p3F, p40:r, p41:r", "\n\t\t",
            "dispatch2: v 14: MUL9 p3C, p3D:r, p3E:f", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQB: i NOP", "\n\t\t",
            "IQA: v 13: MUL8 p39, p3A:r, p3B:f", "\n\t\t",
            "IQ9: v 12: ALUA p36, p37:f, p38:r", "\n\t\t",
            "IQ8: v 11: ALU9 p33, p34:r, p35:r", "\n\t\t",
            "IQ7: v 10: MUL7 p30, p31:r, p32:f", "\n\t\t",
            "IQ6: v F: ALU8 p2D, p2E:f, p2F:r", "\n\t\t",
            "IQ5: v E: MUL6 p2A, p2B:r, p2C:f", "\n\t\t",
            "IQ4: v D: ALU7 p27, p28:f, p29:f", "\n\t\t",
            "IQ3: v B: ALU6 p21, p22:f, p23:f", "\n\t\t",
            "IQ2: v 9: MUL4 p1B, p1C:r, p1D:r", "\n\t\t",
            "IQ1: v 7: ALU4 p15, p16:r, p17:f", "\n\t\t",
            "IQ0: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "issue ALU Reg-Reg: i NOP", "\n\t\t",
            "issue Mul-Div: i NOP", "\n\t\t",
			"activity: ALU pipeline stall, Mul-Div pipeline stall", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1100;
		tb_dispatch_valid_alu_reg_by_way = 4'b0000;
		tb_dispatch_valid_mdu_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'hA, 4'h9, 4'h0, 4'h0};
		tb_dispatch_A_PR_by_way = {7'h40, 7'h3D, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1100;
		tb_dispatch_B_PR_by_way = {7'h41, 7'h3E, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b1000;
		tb_dispatch_dest_PR_by_way = {7'h3F, 7'h3C, 7'h0, 7'h30};
		tb_dispatch_ROB_index_by_way = {7'h15, 7'h14, 7'h0, 7'h0};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b0;
		tb_mdu_pipeline_ready = 1'b0;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b0001;
		expected_dispatch_ack_by_way = 4'b0100;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b0;
		expected_issue_alu_reg_op = 4'h0;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h0;
		expected_issue_alu_reg_dest_PR = 7'h0;
		expected_issue_alu_reg_ROB_index = 7'h0;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b0;
		expected_PRF_alu_reg_req_A_PR = 7'h0;
		expected_PRF_alu_reg_req_B_valid = 1'b0;
		expected_PRF_alu_reg_req_B_PR = 7'h0;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b0;
		expected_issue_mdu_op = 4'h0;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h0;
		expected_issue_mdu_dest_PR = 7'h0;
		expected_issue_mdu_ROB_index = 7'h0;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b0;
		expected_PRF_mdu_req_A_PR = 7'h0;
		expected_PRF_mdu_req_B_valid = 1'b0;
		expected_PRF_mdu_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: vi 15: MULA p3F, p40:r, p41:r", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQB: v 14: MUL9 p3C, p3D:r, p3E:f", "\n\t\t",
            "IQA: v 13: MUL8 p39, p3A:r, p3B:f", "\n\t\t",
            "IQ9: v 12: ALUA p36, p37:f, p38:r", "\n\t\t",
            "IQ8: v 11: ALU9 p33, p34:r, p35:r", "\n\t\t",
            "IQ7: v 10: MUL7 p30, p31:r, p32:f", "\n\t\t",
            "IQ6: v F: ALU8 p2D, p2E:f, p2F:r", "\n\t\t",
            "IQ5: v E: MUL6 p2A, p2B:r, p2C:f", "\n\t\t",
            "IQ4: v D: ALU7 p27, p28:f, p29:f", "\n\t\t",
            "IQ3: v B: ALU6 p21, p22:f, p23:f", "\n\t\t",
            "IQ2: v 9: MUL4 p1B, p1C:r, p1D:r", "\n\t\t",
            "IQ1: v 7: ALU4 p15, p16:r, p17:f", "\n\t\t",
            "IQ0: v 5: ALU2 pF, p10:f, p11:f", "\n\t\t",
            "issue ALU Reg-Reg: v 11: ALU9 p33, p34:r, p35:r", "\n\t\t",
            "issue Mul-Div: v 9: MUL4 p1B, p1C:r, p1D:r", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1000;
		tb_dispatch_valid_alu_reg_by_way = 4'b0000;
		tb_dispatch_valid_mdu_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'hA, 4'h0, 4'h0, 4'h0};
		tb_dispatch_A_PR_by_way = {7'h40, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1000;
		tb_dispatch_B_PR_by_way = {7'h41, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b1000;
		tb_dispatch_dest_PR_by_way = {7'h3F, 7'h0, 7'h0, 7'h30};
		tb_dispatch_ROB_index_by_way = {7'h15, 7'h0, 7'h0, 7'h0};
	    // ALU op dispatch feedback
	    // pipeline feedback
		tb_alu_reg_pipeline_ready = 1'b1;
		tb_mdu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op issue to ALU Reg-Reg pipeline
	    // ALU Reg-Reg pipeline reg read req to PRF
	    // op issue to Mul-Div pipeline
	    // Mul-Div pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // ALU op dispatch feedback
		// expected_dispatch_ready_advertisement_by_way = 4'b0000;
		expected_dispatch_ack_by_way = 4'b0000;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Reg pipeline
		expected_issue_alu_reg_valid = 1'b1;
		expected_issue_alu_reg_op = 4'h9;
		expected_issue_alu_reg_A_forward = 1'b0;
		expected_issue_alu_reg_A_bank = 2'h0;
		expected_issue_alu_reg_B_forward = 1'b0;
		expected_issue_alu_reg_B_bank = 2'h1;
		expected_issue_alu_reg_dest_PR = 7'h33;
		expected_issue_alu_reg_ROB_index = 7'h11;
	    // ALU Reg-Reg pipeline reg read req to PRF
		expected_PRF_alu_reg_req_A_valid = 1'b1;
		expected_PRF_alu_reg_req_A_PR = 7'h34;
		expected_PRF_alu_reg_req_B_valid = 1'b1;
		expected_PRF_alu_reg_req_B_PR = 7'h35;
	    // op issue to Mul-Div pipeline
		expected_issue_mdu_valid = 1'b1;
		expected_issue_mdu_op = 4'h4;
		expected_issue_mdu_A_forward = 1'b0;
		expected_issue_mdu_A_bank = 2'h0;
		expected_issue_mdu_B_forward = 1'b0;
		expected_issue_mdu_B_bank = 2'h1;
		expected_issue_mdu_dest_PR = 7'h1B;
		expected_issue_mdu_ROB_index = 7'h9;
	    // Mul-Div pipeline reg read req to PRF
		expected_PRF_mdu_req_A_valid = 1'b1;
		expected_PRF_mdu_req_A_PR = 7'h1C;
		expected_PRF_mdu_req_B_valid = 1'b1;
		expected_PRF_mdu_req_B_PR = 7'h1D;

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