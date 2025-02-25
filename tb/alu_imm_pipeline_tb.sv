/*
    Filename: alu_imm_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_imm_pipeline module. 
    Spec: LOROF/spec/design/alu_imm_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_pipeline_tb ();

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


    // ALU imm op issue from IQ
	logic tb_issue_valid;
	logic [3:0] tb_issue_op;
	logic [11:0] tb_issue_imm12;
	logic tb_issue_A_forward;
	logic tb_issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_A_bank;
	logic [LOG_PR_COUNT-1:0] tb_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_issue_ROB_index;

    // ready feedback to IQ
	logic DUT_issue_ready, expected_issue_ready;

    // reg read info and data from PRF
	logic tb_A_reg_read_ack;
	logic tb_A_reg_read_port;
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] tb_reg_read_data_by_bank_by_port;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_forward_data_by_bank;

    // writeback data to PRF
	logic DUT_WB_valid, expected_WB_valid;
	logic [31:0] DUT_WB_data, expected_WB_data;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR, expected_WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_WB_ROB_index, expected_WB_ROB_index;

    // writeback backpressure from PRF
	logic tb_WB_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_imm_pipeline DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // ALU imm op issue from IQ
		.issue_valid(tb_issue_valid),
		.issue_op(tb_issue_op),
		.issue_imm12(tb_issue_imm12),
		.issue_A_forward(tb_issue_A_forward),
		.issue_A_is_zero(tb_issue_A_is_zero),
		.issue_A_bank(tb_issue_A_bank),
		.issue_dest_PR(tb_issue_dest_PR),
		.issue_ROB_index(tb_issue_ROB_index),

	    // ready feedback to IQ
		.issue_ready(DUT_issue_ready),

	    // reg read info and data from PRF
		.A_reg_read_ack(tb_A_reg_read_ack),
		.A_reg_read_port(tb_A_reg_read_port),
		.reg_read_data_by_bank_by_port(tb_reg_read_data_by_bank_by_port),

	    // forward data from PRF
		.forward_data_by_bank(tb_forward_data_by_bank),

	    // writeback data to PRF
		.WB_valid(DUT_WB_valid),
		.WB_data(DUT_WB_data),
		.WB_PR(DUT_WB_PR),
		.WB_ROB_index(DUT_WB_ROB_index),

	    // writeback backpressure from PRF
		.WB_ready(tb_WB_ready)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_issue_ready !== DUT_issue_ready) begin
			$display("TB ERROR: expected_issue_ready (%h) != DUT_issue_ready (%h)",
				expected_issue_ready, DUT_issue_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_valid !== DUT_WB_valid) begin
			$display("TB ERROR: expected_WB_valid (%h) != DUT_WB_valid (%h)",
				expected_WB_valid, DUT_WB_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_data !== DUT_WB_data) begin
			$display("TB ERROR: expected_WB_data (%h) != DUT_WB_data (%h)",
				expected_WB_data, DUT_WB_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_PR !== DUT_WB_PR) begin
			$display("TB ERROR: expected_WB_PR (%h) != DUT_WB_PR (%h)",
				expected_WB_PR, DUT_WB_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_ROB_index !== DUT_WB_ROB_index) begin
			$display("TB ERROR: expected_WB_ROB_index (%h) != DUT_WB_ROB_index (%h)",
				expected_WB_ROB_index, DUT_WB_ROB_index);
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
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h0;
		tb_issue_ROB_index = 7'h0;
	    // ready feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = '0;
	    // forward data from PRF
		tb_forward_data_by_bank = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h0;
		tb_issue_ROB_index = 7'h0;
	    // ready feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = '0;
	    // forward data from PRF
		tb_forward_data_by_bank = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF

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
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h0;
		tb_issue_ROB_index = 7'h0;
	    // ready feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = '0;
	    // forward data from PRF
		tb_forward_data_by_bank = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF

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