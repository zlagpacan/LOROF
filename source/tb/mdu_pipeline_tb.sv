/*
    Filename: mdu_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for mdu_pipeline module. 
    Spec: LOROF/spec/design/mdu_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module mdu_pipeline_tb #(
	parameter IS_OC_BUFFER_SIZE = 2,
	parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3,
	parameter MDU_RESULT_CACHE_ENTRIES = 4,
	parameter LOG_MDU_RESULT_CACHE_ENTRIES = $clog2(MDU_RESULT_CACHE_ENTRIES)
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


    // MDU pipeline issue
	logic tb_issue_valid;
	logic [2:0] tb_issue_op;
	logic tb_issue_A_forward;
	logic tb_issue_A_is_zero;
	logic [LOG_PR_COUNT-1:0] tb_issue_A_PR;
	logic tb_issue_B_forward;
	logic tb_issue_B_is_zero;
	logic [LOG_PR_COUNT-1:0] tb_issue_B_PR;
	logic [LOG_PR_COUNT-1:0] tb_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_issue_ROB_index;

    // MDU pipeline feedback to IQ
	logic DUT_issue_ready, expected_issue_ready;

    // reg read data from PRF
	logic tb_A_reg_read_resp_valid;
	logic [31:0] tb_A_reg_read_resp_data;
	logic tb_B_reg_read_resp_valid;
	logic [31:0] tb_B_reg_read_resp_data;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_forward_data_by_bank;

    // writeback data to PRF
	logic DUT_WB_valid, expected_WB_valid;
	logic [31:0] DUT_WB_data, expected_WB_data;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR, expected_WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_WB_ROB_index, expected_WB_ROB_index;

    // writeback feedback from
	logic tb_WB_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	mdu_pipeline #(
		.IS_OC_BUFFER_SIZE(IS_OC_BUFFER_SIZE),
		.PRF_RR_OUTPUT_BUFFER_SIZE(PRF_RR_OUTPUT_BUFFER_SIZE),
		.MDU_RESULT_CACHE_ENTRIES(MDU_RESULT_CACHE_ENTRIES),
		.LOG_MDU_RESULT_CACHE_ENTRIES(LOG_MDU_RESULT_CACHE_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // MDU pipeline issue
		.issue_valid(tb_issue_valid),
		.issue_op(tb_issue_op),
		.issue_A_forward(tb_issue_A_forward),
		.issue_A_is_zero(tb_issue_A_is_zero),
		.issue_A_PR(tb_issue_A_PR),
		.issue_B_forward(tb_issue_B_forward),
		.issue_B_is_zero(tb_issue_B_is_zero),
		.issue_B_PR(tb_issue_B_PR),
		.issue_dest_PR(tb_issue_dest_PR),
		.issue_ROB_index(tb_issue_ROB_index),

	    // MDU pipeline feedback to IQ
		.issue_ready(DUT_issue_ready),

	    // reg read data from PRF
		.A_reg_read_resp_valid(tb_A_reg_read_resp_valid),
		.A_reg_read_resp_data(tb_A_reg_read_resp_data),
		.B_reg_read_resp_valid(tb_B_reg_read_resp_valid),
		.B_reg_read_resp_data(tb_B_reg_read_resp_data),

	    // forward data from PRF
		.forward_data_by_bank(tb_forward_data_by_bank),

	    // writeback data to PRF
		.WB_valid(DUT_WB_valid),
		.WB_data(DUT_WB_data),
		.WB_PR(DUT_WB_PR),
		.WB_ROB_index(DUT_WB_ROB_index),

	    // writeback feedback from
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
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback feedback from

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback feedback from

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 0",
            "\n\t\tIS:      MUL p3, p1:r, p2:r @ ri4",
            "\n\t\tISBUF1: ",
            "\n\t\tISBUF0: ",
            "\n\t\tOC: ",
            "\n\t\tEX: ",
            "\n\t\tWB: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h01;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h02;
		tb_issue_dest_PR = 7'h03;
		tb_issue_ROB_index = 7'h04;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 1",
            "\n\t\tIS:      MULH p7, p5:f, p6:r @ ri8",
            "\n\t\tISBUF1: ",
            "\n\t\tISBUF0:  MUL p3, p1:r, p2:rR @ ri4",
            "\n\t\tOC:      MUL p3, p1:r, p2:rR @ ri4",
            "\n\t\tEX: ",
            "\n\t\tWB: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b001;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h05;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h06;
		tb_issue_dest_PR = 7'h07;
		tb_issue_ROB_index = 7'h08;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b1;
		tb_B_reg_read_resp_data = 32'hD2D2D2D2;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 2",
            "\n\t\tIS:      MULHSU pB, p9:r, pA:f @ riC",
            "\n\t\tISBUF1:  MULH p7, p5:fF, p6:rR @ ri8",
            "\n\t\tISBUF0:  MUL p3, p1:r, p2:R @ ri4",
            "\n\t\tOC:      MUL p3, p1:r, p2:R @ ri4",
            "\n\t\tEX: ",
            "\n\t\tWB: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b010;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h09;
		tb_issue_B_forward = 1'b1;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h0A;
		tb_issue_dest_PR = 7'h0B;
		tb_issue_ROB_index = 7'h0C;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b1;
		tb_B_reg_read_resp_data = 32'h96969696;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'hA5A5A5A5,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 3",
            "\n\t\tIS:      MULHSU pB, p9:r, pA:f @ riC",
            "\n\t\tISBUF1:  MULH p7, p5:F, p6:R @ ri8",
            "\n\t\tISBUF0:  MUL p3, p1:rR, p2:R @ ri4",
            "\n\t\tOC:      MUL p3, p1:rR, p2:R @ ri4",
            "\n\t\tEX: ",
            "\n\t\tWB: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b010;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h09;
		tb_issue_B_forward = 1'b1;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h0A;
		tb_issue_dest_PR = 7'h0B;
		tb_issue_ROB_index = 7'h0C;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hE1E1E1E1;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h03;
		expected_WB_ROB_index = 7'h04;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 4",
            "\n\t\tIS:      MULHSU pB, p9:r, pA:f @ riC",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  MULH p7, p5:F, p6:R @ ri8",
            "\n\t\tOC:      MULH p7, p5:F, p6:R @ ri8",
            "\n\t\tEX:      MUL p3, p1:R, p2:R @ ri4",
            "\n\t\tWB: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b010;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h09;
		tb_issue_B_forward = 1'b1;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h0A;
		tb_issue_dest_PR = 7'h0B;
		tb_issue_ROB_index = 7'h0C;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h03;
		expected_WB_ROB_index = 7'h04;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 5",
            "\n\t\tIS:      MULHU pF, pD:f, pE:f @ ri10",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  MULHSU pB, p9:r, pA:fF @ riC",
            "\n\t\tOC:      MULHSU pB, p9:r, pA:fF @ riC",
            "\n\t\tEX:      MULH p7, p5:F, p6:R @ ri8",
            "\n\t\tWB:      MUL p3, p1:R, p2:R @ ri4"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b011;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h0D;
		tb_issue_B_forward = 1'b1;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h0E;
		tb_issue_dest_PR = 7'h0F;
		tb_issue_ROB_index = 7'h10;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h5A5A5A5A,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h7327dc92;
		expected_WB_PR = 7'h03;
		expected_WB_ROB_index = 7'h04;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 6",
            "\n\t\tIS:      DIV p13, p11:z, p12:r @ ri14",
            "\n\t\tISBUF1:  MULHU pF, pD:fF, pE:fF @ ri10",
            "\n\t\tISBUF0:  MULHSU pB, p9:r, pA:F @ riC",
            "\n\t\tOC:      MULHSU pB, p9:r, pA:F @ riC",
            "\n\t\tEX:      ",
            "\n\t\tWB:      MULH p7, p5:F, p6:R @ ri8"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b100;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b1;
		tb_issue_A_PR = 7'h11;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h12;
		tb_issue_dest_PR = 7'h13;
		tb_issue_ROB_index = 7'h14;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h1E1E1E1E,
            32'h2D2D2D2D,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h25344352;
		expected_WB_PR = 7'h07;
		expected_WB_ROB_index = 7'h08;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 7",
            "\n\t\tIS:      DIV p13, p11:z, p12:r @ ri14",
            "\n\t\tISBUF1:  MULHU pF, pD:F, pE:F @ ri10",
            "\n\t\tISBUF0:  MULHSU pB, p9:rR, pA:F @ riC",
            "\n\t\tOC:      MULHSU pB, p9:rR, pA:F @ riC",
            "\n\t\tEX:      ",
            "\n\t\tWB:      "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b100;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b1;
		tb_issue_A_PR = 7'h11;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h12;
		tb_issue_dest_PR = 7'h13;
		tb_issue_ROB_index = 7'h14;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hFFFFFFF7;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h0B;
		expected_WB_ROB_index = 7'h0C;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 8",
            "\n\t\tIS:      DIV p13, p11:z, p12:r @ ri14",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  MULHU pF, pD:F, pE:F @ ri10",
            "\n\t\tOC:      MULHU pF, pD:F, pE:F @ ri10",
            "\n\t\tEX:      MULHSU pB, p9:R, pA:F @ riC",
            "\n\t\tWB:      "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b100;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b1;
		tb_issue_A_PR = 7'h11;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h12;
		tb_issue_dest_PR = 7'h13;
		tb_issue_ROB_index = 7'h14;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h0B;
		expected_WB_ROB_index = 7'h0C;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 9",
            "\n\t\tIS:      DIVU p17, p15:r, p16:f @ ri18",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  DIV p13, p11:z, p12:rR @ ri14",
            "\n\t\tOC:      DIV p13, p11:z, p12:rR @ ri14",
            "\n\t\tEX:      MULHU pF, pD:F, pE:F @ ri10",
            "\n\t\tWB:      MULHSU pB, p9:R, pA:F @ riC"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b101;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h15;
		tb_issue_B_forward = 1'b1;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h16;
		tb_issue_dest_PR = 7'h17;
		tb_issue_ROB_index = 7'h18;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b1;
		tb_B_reg_read_resp_data = 32'hED12ED12;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hFFFFFFFC;
		expected_WB_PR = 7'h0B;
		expected_WB_ROB_index = 7'h0C;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle A",
            "\n\t\tIS:      REMU p1B, p15:r, p16:r @ ri1C",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  DIVU p17, p15:rR, p16:fF @ ri18",
            "\n\t\tOC:      DIVU p17, p15:rR, p16:fF @ ri18",
            "\n\t\tEX:      DIV p13, p11:z, p12:R @ ri14",
            "\n\t\tWB:      MULHU pF, pD:F, pE:F @ ri10"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b111;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h15;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h16;
		tb_issue_dest_PR = 7'h1B;
		tb_issue_ROB_index = 7'h1C;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hEA15EA15;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'hE916E916,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h05509be7;
		expected_WB_PR = 7'h0F;
		expected_WB_ROB_index = 7'h10;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle B",
            "\n\t\tIS:      REM p1F, p1D:r, p1E:z @ ri20",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  REMU p1B, p19:rR, p1A:rR @ ri1C",
            "\n\t\tOC:      REMU p1B, p15:rR, p16:rR @ ri1C",
            "\n\t\tEX:      DIVU p17, p15:R, p16:F @ ri18",
            "\n\t\tWB:      DIV p13, p11:z, p12:R @ ri14"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b110;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h1D;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b1;
		tb_issue_B_PR = 7'h1E;
		tb_issue_dest_PR = 7'h1F;
		tb_issue_ROB_index = 7'h20;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hDEADDEAD; // should be ignored
		tb_B_reg_read_resp_valid = 1'b1;
		tb_B_reg_read_resp_data = 32'hBEEFBEEF; // should be ignored
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h2d2d2d2d;
		expected_WB_PR = 7'h13;
		expected_WB_ROB_index = 7'h14;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle C",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  REM p1F, p1D:rR, p1E:z @ ri20",
            "\n\t\tISBUF0:  REMU p1B, p19:R, p1A:R @ ri1C",
            "\n\t\tOC:      REMU p1B, p15:R, p16:R @ ri1C",
            "\n\t\tEX:      DIVU p17, p15:R, p16:F @ ri18",
            "\n\t\tWB:      DIV p13, p11:z, p12:R @ ri14"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hE21DE21D;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h13;
		expected_WB_ROB_index = 7'h14;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle D",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  REM p1F, p1D:R, p1E:z @ ri20",
            "\n\t\tISBUF0:  REMU p1B, p19:R, p1A:R @ ri1C",
            "\n\t\tOC:      REMU p1B, p15:R, p16:R @ ri1C",
            "\n\t\tEX:      DIVU p17, p15:R, p16:F @ ri18",
            "\n\t\tWB:      DIV p13, p11:z, p12:R @ ri14"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h13;
		expected_WB_ROB_index = 7'h14;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle E",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  REM p1F, p1D:R, p1E:z @ ri20",
            "\n\t\tOC:      REM p1F, p1D:R, p1E:z @ ri20",
            "\n\t\tEX:      REMU p1B, p15:R, p16:R @ ri1C",
            "\n\t\tWB:      DIVU p17, p15:R, p16:F @ ri18"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h17;
		expected_WB_ROB_index = 7'h18;
	    // writeback feedback from

		check_outputs();

        for (int i = 'hF; i < 'h30; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = {
                $sformatf("simple cycle %2h (outputs ignored)", i),
                "\n\t\tIS:      ",
                "\n\t\tISBUF1:  ",
                "\n\t\tISBUF0:  REM p1F, p1D:R, p1E:z @ ri20",
                "\n\t\tOC:      REM p1F, p1D:R, p1E:z @ ri20",
                "\n\t\tEX:      REMU p1B, p15:R, p16:R @ ri1C",
                "\n\t\tWB:      DIVU p17, p15:R, p16:F @ ri18"
            };
            $display("\t- sub_test: %s", sub_test_case);
        end

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 30",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  REM p1F, p1D:R, p1E:z @ ri20",
            "\n\t\tOC:      REM p1F, p1D:R, p1E:z @ ri20",
            "\n\t\tEX:      REMU p1B, p15:R, p16:R @ ri1C",
            "\n\t\tWB:      DIVU p17, p15:R, p16:F @ ri18"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h00000001;
		expected_WB_PR = 7'h17;
		expected_WB_ROB_index = 7'h18;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 31",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  ",
            "\n\t\tOC:      ",
            "\n\t\tEX:      REM p1F, p1D:R, p1E:z @ ri20",
            "\n\t\tWB:      REMU p1B, p15:R, p16:R @ ri1C"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h00FF00FF;
		expected_WB_PR = 7'h1B;
		expected_WB_ROB_index = 7'h1C;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 32",
            "\n\t\tIS:      DIV p23, p1D:r, p1E:f @ ri24",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  ",
            "\n\t\tOC:      ",
            "\n\t\tEX:      ",
            "\n\t\tWB:      REM p1F, p1D:R, p1E:z @ ri20"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b1;
		tb_issue_op = 3'b100;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h1D;
		tb_issue_B_forward = 1'b1;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h1E;
		tb_issue_dest_PR = 7'h23;
		tb_issue_ROB_index = 7'h24;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h1F;
		expected_WB_ROB_index = 7'h20;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 33",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  DIV p23, p1D:rR, p1E:fF @ ri24",
            "\n\t\tOC:      DIV p23, p1D:rR, p1E:fF @ ri24",
            "\n\t\tEX:      ",
            "\n\t\tWB:      REM p1F, p1D:R, p1E:z @ ri20"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hDEADBEEF;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'hBEEFDEAD,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h1F;
		expected_WB_ROB_index = 7'h20;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 34",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  ",
            "\n\t\tOC:      ",
            "\n\t\tEX:      DIV p23, p1D:R, p1E:F @ ri24",
            "\n\t\tWB:      REM p1F, p1D:R, p1E:z @ ri20"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hE21DE21D;
		expected_WB_PR = 7'h1F;
		expected_WB_ROB_index = 7'h20;
	    // writeback feedback from

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "simple cycle 35",
            "\n\t\tIS:      ",
            "\n\t\tISBUF1:  ",
            "\n\t\tISBUF0:  ",
            "\n\t\tOC:      ",
            "\n\t\tEX:      ",
            "\n\t\tWB:      DIV p23, p1D:R, p1E:F @ ri24"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // MDU pipeline issue
		tb_issue_valid = 1'b0;
		tb_issue_op = 3'b000;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_PR = 7'h00;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_PR = 7'h00;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // MDU pipeline feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
		tb_B_reg_read_resp_valid = 1'b0;
		tb_B_reg_read_resp_data = 32'h00000000;
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback feedback from
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // MDU pipeline issue
	    // MDU pipeline feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hFFFFFFFF;
		expected_WB_PR = 7'h23;
		expected_WB_ROB_index = 7'h24;
	    // writeback feedback from

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