/*
    Filename: alu_imm_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_imm_pipeline module. 
    Spec: LOROF/spec/design/alu_imm_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module alu_imm_pipeline_tb #(
	parameter IS_OC_BUFFER_SIZE = 2,
	parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3,
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


    // ALU imm op issue from IQ
	logic tb_issue_valid;
	logic [3:0] tb_issue_op;
	logic [11:0] tb_issue_imm12;
	logic tb_issue_A_is_reg;
	logic tb_issue_A_is_bus_forward;
	logic tb_issue_A_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] tb_issue_A_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_A_bank;
	logic [LOG_PR_COUNT-1:0] tb_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_issue_ROB_index;

    // ready feedback to IQ
	logic DUT_issue_ready, expected_issue_ready;

    // reg read data from PRF
	logic tb_A_reg_read_resp_valid;
	logic [31:0] tb_A_reg_read_resp_data;

    // bus forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_bus_forward_data_by_bank;

    // fast forward data
	logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] tb_fast_forward_data_by_pipe;

    // writeback data to PRF
	logic DUT_WB_valid, expected_WB_valid;
	logic [31:0] DUT_WB_data, expected_WB_data;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR, expected_WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_WB_ROB_index, expected_WB_ROB_index;

    // writeback backpressure from PRF
	logic tb_WB_ready;

    // this pipe's fast forward notif
	logic DUT_pipe_fast_forward_notif_valid, expected_pipe_fast_forward_notif_valid;
	logic [LOG_PR_COUNT-1:0] DUT_pipe_fast_forward_notif_PR, expected_pipe_fast_forward_notif_PR;

	logic DUT_pipe_fast_forward_data_valid, expected_pipe_fast_forward_data_valid;
	logic [31:0] DUT_pipe_fast_forward_data, expected_pipe_fast_forward_data;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_imm_pipeline #(
		.IS_OC_BUFFER_SIZE(IS_OC_BUFFER_SIZE),
		.PRF_RR_OUTPUT_BUFFER_SIZE(PRF_RR_OUTPUT_BUFFER_SIZE),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // ALU imm op issue from IQ
		.issue_valid(tb_issue_valid),
		.issue_op(tb_issue_op),
		.issue_imm12(tb_issue_imm12),
		.issue_A_is_reg(tb_issue_A_is_reg),
		.issue_A_is_bus_forward(tb_issue_A_is_bus_forward),
		.issue_A_is_fast_forward(tb_issue_A_is_fast_forward),
		.issue_A_fast_forward_pipe(tb_issue_A_fast_forward_pipe),
		.issue_A_bank(tb_issue_A_bank),
		.issue_dest_PR(tb_issue_dest_PR),
		.issue_ROB_index(tb_issue_ROB_index),

	    // ready feedback to IQ
		.issue_ready(DUT_issue_ready),

	    // reg read data from PRF
		.A_reg_read_resp_valid(tb_A_reg_read_resp_valid),
		.A_reg_read_resp_data(tb_A_reg_read_resp_data),

	    // bus forward data from PRF
		.bus_forward_data_by_bank(tb_bus_forward_data_by_bank),

	    // fast forward data
		.fast_forward_data_by_pipe(tb_fast_forward_data_by_pipe),

	    // writeback data to PRF
		.WB_valid(DUT_WB_valid),
		.WB_data(DUT_WB_data),
		.WB_PR(DUT_WB_PR),
		.WB_ROB_index(DUT_WB_ROB_index),

	    // writeback backpressure from PRF
		.WB_ready(tb_WB_ready),

	    // this pipe's fast forward notif
		.pipe_fast_forward_notif_valid(DUT_pipe_fast_forward_notif_valid),
		.pipe_fast_forward_notif_PR(DUT_pipe_fast_forward_notif_PR),

		.pipe_fast_forward_data_valid(DUT_pipe_fast_forward_data_valid),
		.pipe_fast_forward_data(DUT_pipe_fast_forward_data)
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

		if (expected_pipe_fast_forward_notif_valid !== DUT_pipe_fast_forward_notif_valid) begin
			$display("TB ERROR: expected_pipe_fast_forward_notif_valid (%h) != DUT_pipe_fast_forward_notif_valid (%h)",
				expected_pipe_fast_forward_notif_valid, DUT_pipe_fast_forward_notif_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pipe_fast_forward_notif_PR !== DUT_pipe_fast_forward_notif_PR) begin
			$display("TB ERROR: expected_pipe_fast_forward_notif_PR (%h) != DUT_pipe_fast_forward_notif_PR (%h)",
				expected_pipe_fast_forward_notif_PR, DUT_pipe_fast_forward_notif_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pipe_fast_forward_data_valid !== DUT_pipe_fast_forward_data_valid) begin
			$display("TB ERROR: expected_pipe_fast_forward_data_valid (%h) != DUT_pipe_fast_forward_data_valid (%h)",
				expected_pipe_fast_forward_data_valid, DUT_pipe_fast_forward_data_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pipe_fast_forward_data !== DUT_pipe_fast_forward_data) begin
			$display("TB ERROR: expected_pipe_fast_forward_data (%h) != DUT_pipe_fast_forward_data (%h)",
				expected_pipe_fast_forward_data, DUT_pipe_fast_forward_data);
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
		tb_issue_valid = '0;
		tb_issue_op = '0;
		tb_issue_imm12 = '0;
		tb_issue_A_is_reg = '0;
		tb_issue_A_is_bus_forward = '0;
		tb_issue_A_is_fast_forward = '0;
		tb_issue_A_fast_forward_pipe = '0;
		tb_issue_A_bank = '0;
		tb_issue_dest_PR = '0;
		tb_issue_ROB_index = '0;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = '0;
		tb_A_reg_read_resp_data = '0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = '0;
	    // fast forward data
		tb_fast_forward_data_by_pipe = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = '0;
	    // this pipe's fast forward notif

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = '0;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = '0;
		expected_WB_data = '0;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = '0;
		expected_pipe_fast_forward_notif_PR = '0;
		expected_pipe_fast_forward_data_valid = '0;
		expected_pipe_fast_forward_data = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = '0;
		tb_issue_op = '0;
		tb_issue_imm12 = '0;
		tb_issue_A_is_reg = '0;
		tb_issue_A_is_bus_forward = '0;
		tb_issue_A_is_fast_forward = '0;
		tb_issue_A_fast_forward_pipe = '0;
		tb_issue_A_bank = '0;
		tb_issue_dest_PR = '0;
		tb_issue_ROB_index = '0;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = '0;
		tb_A_reg_read_resp_data = '0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = '0;
	    // fast forward data
		tb_fast_forward_data_by_pipe = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = '0;
	    // this pipe's fast forward notif

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = '0;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = '0;
		expected_WB_data = '0;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = '0;
		expected_pipe_fast_forward_notif_PR = '0;
		expected_pipe_fast_forward_data_valid = '0;
		expected_pipe_fast_forward_data = '0;

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
		tb_issue_valid = '0;
		tb_issue_op = '0;
		tb_issue_imm12 = '0;
		tb_issue_A_is_reg = '0;
		tb_issue_A_is_bus_forward = '0;
		tb_issue_A_is_fast_forward = '0;
		tb_issue_A_fast_forward_pipe = '0;
		tb_issue_A_bank = '0;
		tb_issue_dest_PR = '0;
		tb_issue_ROB_index = '0;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = '0;
		tb_A_reg_read_resp_data = '0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = '0;
	    // fast forward data
		tb_fast_forward_data_by_pipe = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = '0;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = '0;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = '0;
		expected_WB_data = '0;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = '0;
		expected_pipe_fast_forward_notif_PR = '0;
		expected_pipe_fast_forward_data_valid = '0;
		expected_pipe_fast_forward_data = '0;

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