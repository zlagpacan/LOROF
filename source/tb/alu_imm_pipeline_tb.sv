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
	parameter OC_ENTRIES = IS_OC_BUFFER_SIZE + 1,
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
	logic [FAST_FORWARD_PIPE_COUNT-1:0] tb_fast_forward_data_valid_by_pipe;
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
		.OC_ENTRIES(OC_ENTRIES),
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
		.fast_forward_data_valid_by_pipe(tb_fast_forward_data_valid_by_pipe),
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
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b0;
		expected_pipe_fast_forward_notif_PR = 7'h00;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'h00000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b0;
		expected_pipe_fast_forward_notif_PR = 7'h00;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'h00000000;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i}, i : issue reg0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0f0;
		tb_issue_A_is_reg = 1'b1;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h0f;
		tb_issue_ROB_index = 7'h0f;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b0;
		expected_pipe_fast_forward_notif_PR = 7'h00;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, reg0}, i : issue reg1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0001;
		tb_issue_imm12 = 12'h1e1;
		tb_issue_A_is_reg = 1'b1;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h1e;
		tb_issue_ROB_index = 7'h1e;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000000;
		expected_WB_PR = 7'h00;
		expected_WB_ROB_index = 7'h00;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h0f;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{reg1, reg0:c}, i : (fail) issue reg2, resp reg0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h2d2;
		tb_issue_A_is_reg = 1'b1;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h2d;
		tb_issue_ROB_index = 7'h2d;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hf0f0f0f0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1010;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h000000f0;
		expected_WB_PR = 7'h0f;
		expected_WB_ROB_index = 7'h0f;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h0f;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'h000000f0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, reg1}, reg0 : issue reg2, WB not ready";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h2d2;
		tb_issue_A_is_reg = 1'b1;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h2d;
		tb_issue_ROB_index = 7'h2d;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1010;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hf0f0f0f0 + 32'h000000f0;
		expected_WB_PR = 7'h0f;
		expected_WB_ROB_index = 7'h0f;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h1e;
		expected_pipe_fast_forward_data_valid = 1'b1;
		expected_pipe_fast_forward_data = 32'hf0f0f0f0 + 32'h000000f0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{reg2, reg1:c}, reg0 : reg1 resp";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'he1e1e1e1;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1010;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hf0f0f0f0 + 32'h000000f0;
		expected_WB_PR = 7'h0f;
		expected_WB_ROB_index = 7'h0f;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h1e;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'hf0f0f0f0 + 32'h000000f0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, reg2:c}, reg1:c : issue busfwd3, reg2 resp";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0011;
		tb_issue_imm12 = 12'h3c3;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b1;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h3;
		tb_issue_dest_PR = 7'h3c;
		tb_issue_ROB_index = 7'h3c;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b1;
		tb_A_reg_read_resp_data = 32'hd2d2d2d2;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0101;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'he1e1e1e1 << 1;
		expected_WB_PR = 7'h1e;
		expected_WB_ROB_index = 7'h1e;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h2d;
		expected_pipe_fast_forward_data_valid = 1'b1;
		expected_pipe_fast_forward_data = 32'he1e1e1e1 << 1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, busfwd3:c}, reg2:c : issue fastfwd4, busfwd3 bus";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0100;
		tb_issue_imm12 = 12'h4b4;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b1;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h4b;
		tb_issue_ROB_index = 7'h4b;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hc3c3c3c3,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0101;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h1;
		expected_WB_PR = 7'h2d;
		expected_WB_ROB_index = 7'h2d;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h3c;
		expected_pipe_fast_forward_data_valid = 1'b1;
		expected_pipe_fast_forward_data = 32'h1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, fastfwd4}, busfwd3:c : issue fastfwd4p2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0101;
		tb_issue_imm12 = 12'h5a5;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b1;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h5a;
		tb_issue_ROB_index = 7'h5a;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1110;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'h0;
		expected_WB_PR = 7'h3c;
		expected_WB_ROB_index = 7'h3c;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h4b;
		expected_pipe_fast_forward_data_valid = 1'b1;
		expected_pipe_fast_forward_data = 32'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{fastfwd4p2:c, fastfwd4:c}, i : fastfwd4[p2] resp";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1101;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hb4b4b4b4
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h000004b4;
		expected_WB_PR = 7'h4b;
		expected_WB_ROB_index = 7'h4b;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h4b;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'h000004b4;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, fastfwd4p2:c}, fastfwd4:c : none";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hb4b4b000;
		expected_WB_PR = 7'h4b;
		expected_WB_ROB_index = 7'h4b;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b1;
		expected_pipe_fast_forward_notif_PR = 7'h5a;
		expected_pipe_fast_forward_data_valid = 1'b1;
		expected_pipe_fast_forward_data = 32'h4b4b4b000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i}, fastfwd4p2:c : WB not ready";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b0;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hb4b4b4b4 >> 5;
		expected_WB_PR = 7'h5a;
		expected_WB_ROB_index = 7'h5a;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b0;
		expected_pipe_fast_forward_notif_PR = 7'h4b;
		expected_pipe_fast_forward_data_valid = 1'b1;
		expected_pipe_fast_forward_data = 32'hb4b4b4b4 >> 5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i}, fastfwd4p2:c : WB ready";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b1;
		expected_WB_data = 32'hb4b4b4b4 >> 5;
		expected_WB_PR = 7'h5a;
		expected_WB_ROB_index = 7'h5a;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b0;
		expected_pipe_fast_forward_notif_PR = 7'h4b;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'hb4b4b4b4 >> 5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i}, i : none";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU imm op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h000;
		tb_issue_A_is_reg = 1'b0;
		tb_issue_A_is_bus_forward = 1'b0;
		tb_issue_A_is_fast_forward = 1'b0;
		tb_issue_A_fast_forward_pipe = 2'h0;
		tb_issue_A_bank = 2'h0;
		tb_issue_dest_PR = 7'h00;
		tb_issue_ROB_index = 7'h00;
	    // ready feedback to IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = 1'b0;
		tb_A_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // this pipe's fast forward notif

		@(negedge CLK);

		// outputs:

	    // ALU imm op issue from IQ
	    // ready feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'hc3c3c777; // don't care
		expected_WB_PR = 7'h4b;
		expected_WB_ROB_index = 7'h4b;
	    // writeback backpressure from PRF
	    // this pipe's fast forward notif
		expected_pipe_fast_forward_notif_valid = 1'b0;
		expected_pipe_fast_forward_notif_PR = 7'h4b;
		expected_pipe_fast_forward_data_valid = 1'b0;
		expected_pipe_fast_forward_data = 32'hc3c3c777; // don't care

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