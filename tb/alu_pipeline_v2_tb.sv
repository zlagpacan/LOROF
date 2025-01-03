/*
    Filename: alu_pipeline_v2_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_pipeline_v2 module. 
    Spec: LOROF/spec/design/alu_pipeline_v2.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_pipeline_v2_tb ();

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


    // ALU op issue from ALU IQ
	logic tb_issue_valid;
	logic [3:0] tb_issue_op;
	logic tb_issue_is_imm;
	logic [31:0] tb_issue_imm;
	logic tb_issue_A_unneeded;
	logic tb_issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_A_bank;
	logic tb_issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_B_bank;
	logic [LOG_PR_COUNT-1:0] tb_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_issue_ROB_index;

    // reg read info and data from PRF
	logic tb_A_reg_read_valid;
	logic tb_B_reg_read_valid;
	logic [PRF_BANK_COUNT-1:0][31:0] tb_reg_read_data_by_bank;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_forward_data_by_bank;

    // ready feedback to ALU IQ
	logic DUT_issue_ready, expected_issue_ready;

    // writeback data to PRF
	logic DUT_WB_valid, expected_WB_valid;
	logic [31:0] DUT_WB_data, expected_WB_data;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR, expected_WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_WB_ROB_index, expected_WB_ROB_index;

    // writeback backpressure from PRF
	logic tb_WB_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_pipeline_v2 DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // ALU op issue from ALU IQ
		.issue_valid(tb_issue_valid),
		.issue_op(tb_issue_op),
		.issue_is_imm(tb_issue_is_imm),
		.issue_imm(tb_issue_imm),
		.issue_A_unneeded(tb_issue_A_unneeded),
		.issue_A_forward(tb_issue_A_forward),
		.issue_A_bank(tb_issue_A_bank),
		.issue_B_forward(tb_issue_B_forward),
		.issue_B_bank(tb_issue_B_bank),
		.issue_dest_PR(tb_issue_dest_PR),
		.issue_ROB_index(tb_issue_ROB_index),

	    // reg read info and data from PRF
		.A_reg_read_valid(tb_A_reg_read_valid),
		.B_reg_read_valid(tb_B_reg_read_valid),
		.reg_read_data_by_bank(tb_reg_read_data_by_bank),

	    // forward data from PRF
		.forward_data_by_bank(tb_forward_data_by_bank),

	    // ready feedback to ALU IQ
		.issue_ready(DUT_issue_ready),

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
	    // ALU op issue from ALU IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_is_imm = 1'b0;
		tb_issue_imm = 32'h0;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 6'h0;
		tb_issue_ROB_index = 6'h0;
	    // reg read info and data from PRF
		tb_A_reg_read_valid = 1'b0;
		tb_B_reg_read_valid = 1'b0;
		tb_reg_read_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;

		@(posedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_issue_ready = 1'b1;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 6'h0;
		expected_WB_ROB_index = 6'h0;
	    // writeback backpressure from PRF

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op issue from ALU IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_is_imm = 1'b0;
		tb_issue_imm = 32'h0;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 6'h0;
		tb_issue_ROB_index = 6'h0;
	    // reg read info and data from PRF
		tb_A_reg_read_valid = 1'b0;
		tb_B_reg_read_valid = 1'b0;
		tb_reg_read_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;

		@(posedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_issue_ready = 1'b1;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 6'h0;
		expected_WB_ROB_index = 6'h0;
	    // writeback backpressure from PRF

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK);

		// inputs
		sub_test_case = {"\n\t\t", 
            "issue: i NOP", "\n\t\t",
            "OC: i NOP", "\n\t\t",
            "EX: i NOP", "\n\t\t",
            "WB: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op issue from ALU IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_is_imm = 1'b0;
		tb_issue_imm = 32'h0;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 6'h0;
		tb_issue_ROB_index = 6'h0;
	    // reg read info and data from PRF
		tb_A_reg_read_valid = 1'b0;
		tb_B_reg_read_valid = 1'b0;
		tb_reg_read_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_issue_ready = 1'b1;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 6'h0;
		expected_WB_ROB_index = 6'h0;
	    // writeback backpressure from PRF

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = {"\n\t\t", 
            "issue: v 0: ADD p2, p0:r, p1:r", "\n\t\t",
            "OC: i NOP", "\n\t\t",
            "EX: i NOP", "\n\t\t",
            "WB: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op issue from ALU IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0000;
		tb_issue_is_imm = 1'b0;
		tb_issue_imm = 32'h0;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h1;
		tb_issue_dest_PR = 6'h2;
		tb_issue_ROB_index = 6'h0;
	    // reg read info and data from PRF
		tb_A_reg_read_valid = 1'b0;
		tb_B_reg_read_valid = 1'b0;
		tb_reg_read_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_issue_ready = 1'b1;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 6'h0;
		expected_WB_ROB_index = 6'h0;
	    // writeback backpressure from PRF

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = {"\n\t\t", 
            "issue: v 1: SLLI p4, p3:r, 0x4", "\n\t\t",
            "OC: v 0: ADD p2, p0:r, p1:r", "\n\t\t",
            "EX: i NOP", "\n\t\t",
            "WB: i NOP", "\n\t\t",
			"activity: reg read p0, p1", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op issue from ALU IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0001;
		tb_issue_is_imm = 1'b1;
		tb_issue_imm = 32'h4;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 6'h4;
		tb_issue_ROB_index = 6'h1;
	    // reg read info and data from PRF
		tb_A_reg_read_valid = 1'b1;
		tb_B_reg_read_valid = 1'b1;
		tb_reg_read_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h1};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_issue_ready = 1'b1;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 6'h0;
		expected_WB_ROB_index = 6'h0;
	    // writeback backpressure from PRF

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = {"\n\t\t", 
            "issue: v 2: SLT p7, p5:f, p6:r", "\n\t\t",
            "OC: v 1: SLLI p4, p3:r, 0x4", "\n\t\t",
            "EX: v 0: ADD p2, p0:r, p1:r", "\n\t\t",
            "WB: i NOP", "\n\t\t",
			"activity: reg read p3", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op issue from ALU IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0010;
		tb_issue_is_imm = 1'b0;
		tb_issue_imm = 32'h0;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_bank = 2'h1;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h2;
		tb_issue_dest_PR = 6'h7;
		tb_issue_ROB_index = 6'h2;
	    // reg read info and data from PRF
		tb_A_reg_read_valid = 1'b1;
		tb_B_reg_read_valid = 1'b0;
		tb_reg_read_data_by_bank = {32'h3, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_issue_ready = 1'b1;
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h0;
		expected_WB_PR = 6'h0;
		expected_WB_ROB_index = 6'h0;
	    // writeback backpressure from PRF

		check_outputs();

        // ------------------------------------------------------------
        // finish:
        @(posedge CLK);
        
        test_case = "finish";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK);

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