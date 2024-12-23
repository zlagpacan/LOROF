/*
    Filename: alu_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_pipeline module. 
    Spec: LOROF/spec/design/alu_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_pipeline_tb ();

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
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

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // DUT signals:


    // ALU op issue from ALU IQ
	logic tb_valid_in;
	logic [3:0] tb_op_in;
	logic tb_is_imm_in;
	logic [31:0] tb_imm_in;
	logic tb_A_unneeded_in;
	logic tb_A_forward_in;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_A_bank_in;
	logic tb_B_forward_in;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_B_bank_in;
	logic [LOG_PR_COUNT-1:0] tb_dest_PR_in;

    // reg read info and data from PRF
	logic tb_A_reg_read_valid_in;
	logic tb_B_reg_read_valid_in;
	logic [PRF_BANK_COUNT-1:0][31:0] tb_reg_read_data_by_bank_in;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_forward_data_by_bank_in;

    // ready feedback to ALU IQ
	logic DUT_ready_out, expected_ready_out;

    // writeback data to PRF
	logic DUT_WB_valid_out, expected_WB_valid_out;
	logic [31:0] DUT_WB_data_out, expected_WB_data_out;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR_out, expected_WB_PR_out;

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // DUT instantiation:

	alu_pipeline DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // ALU op issue from ALU IQ
		.valid_in(tb_valid_in),
		.op_in(tb_op_in),
		.is_imm_in(tb_is_imm_in),
		.imm_in(tb_imm_in),
		.A_unneeded_in(tb_A_unneeded_in),
		.A_forward_in(tb_A_forward_in),
		.A_bank_in(tb_A_bank_in),
		.B_forward_in(tb_B_forward_in),
		.B_bank_in(tb_B_bank_in),
		.dest_PR_in(tb_dest_PR_in),

	    // reg read info and data from PRF
		.A_reg_read_valid_in(tb_A_reg_read_valid_in),
		.B_reg_read_valid_in(tb_B_reg_read_valid_in),
		.reg_read_data_by_bank_in(tb_reg_read_data_by_bank_in),

	    // forward data from PRF
		.forward_data_by_bank_in(tb_forward_data_by_bank_in),

	    // ready feedback to ALU IQ
		.ready_out(DUT_ready_out),

	    // writeback data to PRF
		.WB_valid_out(DUT_WB_valid_out),
		.WB_data_out(DUT_WB_data_out),
		.WB_PR_out(DUT_WB_PR_out)
	);

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // tasks:

    task check_outputs();
    begin
		if (expected_ready_out !== DUT_ready_out) begin
			$display("TB ERROR: expected_ready_out (%h) != DUT_ready_out (%h)",
				expected_ready_out, DUT_ready_out);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_valid_out !== DUT_WB_valid_out) begin
			$display("TB ERROR: expected_WB_valid_out (%h) != DUT_WB_valid_out (%h)",
				expected_WB_valid_out, DUT_WB_valid_out);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_data_out !== DUT_WB_data_out) begin
			$display("TB ERROR: expected_WB_data_out (%h) != DUT_WB_data_out (%h)",
				expected_WB_data_out, DUT_WB_data_out);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_PR_out !== DUT_WB_PR_out) begin
			$display("TB ERROR: expected_WB_PR_out (%h) != DUT_WB_PR_out (%h)",
				expected_WB_PR_out, DUT_WB_PR_out);
			num_errors++;
			tb_error = 1'b1;
		end

        #(PERIOD / 10);
        tb_error = 1'b0;
    end
    endtask

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // initial block:

    initial begin

        ///////////////////////////////////////////////////////////////////////////////////////////////////
        // reset:
        test_case = "reset";
        $display("\ntest %d: %s", test_num, test_case);
        test_num++;

        // inputs:
        sub_test_case = "assert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b0;
	    // ALU op issue from ALU IQ
		tb_valid_in = 1'b0;
		tb_op_in = 4'b0000;
		tb_is_imm_in = 1'b0;
		tb_imm_in = 32'h0;
		tb_A_unneeded_in = 1'b0;
		tb_A_forward_in = 1'b0;
		tb_A_bank_in = 2'h0;
		tb_B_forward_in = 1'b0;
		tb_B_bank_in = 2'h0;
		tb_dest_PR_in = 6'h0;
	    // reg read info and data from PRF
		tb_A_reg_read_valid_in = 1'b0;
		tb_B_reg_read_valid_in = 1'b0;
		tb_reg_read_data_by_bank_in = {32'h0, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank_in = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF

		@(posedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_ready_out = 1'b1;
	    // writeback data to PRF
		expected_WB_valid_out = 1'b0;
		expected_WB_data_out = 32'h0;
		expected_WB_PR_out = 6'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op issue from ALU IQ
		tb_valid_in = 1'b0;
		tb_op_in = 4'b0000;
		tb_is_imm_in = 1'b0;
		tb_imm_in = 32'h0;
		tb_A_unneeded_in = 1'b0;
		tb_A_forward_in = 1'b0;
		tb_A_bank_in = 2'h0;
		tb_B_forward_in = 1'b0;
		tb_B_bank_in = 2'h0;
		tb_dest_PR_in = 6'h0;
	    // reg read info and data from PRF
		tb_A_reg_read_valid_in = 1'b0;
		tb_B_reg_read_valid_in = 1'b0;
		tb_reg_read_data_by_bank_in = {32'h0, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank_in = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF

		@(posedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_ready_out = 1'b1;
	    // writeback data to PRF
		expected_WB_valid_out = 1'b0;
		expected_WB_data_out = 32'h0;
		expected_WB_PR_out = 6'h0;

		check_outputs();

        ///////////////////////////////////////////////////////////////////////////////////////////////////
        // default:
        test_case = "default";
        $display("\ntest %d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK);

		// inputs
		sub_test_case = "default";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op issue from ALU IQ
		tb_valid_in = 1'b0;
		tb_op_in = 4'b0000;
		tb_is_imm_in = 1'b0;
		tb_imm_in = 32'h0;
		tb_A_unneeded_in = 1'b0;
		tb_A_forward_in = 1'b0;
		tb_A_bank_in = 2'h0;
		tb_B_forward_in = 1'b0;
		tb_B_bank_in = 2'h0;
		tb_dest_PR_in = 6'h0;
	    // reg read info and data from PRF
		tb_A_reg_read_valid_in = 1'b0;
		tb_B_reg_read_valid_in = 1'b0;
		tb_reg_read_data_by_bank_in = {32'h0, 32'h0, 32'h0, 32'h0};
	    // forward data from PRF
		tb_forward_data_by_bank_in = {32'h0, 32'h0, 32'h0, 32'h0};
	    // ready feedback to ALU IQ
	    // writeback data to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op issue from ALU IQ
	    // reg read info and data from PRF
	    // forward data from PRF
	    // ready feedback to ALU IQ
		expected_ready_out = 1'b1;
	    // writeback data to PRF
		expected_WB_valid_out = 1'b0;
		expected_WB_data_out = 32'h0;
		expected_WB_PR_out = 6'h0;

		check_outputs();

        ///////////////////////////////////////////////////////////////////////////////////////////////////
        // finish:
        @(posedge CLK);
        
        test_case = "finish";
        $display("\ntest %d: %s", test_num, test_case);
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

