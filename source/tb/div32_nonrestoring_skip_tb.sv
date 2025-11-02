/*
    Filename: div32_nonrestoring_skip_tb.sv
    Author: zlagpacan
    Description: Testbench for div32_nonrestoring_skip module. 
    Spec: LOROF/spec/design/div32_nonrestoring_skip.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module div32_nonrestoring_skip_tb #(
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


    // fsm control
	logic tb_clear;
	logic tb_is_signed;
	logic DUT_done, expected_done;

    // inputs
	logic [31:0] tb_A32_in;
	logic [31:0] tb_B32_in;

    // outputs
	logic [31:0] DUT_quotient_out, expected_quotient_out;
	logic [31:0] DUT_remainder_out, expected_remainder_out;

    // ----------------------------------------------------------------
    // DUT instantiation:

	div32_nonrestoring_skip #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // fsm control
		.clear(tb_clear),
		.is_signed(tb_is_signed),
		.done(DUT_done),

	    // inputs
		.A32_in(tb_A32_in),
		.B32_in(tb_B32_in),

	    // outputs
		.quotient_out(DUT_quotient_out),
		.remainder_out(DUT_remainder_out)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_done !== DUT_done) begin
			$display("TB ERROR: expected_done (%h) != DUT_done (%h)",
				expected_done, DUT_done);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_quotient_out !== DUT_quotient_out) begin
			$display("TB ERROR: expected_quotient_out (%h) != DUT_quotient_out (%h)",
				expected_quotient_out, DUT_quotient_out);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_remainder_out !== DUT_remainder_out) begin
			$display("TB ERROR: expected_remainder_out (%h) != DUT_remainder_out (%h)",
				expected_remainder_out, DUT_remainder_out);
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
	    // fsm control
		tb_clear = 
		tb_is_signed = 1'b0;
	    // inputs
		tb_A32_in = 32'h0;
		tb_B32_in = 32'h0;
	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // fsm control
		expected_done = 1'b0;
	    // inputs
	    // outputs
		expected_quotient_out = 32'h0;
		expected_remainder_out = 32'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fsm control
		tb_clear = 
		tb_is_signed = 1'b0;
	    // inputs
		tb_A32_in = 32'h0;
		tb_B32_in = 32'h0;
	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // fsm control
		expected_done = 1'b0;
	    // inputs
	    // outputs
		expected_quotient_out = 32'h0;
		expected_remainder_out = 32'h0;

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
	    // fsm control
		tb_clear = 
		tb_is_signed = 1'b0;
	    // inputs
		tb_A32_in = 32'h0;
		tb_B32_in = 32'h0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // fsm control
		expected_done = 1'b0;
	    // inputs
	    // outputs
		expected_quotient_out = 32'h0;
		expected_remainder_out = 32'h0;

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