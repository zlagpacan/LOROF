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
	// logic DUT_done, expected_done;

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
    // classes:

    class RandIntOperands;
        rand bit            is_signed;
        rand bit            small_divisor;
        rand bit [31:0]     A;
        rand bit [31:0]     B;

        constraint B_range {
            if (small_divisor) {
                if (is_signed) {
                    -32768 <= B && B <= 32767;
                }
                else {
                    0 <= B && B <= 65535;
                }
            }
        }

    endclass

    RandIntOperands operands;

    int i;
    int cycle_counter;

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		// if (expected_done !== DUT_done) begin
		// 	$display("TB ERROR: expected_done (%h) != DUT_done (%h)",
		// 		expected_done, DUT_done);
		// 	num_errors++;
		// 	tb_error = 1'b1;
		// end

		if (expected_quotient_out !== DUT_quotient_out) begin
			$display("TB ERROR: expected_quotient_out (%d) != DUT_quotient_out (%d)",
				$signed(expected_quotient_out), $signed(DUT_quotient_out));
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_remainder_out !== DUT_remainder_out) begin
			$display("TB ERROR: expected_remainder_out (%d) != DUT_remainder_out (%d)",
				$signed(expected_remainder_out), $signed(DUT_remainder_out));
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
		tb_clear = 1'b1;
		tb_is_signed = 1'b0;
	    // inputs
		tb_A32_in = 32'h0;
		tb_B32_in = 32'h0;
	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // fsm control
		// expected_done = 1'b0;
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
		tb_clear = 1'b1;
		tb_is_signed = 1'b0;
	    // inputs
		tb_A32_in = 32'h0;
		tb_B32_in = 32'h0;
	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // fsm control
		// expected_done = 1'b0;
	    // inputs
	    // outputs
		expected_quotient_out = 32'h0;
		expected_remainder_out = 32'h0;

		check_outputs();

        // ------------------------------------------------------------
        // manual test cases:
        test_case = "manual test cases";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        sub_test_case = $sformatf("%d / %d (signed)", 13, 5);
        $display("\t- sub_test: %s", sub_test_case);

        cycle_counter = 0;
        while (1) begin
            @(posedge CLK); #(PERIOD/10);

            // reset
            nRST = 1'b1;
            // fsm control
            tb_clear = 1'b0;
            tb_is_signed = 1'b1;
            // inputs
            tb_A32_in = 13;
            tb_B32_in = 5;
            // outputs

            @(negedge CLK);

            // outputs:

            // fsm control
            // expected_done = 1'b0;
            // inputs
            // outputs
            expected_quotient_out = 13 / 5;
            expected_remainder_out = 13 % 5;

            cycle_counter++;

            if (DUT_done) begin

                check_outputs();

                $display("    output in %d cycles", cycle_counter);

                @(posedge CLK); #(PERIOD/10);

                tb_clear = 1'b1;

                @(negedge CLK);

                break;
            end
        end

        sub_test_case = $sformatf("%d / %d (signed)", -17, -6);
        $display("\t- sub_test: %s", sub_test_case);

        cycle_counter = 0;
        while (1) begin
            @(posedge CLK); #(PERIOD/10);

            // reset
            nRST = 1'b1;
            // fsm control
            tb_clear = 1'b0;
            tb_is_signed = 1'b1;
            // inputs
            tb_A32_in = -17;
            tb_B32_in = -6;
            // outputs

            @(negedge CLK);

            // outputs:

            // fsm control
            // expected_done = 1'b0;
            // inputs
            // outputs
            expected_quotient_out = -17 / -6;
            expected_remainder_out = -17 % -6;

            cycle_counter++;

            if (DUT_done) begin

                check_outputs();

                $display("    output in %d cycles", cycle_counter);

                @(posedge CLK); #(PERIOD/10);

                tb_clear = 1'b1;

                @(negedge CLK);

                break;
            end
        end

        sub_test_case = $sformatf("%d / %d (signed)", -5, 2);
        $display("\t- sub_test: %s", sub_test_case);

        cycle_counter = 0;
        while (1) begin
            @(posedge CLK); #(PERIOD/10);

            // reset
            nRST = 1'b1;
            // fsm control
            tb_clear = 1'b0;
            tb_is_signed = 1'b1;
            // inputs
            tb_A32_in = -5;
            tb_B32_in = 2;
            // outputs

            @(negedge CLK);

            // outputs:

            // fsm control
            // expected_done = 1'b0;
            // inputs
            // outputs
            expected_quotient_out = -5 / 2;
            expected_remainder_out = -5 % 2;

            cycle_counter++;

            if (DUT_done) begin

                check_outputs();

                $display("    output in %d cycles", cycle_counter);

                @(posedge CLK); #(PERIOD/10);

                tb_clear = 1'b1;

                @(negedge CLK);

                break;
            end
        end

        sub_test_case = $sformatf("%d / %d (signed)", 24, -7);
        $display("\t- sub_test: %s", sub_test_case);

        cycle_counter = 0;
        while (1) begin
            @(posedge CLK); #(PERIOD/10);

            // reset
            nRST = 1'b1;
            // fsm control
            tb_clear = 1'b0;
            tb_is_signed = 1'b1;
            // inputs
            tb_A32_in = 24;
            tb_B32_in = -7;
            // outputs

            @(negedge CLK);

            // outputs:

            // fsm control
            // expected_done = 1'b0;
            // inputs
            // outputs
            expected_quotient_out = 24 / -7;
            expected_remainder_out = 24 % -7;

            cycle_counter++;

            if (DUT_done) begin

                check_outputs();

                $display("    output in %d cycles", cycle_counter);

                @(posedge CLK); #(PERIOD/10);

                tb_clear = 1'b1;

                @(negedge CLK);

                break;
            end
        end

        sub_test_case = $sformatf("%d / %d (unsigned)", $unsigned(3964119742), $unsigned(3597913658));
        $display("\t- sub_test: %s", sub_test_case);

        cycle_counter = 0;
        while (1) begin
            @(posedge CLK); #(PERIOD/10);

            // reset
            nRST = 1'b1;
            // fsm control
            tb_clear = 1'b0;
            tb_is_signed = 1'b0;
            // inputs
            tb_A32_in = 3964119742;
            tb_B32_in = 3597913658;
            // outputs

            @(negedge CLK);

            // outputs:

            // fsm control
            // expected_done = 1'b0;
            // inputs
            // outputs
            expected_quotient_out = $unsigned(3964119742) / $unsigned(3597913658);
            expected_remainder_out = $unsigned(3964119742) % $unsigned(3597913658);

            cycle_counter++;

            if (DUT_done) begin

                check_outputs();

                $display("    output in %d cycles", cycle_counter);

                @(posedge CLK); #(PERIOD/10);

                tb_clear = 1'b1;

                @(negedge CLK);

                break;
            end
        end

        // ------------------------------------------------------------
        // randomized test cases:
        test_case = "randomized test cases";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        operands = new();
        operands.randomize();

        i = 0;
        cycle_counter = 0;
        while (i < 1024) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            if (operands.is_signed) begin
                if (DUT_done) begin
                    sub_test_case = $sformatf("(signed) %d / %d = %d R %d", $signed(operands.A), $signed(operands.B), $signed(operands.A) / $signed(operands.B), $signed(operands.A) % $signed(operands.B));
                    $display("\t- sub_test: %s", sub_test_case);
                end

                // reset
                nRST = 1'b1;
                // fsm control
                tb_clear = 1'b0;
                tb_is_signed = operands.is_signed;
                // inputs
                tb_A32_in = operands.A;
                tb_B32_in = operands.B;
                // outputs

                @(negedge CLK);

                // outputs:

                // fsm control
                // expected_done = 1'b0;
                // inputs
                // outputs
                expected_quotient_out = $signed(operands.A) / $signed(operands.B);
                expected_remainder_out = $signed(operands.A) % $signed(operands.B);
            end
            else begin
                if (DUT_done) begin
                    sub_test_case = $sformatf("(unsigned) %d / %d = %d R %d", operands.A, operands.B, operands.A / operands.B, operands.A % operands.B);
                    $display("\t- sub_test: %s", sub_test_case);
                end

                // reset
                nRST = 1'b1;
                // fsm control
                tb_clear = 1'b0;
                tb_is_signed = operands.is_signed;
                // inputs
                tb_A32_in = operands.A;
                tb_B32_in = operands.B;
                // outputs

                @(negedge CLK);

                // outputs:

                // fsm control
                // expected_done = 1'b0;
                // inputs
                // outputs
                expected_quotient_out = operands.A / operands.B;
                expected_remainder_out = operands.A % operands.B;
            end

            cycle_counter++;

            if (DUT_done) begin

                check_outputs();

                operands.randomize();

                @(posedge CLK); #(PERIOD/10);

                tb_clear = 1'b1;

                @(negedge CLK);

                i++;
                cycle_counter = 0;
            end
        end

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