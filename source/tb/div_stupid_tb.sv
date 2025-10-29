/*
    Filename: div_stupid_tb.sv
    Author: zlagpacan
    Description: Testbench for div_stupid module. 
    Spec: LOROF/spec/design/div_stupid.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;


module div_stupid_tb ();

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

	logic signed [31:0] tb_A;
	logic signed [31:0] tb_B;

	logic signed [31:0] DUT_quotient, expected_quotient;
	logic signed [31:0] DUT_remainder, expected_remainder;

    // ----------------------------------------------------------------
    // DUT instantiation:

	div_stupid #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

		.A(tb_A),
		.B(tb_B),

		.quotient(DUT_quotient),
		.remainder(DUT_remainder)
	);

    // ----------------------------------------------------------------
    // classes:

    class RandIntOperands;
        rand bit signed [31:0] A;
        rand bit signed [31:0] B;
    endclass

    RandIntOperands operands;

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_quotient !== DUT_quotient) begin
			$display("TB ERROR: expected_quotient (%h) != DUT_quotient (%h)",
				expected_quotient, DUT_quotient);
			num_errors++;
			tb_error = 1'b1;
		end
		if (expected_remainder !== DUT_remainder) begin
			$display("TB ERROR: expected_remainder (%h) != DUT_remainder (%h)",
				expected_remainder, DUT_remainder);
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
		tb_A = 0;
		tb_B = 0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_quotient = '1;
		expected_remainder = 0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_A = 0;
		tb_B = 0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_quotient = '1;
		expected_remainder = 0;

		check_outputs();

        // ------------------------------------------------------------
        // random operands:
        test_case = "random operands";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        operands = new();

        for (int i = 0; i < 1024; i++) begin

            operands.randomize();

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("%d / %d", operands.A, operands.B);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_A = operands.A;
            tb_B = operands.B;

            @(negedge CLK);

            // outputs:

            if (operands.B == 0) begin
                expected_quotient = '1;
                expected_remainder = '1;
            end
            else begin
                expected_quotient = operands.A / operands.B;
                expected_remainder = operands.A % operands.B;
            end

            check_outputs();
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
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule