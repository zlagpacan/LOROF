/*
    Filename: mul_diff_signs_33_tb.sv
    Author: zlagpacan
    Description: Testbench for mul_diff_signs_33 module. 
    Spec: LOROF/spec/design/mul_diff_signs_33.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;


module mul_diff_signs_33_tb ();

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

	logic [31:0] tb_A;
	logic [31:0] tb_B;

	logic [1:0] tb_sel;

	logic [63:0] DUT_out, expected_out;

    // ----------------------------------------------------------------
    // DUT instantiation:

	mul_diff_signs_33 #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

		.A(tb_A),
		.B(tb_B),

		.sel(tb_sel),

		.out(DUT_out)
	);

    // ----------------------------------------------------------------
    // classes:

    class RandIntOperands;
        rand bit [31:0] A;
        rand bit [31:0] B;
    endclass

    RandIntOperands operands;

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_out !== DUT_out) begin
			$display("TB ERROR: expected_out (%h) != DUT_out (%h)",
				expected_out, DUT_out);
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
		tb_sel = 2'b00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_out = 0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_A = 0;
		tb_B = 0;
		tb_sel = 2'b00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_out = 0;

		check_outputs();

        // ------------------------------------------------------------
        // random operands MUL/MULH:
        test_case = "random operands MUL/MULH";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        operands = new();

        for (int i = 0; i < 100; i++) begin

            operands.randomize();

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("%d * %d", $signed(operands.A), $signed(operands.B));
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_A = operands.A;
            tb_B = operands.B;
		    tb_sel = 2'b01;

            @(negedge CLK);

            // outputs:

            expected_out = $signed(operands.A) * $signed(operands.B);

            check_outputs();
        end

        // ------------------------------------------------------------
        // random operands MUL/MULHSU:
        test_case = "random operands MUL/MULHSU";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 100; i++) begin

            operands.randomize();

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("%d * %d", $signed({operands.A[31], operands.A}), $signed({1'b0, operands.B}));
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_A = operands.A;
            tb_B = operands.B;
		    tb_sel = 2'b10;

            @(negedge CLK);

            // outputs:

            expected_out = $signed({operands.A[31], operands.A}) * $signed({1'b0, operands.B});

            check_outputs();
        end

        // ------------------------------------------------------------
        // random operands MUL/MULHU:
        test_case = "random operands MUL/MULHU";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 100; i++) begin

            operands.randomize();

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("%d * %d", operands.A, operands.B);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_A = operands.A;
            tb_B = operands.B;
		    tb_sel = 2'b11;

            @(negedge CLK);

            // outputs:

            expected_out = operands.A * operands.B;

            check_outputs();
        end

        // ------------------------------------------------------------
        // custom inputs:
        test_case = "custom inputs";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("%d * %d", -9, 32'h5A5A5A5A);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_A = -9;
        tb_B = 32'h5A5A5A5A;
        tb_sel = 2'b10;

        @(negedge CLK);

        // outputs:

        expected_out = -9 * 32'h5A5A5A5A;

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("%d * %d", 33'h1FFFFFFF6, 33'h05A5A5A5A);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_A = $signed(33'h1FFFFFFF6);
        tb_B = $signed(33'h05A5A5A5A);
        tb_sel = 2'b10;

        @(negedge CLK);

        // outputs:

        expected_out = $signed(33'h1FFFFFFF6) * $signed(33'h05A5A5A5A);

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