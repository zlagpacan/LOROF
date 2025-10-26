/*
    Filename: alu_tb.sv
    Author: zlagpacan
    Description: Testbench for alu module. 
    Spec: LOROF/spec/design/alu.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_tb ();

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
	logic [3:0] tb_op;
	logic [31:0] tb_A;
	logic [31:0] tb_B;

	logic [31:0] DUT_out, expected_out;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu DUT (
		.op(tb_op),
		.A(tb_A),
		.B(tb_B),

		.out(DUT_out)
	);

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
		tb_op = 4'b0000;
		tb_A = 32'h0;
		tb_B = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_out = 32'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = 4'b0000;
		tb_A = 32'h0;
		tb_B = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_out = 32'h0;

		check_outputs();

        // ------------------------------------------------------------
        // ADD:
        test_case = "ADD";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0000;
		tb_A = 32'h2;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h4;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0000;
		tb_A = 32'h00000001;
		tb_B = 32'h7FFFFFFF;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h80000000;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0000;
		tb_A = 32'h7FFFFFFF;
		tb_B = 32'h7FFFFFFF;
		@(negedge CLK);
		// outputs:
		expected_out = 32'hFFFFFFFE;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0000;
		tb_A = 32'h7FFFFFFF;
		tb_B = 32'h80000001;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

        // ------------------------------------------------------------
        // SUB:
        test_case = "SUB";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1000;
		tb_A = 32'h4;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h2;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1000;
		tb_A = 32'h7FFFFFFF;
		tb_B = 32'h80000000;
		@(negedge CLK);
		// outputs:
		expected_out = 32'hFFFFFFFF;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1000;
		tb_A = 32'h80000001;
		tb_B = 32'h00000002;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h7FFFFFFF;
		check_outputs();

        // ------------------------------------------------------------
        // SLL:
        test_case = "SLL";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0001;
		tb_A = 32'h4;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h10;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0001;
		tb_A = 32'hFFC4;
		tb_B = 32'h82;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h3FF10;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0001;
		tb_A = 32'h3;
		tb_B = 32'h1F;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h80000000;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1001;
		tb_A = 32'h3;
		tb_B = 32'h1F;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h80000000;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1001;
		tb_A = 32'h8;
		tb_B = 32'h1D;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

        // ------------------------------------------------------------
        // SLT:
        test_case = "SLT";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0010;
		tb_A = 32'h2;
		tb_B = 32'h4;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0010;
		tb_A = 32'h4;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1010;
		tb_A = 32'h0;
		tb_B = 32'h7FFFFFFF;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0010;
		tb_A = 32'h0;
		tb_B = 32'h80000000;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0010;
		tb_A = 32'h80000000;
		tb_B = 32'h80000001;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0010;
		tb_A = 32'h80000001;
		tb_B = 32'h80000000;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0010;
		tb_A = 32'h80000000;
		tb_B = 32'h7FFFFFFF;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0010;
		tb_A = 32'h7FFFFFFF;
		tb_B = 32'h80000000;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

        // ------------------------------------------------------------
        // SLTU:
        test_case = "SLTU";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0011;
		tb_A = 32'h2;
		tb_B = 32'h4;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0011;
		tb_A = 32'h4;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1011;
		tb_A = 32'h0;
		tb_B = 32'h7FFFFFFF;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0011;
		tb_A = 32'h0;
		tb_B = 32'h80000000;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0011;
		tb_A = 32'h80000000;
		tb_B = 32'h80000001;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0011;
		tb_A = 32'h80000001;
		tb_B = 32'h80000000;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0011;
		tb_A = 32'h80000000;
		tb_B = 32'h7FFFFFFF;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h0;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0011;
		tb_A = 32'h7FFFFFFF;
		tb_B = 32'h80000000;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

        // ------------------------------------------------------------
        // XOR:
        test_case = "XOR";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0100;
		tb_A = 32'h1100CACA;
		tb_B = 32'h1010ACAC;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h01106666;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1100;
		tb_A = 32'hCACA1100;
		tb_B = 32'hACAC1010;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h66660110;
		check_outputs();

        // ------------------------------------------------------------
        // SRL:
        test_case = "SRL";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0101;
		tb_A = 32'h8;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h2;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0101;
		tb_A = 32'hFFFFFFF8;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h3FFFFFFE;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0101;
		tb_A = 32'hABCD;
		tb_B = 32'h8;
		@(negedge CLK);
		// outputs:
		expected_out = 32'hAB;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0101;
		tb_A = 32'h8000ABCD;
		tb_B = 32'h1F;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1;
		check_outputs();

        // ------------------------------------------------------------
        // SRA:
        test_case = "SRA";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1101;
		tb_A = 32'h8;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h2;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1101;
		tb_A = 32'hFFFFFFF8;
		tb_B = 32'h2;
		@(negedge CLK);
		// outputs:
		expected_out = 32'hFFFFFFFE;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1101;
		tb_A = 32'hABCD;
		tb_B = 32'h8;
		@(negedge CLK);
		// outputs:
		expected_out = 32'hAB;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1101;
		tb_A = 32'h8000ABCD;
		tb_B = 32'h1F;
		@(negedge CLK);
		// outputs:
		expected_out = 32'hFFFFFFFF;
		check_outputs();

        // ------------------------------------------------------------
        // OR:
        test_case = "OR";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0110;
		tb_A = 32'h1100CACA;
		tb_B = 32'h1010ACAC;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h1110EEEE;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1110;
		tb_A = 32'hCACA1100;
		tb_B = 32'hACAC1010;
		@(negedge CLK);
		// outputs:
		expected_out = 32'hEEEE1110;
		check_outputs();

        // ------------------------------------------------------------
        // AND:
        test_case = "AND";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b0111;
		tb_A = 32'h1100CACA;
		tb_B = 32'h1010ACAC;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h10008888;
		check_outputs();

		@(posedge CLK); #(PERIOD/10);
		// reset
		nRST = 1'b1;
		tb_op = 4'b1111;
		tb_A = 32'hCACA1100;
		tb_B = 32'hACAC1010;
		@(negedge CLK);
		// outputs:
		expected_out = 32'h88881000;
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