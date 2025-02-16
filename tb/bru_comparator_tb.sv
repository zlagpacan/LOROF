/*
    Filename: bru_comparator_tb.sv
    Author: zlagpacan
    Description: Testbench for bru_comparator module. 
    Spec: LOROF/spec/design/bru_comparator.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_comparator_tb ();

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
	logic DUT_eq, expected_eq;
	logic DUT_lts, expected_lts;
	logic DUT_ltu, expected_ltu;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bru_comparator DUT (
		.A(tb_A),
		.B(tb_B),
		.eq(DUT_eq),
		.lts(DUT_lts),
		.ltu(DUT_ltu)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_eq !== DUT_eq) begin
			$display("TB ERROR: expected_eq (%h) != DUT_eq (%h)",
				expected_eq, DUT_eq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_lts !== DUT_lts) begin
			$display("TB ERROR: expected_lts (%h) != DUT_lts (%h)",
				expected_lts, DUT_lts);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ltu !== DUT_ltu) begin
			$display("TB ERROR: expected_ltu (%h) != DUT_ltu (%h)",
				expected_ltu, DUT_ltu);
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
		tb_A = 32'h0;
		tb_B = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_eq = 1'b1;
		expected_lts = 1'b0;
		expected_ltu = 1'b0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_A = 32'h0;
		tb_B = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_eq = 1'b1;
		expected_lts = 1'b0;
		expected_ltu = 1'b0;

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 2**8; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // reset
            nRST = 1'b1;
            tb_A = {8{i[3:0]}};
            tb_B = {8{i[7:4]}};

            // inputs
            sub_test_case = $sformatf("A: %0h; B: %0h", tb_A, tb_B);
            $display("\t- sub_test: %s", sub_test_case);

            @(negedge CLK);

            // outputs:

            expected_eq = tb_A == tb_B;
            expected_lts = $signed(tb_A) < $signed(tb_B);
            expected_ltu = tb_A < tb_B;
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