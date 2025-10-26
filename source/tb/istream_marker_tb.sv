/*
    Filename: istream_marker_tb.sv
    Author: zlagpacan
    Description: Testbench for istream_marker module. 
    Spec: LOROF/spec/design/istream_marker.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module istream_marker_tb ();

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
	logic [15:0] tb_valid_vec;
	logic [15:0] tb_uncompressed_vec;
	logic [15:0] DUT_marker_vec, expected_marker_vec;

    // ----------------------------------------------------------------
    // DUT instantiation:

	istream_marker DUT (
		.valid_vec(tb_valid_vec),
		.uncompressed_vec(tb_uncompressed_vec),
		.marker_vec(DUT_marker_vec)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_marker_vec !== DUT_marker_vec) begin
			$display("TB ERROR: expected_marker_vec (%h) != DUT_marker_vec (%h)",
				expected_marker_vec, DUT_marker_vec);
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
		tb_valid_vec = 16'b0000000000000000;
		tb_uncompressed_vec = 16'b0000000000000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_marker_vec = 16'b0000000000000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b0000000000000000;
		tb_uncompressed_vec = 16'b0000000000000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_marker_vec = 16'b0000000000000000;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "all unC 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b1111111111111111;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b10101010101010101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "all unC 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b10101010101010101;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b10101010101010101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "all C";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b0000000000000000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b1111111111111111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "mixed 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b0001000100010001;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b1101110111011101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "mixed 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b1000100010001000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b0110111011101111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "mixed 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b0000100010001000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b1110111011101111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "mixed 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b0010100010001000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b1010111011101111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "mixed 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b1111111111111111;
		tb_uncompressed_vec = 16'b1010100010001000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b0010111011101111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "mixed w/ invalids 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b0000111100001111;
		tb_uncompressed_vec = 16'b1010100010001000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 16'b0010111011101111;

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