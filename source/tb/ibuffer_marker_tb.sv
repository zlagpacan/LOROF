/*
    Filename: ibuffer_marker_tb.sv
    Author: zlagpacan
    Description: Testbench for ibuffer_marker module. 
    Spec: LOROF/spec/design/ibuffer_marker.md
*/

`timescale 1ns/100ps


module ibuffer_marker_tb #(
	parameter int unsigned WIDTH = 8
) ();

    // ----------------------------------------------------------------
    // TB setup:

    // parameters
    parameter int unsigned PERIOD = 10;

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
	logic [WIDTH-1:0] tb_valid_vec;
	logic [WIDTH-1:0] tb_uncompressed_vec;

	logic [WIDTH-1:0] DUT_marker_vec, expected_marker_vec;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ibuffer_marker #(
		.WIDTH(WIDTH)
	) DUT (
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
		tb_valid_vec = 8'b00000000;
		tb_uncompressed_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_marker_vec = 8'b00000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b00000000;
		tb_uncompressed_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_marker_vec = 8'b00000000;

		check_outputs();

        // ------------------------------------------------------------
        // interesting cases:
        test_case = "interesting cases";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11111111;
		tb_uncompressed_vec = 8'b11111111;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b01010101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b00001111;
		tb_uncompressed_vec = 8'b11111111;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b00000101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b00000111;
		tb_uncompressed_vec = 8'b11111111;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b00000101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11111000;
		tb_uncompressed_vec = 8'b11111111;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b00101000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11111111;
		tb_uncompressed_vec = 8'b00000000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b11111111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b00001111;
		tb_uncompressed_vec = 8'b00000000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b00001111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b00000111;
		tb_uncompressed_vec = 8'b00000000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b00000111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11111000;
		tb_uncompressed_vec = 8'b00000000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b11111000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 8";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11111111;
		tb_uncompressed_vec = 8'b00010001;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b11011101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case 9";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11111111;
		tb_uncompressed_vec = 8'b10011001;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b01101101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case A";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11100111;
		tb_uncompressed_vec = 8'b11111111;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b00100101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case B";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11100111;
		tb_uncompressed_vec = 8'b00000000;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b11100111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case C";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11100111;
		tb_uncompressed_vec = 8'b00100001;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b10100101;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "case D";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 8'b11100111;
		tb_uncompressed_vec = 8'b01000010;

		@(negedge CLK);

		// outputs:

		expected_marker_vec = 8'b01100011;

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