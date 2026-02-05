/*
    Filename: ibuffer_deqer_tb.sv
    Author: zlagpacan
    Description: Testbench for ibuffer_deqer module. 
    Spec: LOROF/spec/design/ibuffer_deqer.md
*/

`timescale 1ns/100ps


module ibuffer_deqer_tb #(
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

	logic [15:0] tb_valid_vec;
	logic [15:0] tb_uncompressed_vec;
	logic [15:0] tb_redirect_vec;

	logic [15:0][4:0] DUT_count_vec, expected_count_vec;
	logic [15:0] DUT_deqing_vec, expected_deqing_vec;

	logic [3:0] DUT_valid_by_way, expected_valid_by_way;
	logic [3:0][3:0] DUT_first_idx_by_way, expected_first_idx_by_way;
	logic [3:0][3:0] DUT_second_idx_by_way, expected_second_idx_by_way;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ibuffer_deqer #(
	) DUT (

		.valid_vec(tb_valid_vec),
		.uncompressed_vec(tb_uncompressed_vec),
		.redirect_vec(tb_redirect_vec),

		.count_vec(DUT_count_vec),
		.deqing_vec(DUT_deqing_vec),

		.valid_by_way(DUT_valid_by_way),
		.first_idx_by_way(DUT_first_idx_by_way),
		.second_idx_by_way(DUT_second_idx_by_way)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_count_vec !== DUT_count_vec) begin
			$display("TB ERROR: expected_count_vec (%h) != DUT_count_vec (%h)",
				expected_count_vec, DUT_count_vec);
            for (int i = 15; i >= 0; i--) begin
                $display("\t[%2d]: v = %1b, unc = %1b, expected = %0h \t%s\t DUT = %0h",
                    i, tb_valid_vec[i], tb_uncompressed_vec[i], expected_count_vec[i], expected_count_vec[i] == DUT_count_vec[i] ? "==" : "!=", DUT_count_vec[i]);
            end
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deqing_vec !== DUT_deqing_vec) begin
			$display("TB ERROR: expected_deqing_vec (%h) != DUT_deqing_vec (%h)",
				expected_deqing_vec, DUT_deqing_vec);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_valid_by_way !== DUT_valid_by_way) begin
			$display("TB ERROR: expected_valid_by_way (%h) != DUT_valid_by_way (%h)",
				expected_valid_by_way, DUT_valid_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_first_idx_by_way !== DUT_first_idx_by_way) begin
			$display("TB ERROR: expected_first_idx_by_way (%h) != DUT_first_idx_by_way (%h)",
				expected_first_idx_by_way, DUT_first_idx_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_second_idx_by_way !== DUT_second_idx_by_way) begin
			$display("TB ERROR: expected_second_idx_by_way (%h) != DUT_second_idx_by_way (%h)",
				expected_second_idx_by_way, DUT_second_idx_by_way);
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
		tb_redirect_vec = 16'b0000000000000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_count_vec = {
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0
        };
		expected_deqing_vec = 16'b0000000000000000;
		expected_valid_by_way = 4'b0000;
		expected_first_idx_by_way = {4'hf, 4'hf, 4'hf, 4'hf};
		expected_second_idx_by_way = {4'hf, 4'hf, 4'hf, 4'hf};

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_vec = 16'b0000000000000000;
		tb_uncompressed_vec = 16'b0000000000000000;
		tb_redirect_vec = 16'b0000000000000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_count_vec = {
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0,
            5'h0
        };
		expected_deqing_vec = 16'b0000000000000000;
		expected_valid_by_way = 4'b0000;
		expected_first_idx_by_way = {4'hf, 4'hf, 4'hf, 4'hf};
		expected_second_idx_by_way = {4'hf, 4'hf, 4'hf, 4'hf};

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
        tb_valid_vec = 16'b1111111111111111;
        tb_uncompressed_vec = 16'b0000000000000000;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h10,
            5'h0F,
            5'h0E,
            5'h0D,
            5'h0C,
            5'h0B,
            5'h0A,
            5'h09,
            5'h08,
            5'h07,
            5'h06,
            5'h05,
            5'h04,
            5'h03,
            5'h02,
            5'h01
        };
        expected_deqing_vec = 16'b0000000000001111;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'h3, 4'h2, 4'h1, 4'h0};
        expected_second_idx_by_way = {4'h4, 4'h3, 4'h2, 4'h1};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 1";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b1111111111111111;
        tb_uncompressed_vec = 16'b1111111111111111;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h08,
            5'h08,
            5'h07,
            5'h07,
            5'h06,
            5'h06,
            5'h05,
            5'h05,
            5'h04,
            5'h04,
            5'h03,
            5'h03,
            5'h02,
            5'h02,
            5'h01,
            5'h01
        };
        expected_deqing_vec = 16'b0000000011111111;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'h6, 4'h4, 4'h2, 4'h0};
        expected_second_idx_by_way = {4'h7, 4'h5, 4'h3, 4'h1};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 2";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b1111111111111111;
        tb_uncompressed_vec = 16'b0101010101010101;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h08,
            5'h08,
            5'h07,
            5'h07,
            5'h06,
            5'h06,
            5'h05,
            5'h05,
            5'h04,
            5'h04,
            5'h03,
            5'h03,
            5'h02,
            5'h02,
            5'h01,
            5'h01
        };
        expected_deqing_vec = 16'b0000000011111111;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'h6, 4'h4, 4'h2, 4'h0};
        expected_second_idx_by_way = {4'h7, 4'h5, 4'h3, 4'h1};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 3";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b1111111111111111;
        tb_uncompressed_vec = 16'b1010101010101010;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h08,
            5'h08,
            5'h08,
            5'h07,
            5'h07,
            5'h06,
            5'h06,
            5'h05,
            5'h05,
            5'h04,
            5'h04,
            5'h03,
            5'h03,
            5'h02,
            5'h02,
            5'h01
        };
        expected_deqing_vec = 16'b0000000001111111;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'h5, 4'h3, 4'h1, 4'h0};
        expected_second_idx_by_way = {4'h6, 4'h4, 4'h2, 4'h1};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 4";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b0000000011110000;
        tb_uncompressed_vec = 16'b0000000010000000;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h02,
            5'h01,
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        expected_deqing_vec = 16'b0000000001110000;
        expected_valid_by_way = 4'b0111;
        expected_first_idx_by_way = {4'hf, 4'h6, 4'h5, 4'h4};
        expected_second_idx_by_way = {4'hf, 4'h7, 4'h6, 4'h5};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 5";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b0000000111110000;
        tb_uncompressed_vec = 16'b0000000010000000;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h03,
            5'h02,
            5'h01,
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        expected_deqing_vec = 16'b0000000111110000;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'h7, 4'h6, 4'h5, 4'h4};
        expected_second_idx_by_way = {4'h8, 4'h7, 4'h6, 4'h5};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 6";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b0000000011110000;
        tb_uncompressed_vec = 16'b0000000010000000;
		tb_redirect_vec = 16'b0000000010000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h04,
            5'h03,
            5'h02,
            5'h01,
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        expected_deqing_vec = 16'b0000000011110000;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'h7, 4'h6, 4'h5, 4'h4};
        expected_second_idx_by_way = {4'h8, 4'h7, 4'h6, 4'h5};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 7";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b1000000111100000;
        tb_uncompressed_vec = 16'b0000000010000000;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h04,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h02,
            5'h01,
            5'h00,
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        expected_deqing_vec = 16'b1000000111100000;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'hf, 4'h7, 4'h6, 4'h5};
        expected_second_idx_by_way = {4'hf, 4'h8, 4'h7, 4'h6};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 8";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b1000000111100000;
        tb_uncompressed_vec = 16'b1000000010000000;
		tb_redirect_vec = 16'b0000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h02,
            5'h01,
            5'h00,
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        expected_deqing_vec = 16'b0000000111100000;
        expected_valid_by_way = 4'b0111;
        expected_first_idx_by_way = {4'hf, 4'h7, 4'h6, 4'h5};
        expected_second_idx_by_way = {4'hf, 4'h8, 4'h7, 4'h6};

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "case 9";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        tb_valid_vec = 16'b1000000111100000;
        tb_uncompressed_vec = 16'b1000000010000000;
		tb_redirect_vec = 16'b1000000000000000;

        @(negedge CLK);

        // outputs:

        expected_count_vec = {
            5'h04,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h03,
            5'h02,
            5'h01,
            5'h00,
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        expected_deqing_vec = 16'b1000000111100000;
        expected_valid_by_way = 4'b1111;
        expected_first_idx_by_way = {4'hf, 4'h7, 4'h6, 4'h5};
        expected_second_idx_by_way = {4'hf, 4'h8, 4'h7, 4'h6};

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