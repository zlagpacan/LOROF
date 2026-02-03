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

	logic [15:0][4:0] DUT_count_vec, expected_count_vec;
	logic [15:0] DUT_deqing_vec, expected_deqing_vec;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ibuffer_deqer #(
	) DUT (

		.valid_vec(tb_valid_vec),
		.uncompressed_vec(tb_uncompressed_vec),

		.count_vec(DUT_count_vec),
		.deqing_vec(DUT_deqing_vec)
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

		check_outputs();

        // ------------------------------------------------------------
        // every 999th:
        test_case = "every 999th";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 2**16; i += 999) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("i = %16b", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_valid_vec = i[15:0];
            tb_uncompressed_vec = {4{i[3:0]}};

            @(negedge CLK);

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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule