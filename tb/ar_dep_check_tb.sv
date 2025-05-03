/*
    Filename: ar_dep_check_tb.sv
    Author: zlagpacan
    Description: Testbench for ar_dep_check module. 
    Spec: LOROF/spec/design/ar_dep_check.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ar_dep_check_tb ();

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

    // inputs by way
	logic [3:0] tb_regwrite_by_way;
	logic [3:0][4:0] tb_A_AR_by_way;
	logic [3:0][4:0] tb_B_AR_by_way;
	logic [3:0][4:0] tb_dest_AR_by_way;

    // outputs by way
	logic [3:0] DUT_A_PR_dep_by_way, expected_A_PR_dep_by_way;
	logic [3:0][1:0] DUT_A_PR_sel_by_way, expected_A_PR_sel_by_way;
	logic [3:0] DUT_B_PR_dep_by_way, expected_B_PR_dep_by_way;
	logic [3:0][1:0] DUT_B_PR_sel_by_way, expected_B_PR_sel_by_way;
	logic [3:0] DUT_dest_PR_dep_by_way, expected_dest_PR_dep_by_way;
	logic [3:0][1:0] DUT_dest_PR_sel_by_way, expected_dest_PR_sel_by_way;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ar_dep_check DUT (

	    // inputs by way
		.regwrite_by_way(tb_regwrite_by_way),
		.A_AR_by_way(tb_A_AR_by_way),
		.B_AR_by_way(tb_B_AR_by_way),
		.dest_AR_by_way(tb_dest_AR_by_way),

	    // outputs by way
		.A_PR_dep_by_way(DUT_A_PR_dep_by_way),
		.A_PR_sel_by_way(DUT_A_PR_sel_by_way),
		.B_PR_dep_by_way(DUT_B_PR_dep_by_way),
		.B_PR_sel_by_way(DUT_B_PR_sel_by_way),
		.dest_PR_dep_by_way(DUT_dest_PR_dep_by_way),
		.dest_PR_sel_by_way(DUT_dest_PR_sel_by_way)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_A_PR_dep_by_way !== DUT_A_PR_dep_by_way) begin
			$display("TB ERROR: expected_A_PR_dep_by_way (%h) != DUT_A_PR_dep_by_way (%h)",
				expected_A_PR_dep_by_way, DUT_A_PR_dep_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_PR_sel_by_way !== DUT_A_PR_sel_by_way) begin
			$display("TB ERROR: expected_A_PR_sel_by_way (%h) != DUT_A_PR_sel_by_way (%h)",
				expected_A_PR_sel_by_way, DUT_A_PR_sel_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_PR_dep_by_way !== DUT_B_PR_dep_by_way) begin
			$display("TB ERROR: expected_B_PR_dep_by_way (%h) != DUT_B_PR_dep_by_way (%h)",
				expected_B_PR_dep_by_way, DUT_B_PR_dep_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_PR_sel_by_way !== DUT_B_PR_sel_by_way) begin
			$display("TB ERROR: expected_B_PR_sel_by_way (%h) != DUT_B_PR_sel_by_way (%h)",
				expected_B_PR_sel_by_way, DUT_B_PR_sel_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_PR_dep_by_way !== DUT_dest_PR_dep_by_way) begin
			$display("Tdest ERROR: expected_dest_PR_dep_by_way (%h) != DUT_dest_PR_dep_by_way (%h)",
				expected_dest_PR_dep_by_way, DUT_dest_PR_dep_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_PR_sel_by_way !== DUT_dest_PR_sel_by_way) begin
			$display("Tdest ERROR: expected_dest_PR_sel_by_way (%h) != DUT_dest_PR_sel_by_way (%h)",
				expected_dest_PR_sel_by_way, DUT_dest_PR_sel_by_way);
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
	    // inputs by way
		tb_regwrite_by_way = 4'b0000;
		tb_A_AR_by_way = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
		tb_B_AR_by_way = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
		tb_dest_AR_by_way = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
	    // outputs by way

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b0000;
		expected_A_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b0000;
		expected_B_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};
		expected_dest_PR_dep_by_way = 4'b0000;
		expected_dest_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b0000;
		tb_A_AR_by_way = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
		tb_B_AR_by_way = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
		tb_dest_AR_by_way = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
	    // outputs by way

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b0000;
		expected_A_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b0000;
		expected_B_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};
		expected_dest_PR_dep_by_way = 4'b0000;
		expected_dest_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

        // ------------------------------------------------------------
        // simple coverage:
        test_case = "simple coverage";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "no matches";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b1111;
		tb_A_AR_by_way = {
			5'h0,
			5'h1,
			5'h2,
			5'h3
		};
		tb_B_AR_by_way = {
			5'h4,
			5'h5,
			5'h6,
			5'h7
		};
		tb_dest_AR_by_way = {
			5'h8,
			5'h9,
			5'ha,
			5'hb
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b0000;
		expected_A_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b0000;
		expected_B_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "matches way 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b0001;
		tb_A_AR_by_way = {
			5'hc,
			5'h3,
			5'hc,
			5'hc
		};
		tb_B_AR_by_way = {
			5'hc,
			5'hc,
			5'h5,
			5'h4
		};
		tb_dest_AR_by_way = {
			5'h3,
			5'h4,
			5'h5,
			5'hc
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b1010;
		expected_A_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b1100;
		expected_B_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "matches way 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b0110;
		tb_A_AR_by_way = {
			5'h10,
			5'h1d,
			5'h1d,
			5'hc
		};
		tb_B_AR_by_way = {
			5'h1d,
			5'h11,
			5'h12,
			5'h1d
		};
		tb_dest_AR_by_way = {
			5'h11,
			5'h4,
			5'h1d,
			5'h12
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b0100;
		expected_A_PR_sel_by_way = {
			2'h0,
			2'h1,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b1000;
		expected_B_PR_sel_by_way = {
			2'h1,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "matches way 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b0101;
		tb_A_AR_by_way = {
			5'h12,
			5'h12,
			5'h6,
			5'h12
		};
		tb_B_AR_by_way = {
			5'h6,
			5'h12,
			5'h8,
			5'h0
		};
		tb_dest_AR_by_way = {
			5'h6,
			5'h12,
			5'h0,
			5'h9
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b1000;
		expected_A_PR_sel_by_way = {
			2'h2,
			2'h0,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b0000;
		expected_B_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "matches way 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b1001;
		tb_A_AR_by_way = {
			5'h3,
			5'h2,
			5'h3,
			5'h2
		};
		tb_B_AR_by_way = {
			5'h2,
			5'h3,
			5'h2,
			5'h3
		};
		tb_dest_AR_by_way = {
			5'h3,
			5'h7,
			5'h6,
			5'h5
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b0000;
		expected_A_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b0000;
		expected_B_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "bunch of crap 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b1011;
		tb_A_AR_by_way = {
			5'h4,
			5'h3,
			5'h2,
			5'h1
		};
		tb_B_AR_by_way = {
			5'h2,
			5'h3,
			5'h4,
			5'h5
		};
		tb_dest_AR_by_way = {
			5'h5,
			5'h4,
			5'h3,
			5'h2
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b0110;
		expected_A_PR_sel_by_way = {
			2'h0,
			2'h1,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b1100;
		expected_B_PR_sel_by_way = {
			2'h0,
			2'h1,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "bunch of crap 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b1011;
		tb_A_AR_by_way = {
			5'h2,
			5'h2,
			5'h4,
			5'h5
		};
		tb_B_AR_by_way = {
			5'h2,
			5'h3,
			5'h2,
			5'h5
		};
		tb_dest_AR_by_way = {
			5'h5,
			5'h4,
			5'h2,
			5'h2
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b1100;
		expected_A_PR_sel_by_way = {
			2'h1,
			2'h1,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b1010;
		expected_B_PR_sel_by_way = {
			2'h1,
			2'h0,
			2'h0,
			2'h0
		};
		expected_dest_PR_dep_by_way = 4'b0010;
		expected_dest_PR_sel_by_way = {
			2'h0,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "bunch of crap 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b1101;
		tb_A_AR_by_way = {
			5'h9,
			5'h9,
			5'h9,
			5'h9
		};
		tb_B_AR_by_way = {
			5'h9,
			5'h9,
			5'h9,
			5'h9
		};
		tb_dest_AR_by_way = {
			5'h9,
			5'h9,
			5'h9,
			5'h9
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b1110;
		expected_A_PR_sel_by_way = {
			2'h2,
			2'h0,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b1110;
		expected_B_PR_sel_by_way = {
			2'h2,
			2'h0,
			2'h0,
			2'h0
		};
		expected_dest_PR_dep_by_way = 4'b1110;
		expected_dest_PR_sel_by_way = {
			2'h2,
			2'h0,
			2'h0,
			2'h0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "full crap";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs by way
		tb_regwrite_by_way = 4'b1111;
		tb_A_AR_by_way = {
			5'h22,
			5'h22,
			5'h22,
			5'h22
		};
		tb_B_AR_by_way = {
			5'h22,
			5'h22,
			5'h22,
			5'h22
		};
		tb_dest_AR_by_way = {
			5'h22,
			5'h22,
			5'h22,
			5'h22
		};
	    // outputs by way

		@(negedge CLK);

		// outputs:

	    // inputs by way
	    // outputs by way
		expected_A_PR_dep_by_way = 4'b1110;
		expected_A_PR_sel_by_way = {
			2'h2,
			2'h1,
			2'h0,
			2'h0
		};
		expected_B_PR_dep_by_way = 4'b1110;
		expected_B_PR_sel_by_way = {
			2'h2,
			2'h1,
			2'h0,
			2'h0
		};
		expected_dest_PR_dep_by_way = 4'b1110;
		expected_dest_PR_sel_by_way = {
			2'h2,
			2'h1,
			2'h0,
			2'h0
		};

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