/*
    Filename: ready_table_tb.sv
    Author: zlagpacan
    Description: Testbench for ready_table module. 
    Spec: LOROF/spec/design/ready_table.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ready_table_tb ();

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


    // 8x read ports
	logic [7:0][LOG_PR_COUNT-1:0] tb_read_PR_by_port;
	logic [7:0] DUT_read_ready_by_port, expected_read_ready_by_port;

    // 4x set ports
	logic [3:0] tb_set_valid_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] tb_set_PR_by_port;

    // 4x clear ports
	logic [3:0] tb_clear_valid_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] tb_clear_PR_by_port;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ready_table DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // 8x read ports
		.read_PR_by_port(tb_read_PR_by_port),
		.read_ready_by_port(DUT_read_ready_by_port),

	    // 4x set ports
		.set_valid_by_port(tb_set_valid_by_port),
		.set_PR_by_port(tb_set_PR_by_port),

	    // 4x clear ports
		.clear_valid_by_port(tb_clear_valid_by_port),
		.clear_PR_by_port(tb_clear_PR_by_port)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_ready_by_port !== DUT_read_ready_by_port) begin
			$display("TB ERROR: expected_read_ready_by_port (%h) != DUT_read_ready_by_port (%h)",
				expected_read_ready_by_port, DUT_read_ready_by_port);
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
	    // 8x read ports
		tb_read_PR_by_port = {
			7'h0,
			7'h1,
			7'h2,
			7'h3,
			7'h4,
			7'h5,
			7'h6,
			7'h7
		};
	    // 4x set ports
		tb_set_valid_by_port = 4'b0000;
		tb_set_PR_by_port = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};
	    // 4x clear ports
		tb_clear_valid_by_port = 4'b0000;
		tb_clear_PR_by_port = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // 8x read ports
		expected_read_ready_by_port = 8'b11111111;
	    // 4x set ports
	    // 4x clear ports

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // 8x read ports
		tb_read_PR_by_port = {
			7'h0,
			7'h1,
			7'h2,
			7'h3,
			7'h4,
			7'h5,
			7'h6,
			7'h7
		};
	    // 4x set ports
		tb_set_valid_by_port = 4'b0000;
		tb_set_PR_by_port = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};
	    // 4x clear ports
		tb_clear_valid_by_port = 4'b0000;
		tb_clear_PR_by_port = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // 8x read ports
		expected_read_ready_by_port = 8'b11111111;
	    // 4x set ports
	    // 4x clear ports

		check_outputs();

        // ------------------------------------------------------------
        // read reset vals:
        test_case = "read reset vals";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 128; i += 8) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("read %0d:%0d", i, i+7);;
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// 8x read ports
			tb_read_PR_by_port = {
				{i + 7}[6:0],
				{i + 6}[6:0],
				{i + 5}[6:0],
				{i + 4}[6:0],
				{i + 3}[6:0],
				{i + 2}[6:0],
				{i + 1}[6:0],
				{i + 0}[6:0]
			};
			// 4x set ports
			tb_set_valid_by_port = 4'b0000;
			tb_set_PR_by_port = {
				7'h0,
				7'h0,
				7'h0,
				7'h0
			};
			// 4x clear ports
			tb_clear_valid_by_port = 4'b0000;
			tb_clear_PR_by_port = {
				7'h0,
				7'h0,
				7'h0,
				7'h0
			};

			@(negedge CLK);

			// outputs:

			// 8x read ports
			if (i < 32) begin
				expected_read_ready_by_port = 8'b11111111;
			end
			else begin
				expected_read_ready_by_port = 8'b00000000;
			end
			// 4x set ports
			// 4x clear ports

			check_outputs();
		end

        // ------------------------------------------------------------
        // set evens, clear odds:
        test_case = "set evens, clear odds";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 128; i += 4) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("set %0h,%0h,%0h,%0h; clear %0h,%0h,%0h,%0h", 
				i, i+2, i+4, i+6, i+1, i+3, i+5, i+7);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// 8x read ports
			tb_read_PR_by_port = {
				{i + 7}[6:0],
				{i + 6}[6:0],
				{i + 5}[6:0],
				{i + 4}[6:0],
				{i + 3}[6:0],
				{i + 2}[6:0],
				{i + 1}[6:0],
				{i + 0}[6:0]
			};
			// 4x set ports
			tb_set_valid_by_port = 4'b1111;
			tb_set_PR_by_port = {
				{i + 6}[6:0],
				{i + 4}[6:0],
				{i + 2}[6:0],
				{i + 0}[6:0]
			};
			// 4x clear ports
			tb_clear_valid_by_port = 4'b1111;
			tb_clear_PR_by_port = {
				{i + 7}[6:0],
				{i + 5}[6:0],
				{i + 3}[6:0],
				{i + 1}[6:0]
			};

			@(negedge CLK);

			// outputs:

			// 8x read ports
			expected_read_ready_by_port = 8'b01010101;
			// 4x set ports
			// 4x clear ports

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