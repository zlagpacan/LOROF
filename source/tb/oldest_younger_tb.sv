/*
    Filename: oldest_younger_tb.sv
    Author: zlagpacan
    Description: Testbench for oldest_younger module. 
    Spec: LOROF/spec/design/oldest_younger.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter VECTOR_WIDTH = 8;
parameter INDEX_WIDTH = $clog2(VECTOR_WIDTH);

module oldest_younger_tb ();

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
	logic [VECTOR_WIDTH-1:0] tb_req_vec;

	logic [INDEX_WIDTH-1:0] tb_head_index;
	logic [VECTOR_WIDTH-1:0] tb_head_mask;

	logic [INDEX_WIDTH-1:0] tb_target_index;
	logic [VECTOR_WIDTH-1:0] tb_target_mask;

	logic DUT_younger_present, expected_younger_present;
	logic [INDEX_WIDTH-1:0] DUT_oldest_younger_index, expected_oldest_younger_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	oldest_younger #(
		.VECTOR_WIDTH(VECTOR_WIDTH),
		.INDEX_WIDTH(INDEX_WIDTH)
	) DUT (
		.req_vec(tb_req_vec),

		.head_index(tb_head_index),
		.head_mask(tb_head_mask),

		.target_index(tb_target_index),
		.target_mask(tb_target_mask),

		.younger_present(DUT_younger_present),
		.oldest_younger_index(DUT_oldest_younger_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_younger_present !== DUT_younger_present) begin
			$display("TB ERROR: expected_younger_present (%h) != DUT_younger_present (%h)",
				expected_younger_present, DUT_younger_present);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_oldest_younger_index !== DUT_oldest_younger_index) begin
			$display("TB ERROR: expected_oldest_younger_index (%h) != DUT_oldest_younger_index (%h)",
				expected_oldest_younger_index, DUT_oldest_younger_index);
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
		tb_req_vec = 8'b00000000;
		tb_head_index = 3'h0;
		tb_head_mask = 8'b11111111;
		tb_target_index = 3'h0;
		tb_target_mask = 8'b11111111;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_younger_present = 1'b0;
		expected_oldest_younger_index = 3'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b00000000;
		tb_head_index = 3'h0;
		tb_head_mask = 8'b11111111;
		tb_target_index = 3'h0;
		tb_target_mask = 8'b11111111;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_younger_present = 1'b0;
		expected_oldest_younger_index = 3'h0;

		check_outputs();

        // ------------------------------------------------------------
        // head = 1, target = 5:
        test_case = "head = 1, target = 5";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 2**8; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("head = 1, target = 5, req = %8b", i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			tb_req_vec = i;
			tb_head_index = 3'h1;
			tb_head_mask = 8'b11111110;
			tb_target_index = 3'h5;
			tb_target_mask = 8'b11100000;

			@(negedge CLK);

			// outputs:

			expected_younger_present = |i[7:5] | i[0];
			expected_oldest_younger_index = 
				i[5] ? 5
				: i[6] ? 6
				: i[7] ? 7
				: i[0] ? 0
				: i[1] ? 1
				: i[2] ? 2
				: i[3] ? 3
				: i[4] ? 4
				: 0
			;

			check_outputs();
		end

        // ------------------------------------------------------------
        // head = 7, target = 5:
        test_case = "head = 7, target = 5";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 2**8; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("head = 7, target = 5, req = %8b", i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			tb_req_vec = i;
			tb_head_index = 3'h7;
			tb_head_mask = 8'b10000000;
			tb_target_index = 3'h5;
			tb_target_mask = 8'b11100000;

			@(negedge CLK);

			// outputs:

			expected_younger_present = |i[6:5];
			expected_oldest_younger_index = 
				i[5] ? 5
				: i[6] ? 6
				: 0
			;

			check_outputs();
		end

        // ------------------------------------------------------------
        // head = 3, target = 6:
        test_case = "head = 3, target = 6";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 2**8; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("head = 3, target = 6, req = %8b", i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			tb_req_vec = i;
			tb_head_index = 3'h3;
			tb_head_mask = 8'b11111000;
			tb_target_index = 3'h6;
			tb_target_mask = 8'b11000000;

			@(negedge CLK);

			// outputs:

			expected_younger_present = |i[7:6] | |i[2:0];
			expected_oldest_younger_index = 
				i[6] ? 6
				: i[7] ? 7
				: i[0] ? 0
				: i[1] ? 1
				: i[2] ? 2
				: i[3] ? 3
				: i[4] ? 4
				: i[5] ? 5
				: 0
			;

			check_outputs();
		end

        // ------------------------------------------------------------
        // head = 5, target = 4:
        test_case = "head = 5, target = 4";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 2**8; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("head = 5, target = 4, req = %8b", i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			tb_req_vec = i;
			tb_head_index = 3'h5;
			tb_head_mask = 8'b11100000;
			tb_target_index = 3'h4;
			tb_target_mask = 8'b11110000;

			@(negedge CLK);

			// outputs:

			expected_younger_present = i[4];
			expected_oldest_younger_index = 
				i[4] ? 4
				: 0
			;

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