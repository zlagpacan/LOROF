/*
    Filename: pe2_lsb_tb.sv
    Author: zlagpacan
    Description: Testbench for pe2_lsb module. 
    Spec: LOROF/spec/design/pe2_lsb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter WIDTH = 8;

module pe2_lsb_tb ();

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
	logic [WIDTH-1:0] tb_req_vec;

	logic [WIDTH-1:0] DUT_ack_one_hot, expected_ack_one_hot;
	logic [$clog2(WIDTH)-1:0] DUT_ack_index, expected_ack_index;

    logic DUT_found_first, expected_found_first;
    logic DUT_found_second, expected_found_second;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pe2_lsb #(
		.WIDTH(WIDTH)
	) DUT (
		.req_vec(tb_req_vec),

		.ack_one_hot(DUT_ack_one_hot),
		.ack_index(DUT_ack_index),

        .found_first(DUT_found_first),
        .found_second(DUT_found_second)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ack_one_hot !== DUT_ack_one_hot) begin
			$display("TB ERROR: expected_ack_one_hot (%8b) != DUT_ack_one_hot (%8b)",
				expected_ack_one_hot, DUT_ack_one_hot);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack_index !== DUT_ack_index) begin
			$display("TB ERROR: expected_ack_index (%h) != DUT_ack_index (%h)",
				expected_ack_index, DUT_ack_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_found_first !== DUT_found_first) begin
			$display("TB ERROR: expected_found_first (%h) != DUT_found_first (%h)",
				expected_found_first, DUT_found_first);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_found_second !== DUT_found_second) begin
			$display("TB ERROR: expected_found_second (%h) != DUT_found_second (%h)",
				expected_found_second, DUT_found_second);
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

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_one_hot = 8'b00000000;
		expected_ack_index = 0;

		expected_found_first = 1'b0;
		expected_found_second = 1'b0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_one_hot = 8'b00000000;
		expected_ack_index = 0;

		expected_found_first = 1'b0;
		expected_found_second = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // enumerate all:
        test_case = "enumerate all";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 256; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req = %8b", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_req_vec = i;

            @(negedge CLK);

            // outputs:

            expected_ack_one_hot = 8'b00000000;
            expected_ack_index = 0;

            expected_found_first = 1'b0;
            expected_found_second = 1'b0;

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