/*
    Filename: nearest_index_tb.sv
    Author: zlagpacan
    Description: Testbench for nearest_index module. 
    Spec: LOROF/spec/design/nearest_index.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter VECTOR_WIDTH = 8;
parameter INDEX_WIDTH = $clog2(VECTOR_WIDTH);

module nearest_index_tb ();

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
	logic [VECTOR_WIDTH-1:0] tb_bit_vector;
	logic [INDEX_WIDTH-1:0] tb_target_index;

	logic DUT_bit_present, expected_bit_present;
	logic [INDEX_WIDTH-1:0] DUT_nearest_index, expected_nearest_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	nearest_index #(
		.VECTOR_WIDTH(VECTOR_WIDTH),
		.INDEX_WIDTH(INDEX_WIDTH)
	) DUT (
		.bit_vector(tb_bit_vector),
		.target_index(tb_target_index),

		.bit_present(DUT_bit_present),
		.nearest_index(DUT_nearest_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_bit_present !== DUT_bit_present) begin
			$display("TB ERROR: expected_bit_present (%h) != DUT_bit_present (%h)",
				expected_bit_present, DUT_bit_present);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_nearest_index !== DUT_nearest_index) begin
			$display("TB ERROR: expected_nearest_index (%h) != DUT_nearest_index (%h)",
				expected_nearest_index, DUT_nearest_index);
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
		tb_bit_vector = 8'b00000000;
		tb_target_index = 3'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_bit_present = 1'b0;
		expected_nearest_index = 3'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_bit_vector = 8'b00000000;
		tb_target_index = 3'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_bit_present = 1'b0;
		expected_nearest_index = 3'h0;

		check_outputs();

        // ------------------------------------------------------------
        // enumerate for target 0:
        test_case = "enumerate for target 0";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 256; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("tb_bit_vector = %8b, tb_target_index = %h", 
                i, 0);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_bit_vector = i;
            tb_target_index = 3'h0;

            @(negedge CLK);

            // outputs:

            expected_bit_present = i > 0;
            // expected_nearest_index = 0;
            expected_nearest_index = 
                i == 0 ? 0
                : i[0] ? 0
                : i[1] ? 1
                : i[7] ? 7
                : i[2] ? 2
                : i[6] ? 6
                : i[3] ? 3
                : i[5] ? 5
                : 4;

            check_outputs();
        end

        // ------------------------------------------------------------
        // enumerate for target 4:
        test_case = "enumerate for target 4";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 256; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("tb_bit_vector = %8b, tb_target_index = %h", 
                i, 0);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_bit_vector = i;
            tb_target_index = 3'h4;

            @(negedge CLK);

            // outputs:

            expected_bit_present = i > 0;
            // expected_nearest_index = 0;
            expected_nearest_index = 
                i == 0 ? 0
                : i[4] ? 4
                : i[5] ? 5
                : i[3] ? 3
                : i[6] ? 6
                : i[2] ? 2
                : i[7] ? 7
                : i[1] ? 1
                : 0;

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