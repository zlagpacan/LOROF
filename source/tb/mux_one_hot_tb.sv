/*
    Filename: mux_one_hot_tb.sv
    Author: zlagpacan
    Description: Testbench for mux_one_hot module. 
    Spec: LOROF/spec/design/mux_one_hot.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module mux_one_hot_tb #(
	parameter COUNT = 4,
	parameter WIDTH = 32
) ();

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
	logic [COUNT-1:0] tb_sel_one_hot;
	logic [COUNT-1:0][WIDTH-1:0] tb_data_by_requestor;

	logic [WIDTH-1:0] DUT_selected_data, expected_selected_data;

    // ----------------------------------------------------------------
    // DUT instantiation:

	mux_one_hot #(
		.COUNT(COUNT),
		.WIDTH(WIDTH)
	) DUT (
		.sel_one_hot(tb_sel_one_hot),
		.data_by_requestor(tb_data_by_requestor),

		.selected_data(DUT_selected_data)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_selected_data !== DUT_selected_data) begin
			$display("TB ERROR: expected_selected_data (%h) != DUT_selected_data (%h)",
				expected_selected_data, DUT_selected_data);
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
		tb_sel_one_hot = '0;
		tb_data_by_requestor = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_selected_data = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_sel_one_hot = '0;
		tb_data_by_requestor = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_selected_data = '0;

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "default";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_sel_one_hot = '0;
		tb_data_by_requestor = '0;

		@(negedge CLK);

		// outputs:

		expected_selected_data = '0;

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