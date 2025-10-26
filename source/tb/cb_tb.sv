/*
    Filename: cb_tb.sv
    Author: zlagpacan
    Description: Testbench for cb module. 
    Spec: LOROF/spec/design/cb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter DATA_WIDTH = 32;
parameter NUM_ENTRIES = 4;
parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES);

module cb_tb ();

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

    // enq
	logic tb_enq_valid;
	logic [DATA_WIDTH-1:0] tb_enq_data;

    // deq
	logic DUT_deq_valid, expected_deq_valid;
	logic [DATA_WIDTH-1:0] DUT_deq_data, expected_deq_data;

    // deq feedback
	logic tb_deq_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	cb #(
		.DATA_WIDTH(DATA_WIDTH),
		.NUM_ENTRIES(NUM_ENTRIES),
		.LOG_NUM_ENTRIES(LOG_NUM_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // enq
		.enq_valid(tb_enq_valid),
		.enq_data(tb_enq_data),

	    // deq
		.deq_valid(DUT_deq_valid),
		.deq_data(DUT_deq_data),

	    // deq feedback
		.deq_ready(tb_deq_ready)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_deq_valid !== DUT_deq_valid) begin
			$display("TB ERROR: expected_deq_valid (%h) != DUT_deq_valid (%h)",
				expected_deq_valid, DUT_deq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_data !== DUT_deq_data) begin
			$display("TB ERROR: expected_deq_data (%h) != DUT_deq_data (%h)",
				expected_deq_data, DUT_deq_data);
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
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h0;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h0;
	    // deq feedback

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h0;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h0;
	    // deq feedback

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} enq 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hf0f0f0f0;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h0;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, i, i, i} enq 1, deq 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'he1e1e1e1;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hf0f0f0f0;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, 1, i, i} enq 2, deq 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hd2d2d2d2;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'he1e1e1e1;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, 2, i} enq 3, deq 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hc3c3c3c3;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hd2d2d2d2;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, 3} enq 4, deq 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hb4b4b4b4;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hc3c3c3c3;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, i, i, i} enq 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'ha5a5a5a5;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hb4b4b4b4;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, 5, i, i} enq 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h96969696;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hb4b4b4b4;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, 5, 6, i} enq 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h87878787;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hb4b4b4b4;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, 5, 6, 7} enq 8";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h78787878;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hb4b4b4b4;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{8, 5, 6, 7} enq 9, deq 8";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h69696969;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'h78787878;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, 9, 6, 7} enq A, deq 9";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h5a5a5a5a;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'h69696969;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, A, 7} enq B, deq A";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h4b4b4b4b;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'h5a5a5a5a;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, B} enq C, deq B";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h3c3c3c3c;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'h4b4b4b4b;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{C, i, i, i} deq C";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'hdeadbeef;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'h3c3c3c3c;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} enq D";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h2d2d2d2d;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h69696969;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, D, i, i} deq D";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'hdeadbeef;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'h2d2d2d2d;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i}";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'hdeadbeef;
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h5a5a5a5a;
	    // deq feedback

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