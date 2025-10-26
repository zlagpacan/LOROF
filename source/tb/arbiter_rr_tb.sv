/*
    Filename: arbiter_rr_tb.sv
    Author: zlagpacan
    Description: Testbench for arbiter_rr module. 
    Spec: LOROF/spec/design/arbiter_rr.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter REQUESTER_COUNT = 4;
parameter LOG_REQUESTER_COUNT = $clog2(REQUESTER_COUNT);

module arbiter_rr_tb ();

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

	logic [REQUESTER_COUNT-1:0] tb_req_vec;
	logic DUT_req_present, expected_req_present;

	logic tb_ack_ready;
	logic [REQUESTER_COUNT-1:0] DUT_ack_one_hot, expected_ack_one_hot;
	logic [LOG_REQUESTER_COUNT-1:0] DUT_ack_index, expected_ack_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	arbiter_rr #(
		.REQUESTER_COUNT(REQUESTER_COUNT),
		.LOG_REQUESTER_COUNT(LOG_REQUESTER_COUNT)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

		.req_vec(tb_req_vec),
		.req_present(DUT_req_present),

		.ack_ready(tb_ack_ready),
		.ack_one_hot(DUT_ack_one_hot),
		.ack_index(DUT_ack_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_req_present !== DUT_req_present) begin
			$display("TB ERROR: expected_req_present (%h) != DUT_req_present (%h)",
				expected_req_present, DUT_req_present);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack_one_hot !== DUT_ack_one_hot) begin
			$display("TB ERROR: expected_ack_one_hot (%h) != DUT_ack_one_hot (%h)",
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
		tb_req_vec = 4'b0000;
		tb_ack_ready = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_req_present = 1'b0;
		expected_ack_one_hot = 4'b0000;
		expected_ack_index = 2'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b0000;
		tb_ack_ready = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_req_present = 1'b0;
		expected_ack_one_hot = 4'b0000;
		expected_ack_index = 2'h0;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1111 -> 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1111;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0001;
		expected_ack_index = 2'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1111 -> 1 (stall)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1111;
		tb_ack_ready = 1'b0;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0000;
		expected_ack_index = 2'h1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1111 -> 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1111;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0010;
		expected_ack_index = 2'h1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1111 -> 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1111;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0100;
		expected_ack_index = 2'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1111 -> 3 (stall)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1111;
		tb_ack_ready = 1'b0;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0000;
		expected_ack_index = 2'h3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1111 -> 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1111;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b1000;
		expected_ack_index = 2'h3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1111 -> 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1111;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0001;
		expected_ack_index = 2'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1110 -> 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1110;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0010;
		expected_ack_index = 2'h1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1110 -> 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1110;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0100;
		expected_ack_index = 2'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1010 -> 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1010;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b1000;
		expected_ack_index = 2'h3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1010 -> 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1010;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0010;
		expected_ack_index = 2'h1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1001 -> 3 (stall 0)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1001;
		tb_ack_ready = 1'b0;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0000;
		expected_ack_index = 2'h3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1001 -> 3 (stall 1)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1001;
		tb_ack_ready = 1'b0;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0000;
		expected_ack_index = 2'h3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1001 -> 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b1001;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b1000;
		expected_ack_index = 2'h3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "0101 -> 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b0101;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0001;
		expected_ack_index = 2'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "0110 -> 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b0110;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b1;
		expected_ack_one_hot = 4'b0010;
		expected_ack_index = 2'h1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "0000 -> 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 4'b0000;
		tb_ack_ready = 1'b1;

		@(negedge CLK);

		// outputs:

		expected_req_present = 1'b0;
		expected_ack_one_hot = 4'b0000;
		expected_ack_index = 2'h0;

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