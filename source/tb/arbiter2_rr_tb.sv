/*
    Filename: arbiter2_rr_tb.sv
    Author: zlagpacan
    Description: Testbench for arbiter2_rr module. 
    Spec: LOROF/spec/design/arbiter2_rr.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module arbiter2_rr_tb #(
	parameter REQUESTOR_COUNT = 8,
	parameter LOG_REQUESTOR_COUNT = $clog2(REQUESTOR_COUNT)
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

	logic tb_req_valid;
	logic [REQUESTOR_COUNT-1:0] tb_req_vec;

	logic DUT_port0_ack_valid, expected_port0_ack_valid;
	logic [REQUESTOR_COUNT-1:0] DUT_port0_ack_one_hot, expected_port0_ack_one_hot;

	logic DUT_port1_ack_valid, expected_port1_ack_valid;
	logic [REQUESTOR_COUNT-1:0] DUT_port1_ack_one_hot, expected_port1_ack_one_hot;

    // ----------------------------------------------------------------
    // DUT instantiation:

	arbiter2_rr #(
		.REQUESTOR_COUNT(REQUESTOR_COUNT),
		.LOG_REQUESTOR_COUNT(LOG_REQUESTOR_COUNT)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

		.req_valid(tb_req_valid),
		.req_vec(tb_req_vec),

		.port0_ack_valid(DUT_port0_ack_valid),
		.port0_ack_one_hot(DUT_port0_ack_one_hot),

		.port1_ack_valid(DUT_port1_ack_valid),
		.port1_ack_one_hot(DUT_port1_ack_one_hot)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_port0_ack_valid !== DUT_port0_ack_valid) begin
			$display("TB ERROR: expected_port0_ack_valid (%h) != DUT_port0_ack_valid (%h)",
				expected_port0_ack_valid, DUT_port0_ack_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_port0_ack_one_hot !== DUT_port0_ack_one_hot) begin
			$display("TB ERROR: expected_port0_ack_one_hot (%h) != DUT_port0_ack_one_hot (%h)",
				expected_port0_ack_one_hot, DUT_port0_ack_one_hot);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_port1_ack_valid !== DUT_port1_ack_valid) begin
			$display("TB ERROR: expected_port1_ack_valid (%h) != DUT_port1_ack_valid (%h)",
				expected_port1_ack_valid, DUT_port1_ack_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_port1_ack_one_hot !== DUT_port1_ack_one_hot) begin
			$display("TB ERROR: expected_port1_ack_one_hot (%h) != DUT_port1_ack_one_hot (%h)",
				expected_port1_ack_one_hot, DUT_port1_ack_one_hot);
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
		tb_req_valid = '0;
		tb_req_vec = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_port0_ack_valid = '0;
		expected_port0_ack_one_hot = '0;
		expected_port1_ack_valid = '0;
		expected_port1_ack_one_hot = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_valid = '0;
		tb_req_vec = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_port0_ack_valid = '0;
		expected_port0_ack_one_hot = '0;
		expected_port1_ack_valid = '0;
		expected_port1_ack_one_hot = '0;

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
		tb_req_valid = '0;
		tb_req_vec = '0;

		@(negedge CLK);

		// outputs:

		expected_port0_ack_valid = '0;
		expected_port0_ack_one_hot = '0;
		expected_port1_ack_valid = '0;
		expected_port1_ack_one_hot = '0;

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