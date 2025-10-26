/*
    Filename: free_list_tb.sv
    Author: zlagpacan
    Description: Testbench for free_list module. 
    Spec: LOROF/spec/design/free_list.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module free_list_tb ();

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

    // enqueue request
	logic [FREE_LIST_BANK_COUNT-1:0] tb_enq_req_valid_by_bank;
	logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0] tb_enq_req_PR_by_bank;

    // enqueue feedback
	logic [FREE_LIST_BANK_COUNT-1:0] DUT_enq_resp_ack_by_bank, expected_enq_resp_ack_by_bank;

    // dequeue request
	logic [FREE_LIST_BANK_COUNT-1:0] tb_deq_req_valid_by_bank;
	logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0] DUT_deq_req_PR_by_bank, expected_deq_req_PR_by_bank;

    // dequeue feedback
	logic [FREE_LIST_BANK_COUNT-1:0] DUT_deq_resp_ready_by_bank, expected_deq_resp_ready_by_bank;

    // ----------------------------------------------------------------
    // DUT instantiation:

	free_list #(
		.FREE_LIST_BANK_COUNT(FREE_LIST_BANK_COUNT),
		.LOG_FREE_LIST_BANK_COUNT(LOG_FREE_LIST_BANK_COUNT),
		.FREE_LIST_LENGTH_PER_BANK(FREE_LIST_LENGTH_PER_BANK),
		.LOG_FREE_LIST_LENGTH_PER_BANK(LOG_FREE_LIST_LENGTH_PER_BANK),
		.FREE_LIST_SHIFT_REG_ENTRIES(FREE_LIST_SHIFT_REG_ENTRIES),
		.FREE_LIST_LOWER_THRESHOLD(FREE_LIST_LOWER_THRESHOLD),
		.FREE_LIST_UPPER_THRESHOLD(FREE_LIST_UPPER_THRESHOLD)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // enqueue request
		.enq_req_valid_by_bank(tb_enq_req_valid_by_bank),
		.enq_req_PR_by_bank(tb_enq_req_PR_by_bank),

	    // enqueue feedback
		.enq_resp_ack_by_bank(DUT_enq_resp_ack_by_bank),

	    // dequeue request
		.deq_req_valid_by_bank(tb_deq_req_valid_by_bank),
		.deq_req_PR_by_bank(DUT_deq_req_PR_by_bank),

	    // dequeue feedback
		.deq_resp_ready_by_bank(DUT_deq_resp_ready_by_bank)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_enq_resp_ack_by_bank !== DUT_enq_resp_ack_by_bank) begin
			$display("TB ERROR: expected_enq_resp_ack_by_bank (%h) != DUT_enq_resp_ack_by_bank (%h)",
				expected_enq_resp_ack_by_bank, DUT_enq_resp_ack_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_req_PR_by_bank !== DUT_deq_req_PR_by_bank) begin
			$display("TB ERROR: expected_deq_req_PR_by_bank (%h) != DUT_deq_req_PR_by_bank (%h)",
				expected_deq_req_PR_by_bank, DUT_deq_req_PR_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_resp_ready_by_bank !== DUT_deq_resp_ready_by_bank) begin
			$display("TB ERROR: expected_deq_resp_ready_by_bank (%h) != DUT_deq_resp_ready_by_bank (%h)",
				expected_deq_resp_ready_by_bank, DUT_deq_resp_ready_by_bank);
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
	    // enqueue request
		tb_enq_req_valid_by_bank = 4'b0000;
		tb_enq_req_PR_by_bank = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};
	    // enqueue feedback
	    // dequeue request
		tb_deq_req_valid_by_bank = 4'b0000;
	    // dequeue feedback

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enqueue request
	    // enqueue feedback
		expected_enq_resp_ack_by_bank = 4'b0000;
	    // dequeue request
		expected_deq_req_PR_by_bank = {
			7'h23,
			7'h22,
			7'h21,
			7'h20
		};
	    // dequeue feedback
		expected_deq_resp_ready_by_bank = 4'b1111;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enqueue request
		tb_enq_req_valid_by_bank = 4'b0000;
		tb_enq_req_PR_by_bank = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};
	    // enqueue feedback
	    // dequeue request
		tb_deq_req_valid_by_bank = 4'b0000;
	    // dequeue feedback

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enqueue request
	    // enqueue feedback
		expected_enq_resp_ack_by_bank = 4'b0000;
	    // dequeue request
		expected_deq_req_PR_by_bank = {
			7'h23,
			7'h22,
			7'h21,
			7'h20
		};
	    // dequeue feedback
		expected_deq_resp_ready_by_bank = 4'b1111;

		check_outputs();

        // ------------------------------------------------------------
        // simple deq chain:
        test_case = "simple deq chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 32; i < 128; i+=4) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("deq [%2h:%2h+3]", i[6:0], i[6:0]);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// enqueue request
			tb_enq_req_valid_by_bank = 4'b0000;
			tb_enq_req_PR_by_bank = {
				7'h0,
				7'h0,
				7'h0,
				7'h0
			};
			// enqueue feedback
			// dequeue request
			tb_deq_req_valid_by_bank = 4'b1111;
			// dequeue feedback

			@(negedge CLK);

			// outputs:

			// enqueue request
			// enqueue feedback
			expected_enq_resp_ack_by_bank = 4'b0000;
			// dequeue request
			expected_deq_req_PR_by_bank = {
				{i+3}[6:0],
				{i+2}[6:0],
				{i+1}[6:0],
				{i+0}[6:0]
			};
			// dequeue feedback
			expected_deq_resp_ready_by_bank = 4'b1111;

			check_outputs();
		end

        // ------------------------------------------------------------
        // simple enq chain:
        test_case = "simple enq chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 127; i >= 0; i-=4) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("enq [%2h:%2h-3]", i[6:0], i[6:0]);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// enqueue request
			tb_enq_req_valid_by_bank = 4'b1111;
			tb_enq_req_PR_by_bank = {
				{i-3}[6:0],
				{i-2}[6:0],
				{i-1}[6:0],
				{i-0}[6:0]
			};
			// enqueue feedback
			// dequeue request
			tb_deq_req_valid_by_bank = 4'b0000;
			// dequeue feedback

			@(negedge CLK);

			// outputs:

			// enqueue request
			// enqueue feedback
			expected_enq_resp_ack_by_bank = 4'b1111;
			// dequeue request
			if (i > 120) begin
				expected_deq_req_PR_by_bank = {
					7'h0,
					7'h0,
					7'h0,
					7'h0
				};
			end else begin
				expected_deq_req_PR_by_bank = {
					7'h7c,
					7'h7d,
					7'h7e,
					7'h7f
				};
			end
			// dequeue feedback
			if (i > 120) begin
				expected_deq_resp_ready_by_bank = 4'b0000;
			end else begin
				expected_deq_resp_ready_by_bank = 4'b1111;
			end

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