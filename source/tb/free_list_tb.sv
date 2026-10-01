/*
    Filename: free_list_tb.sv
    Author: zlagpacan
    Description: Testbench for free_list module. 
    Spec: LOROF/spec/design/free_list.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module free_list_tb #(
	parameter int unsigned INGRESS_BUFFER_ENTRIES = 16,
	parameter int unsigned EGRESS_BUFFER_ENTRIES = 16,
    parameter string INIT_FILES_BY_WAY [0:3] = {"free_list_way0.mem", "free_list_way1.mem", "free_list_way2.mem", "free_list_way3.mem"}
) ();

    // ----------------------------------------------------------------
    // TB setup:

    // parameters
    parameter int unsigned PERIOD = 10;

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
	logic [3:0] tb_enq_valid_by_way;
	corep::pr_t [3:0] tb_enq_pr_by_way;

    // enq feedback
	logic [3:0] DUT_enq_ready_by_way, expected_enq_ready_by_way;

    // deq
	logic [3:0] DUT_deq_valid_by_way, expected_deq_valid_by_way;
	corep::pr_t [3:0] DUT_deq_pr_by_way, expected_deq_pr_by_way;

    // deq feedback
	logic [3:0] tb_deq_ready_by_way;

    // ----------------------------------------------------------------
    // DUT instantiation:

	free_list #(
		.INGRESS_BUFFER_ENTRIES(INGRESS_BUFFER_ENTRIES),
		.EGRESS_BUFFER_ENTRIES(EGRESS_BUFFER_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // enq
		.enq_valid_by_way(tb_enq_valid_by_way),
		.enq_pr_by_way(tb_enq_pr_by_way),

	    // enq feedback
		.enq_ready_by_way(DUT_enq_ready_by_way),

	    // deq
		.deq_valid_by_way(DUT_deq_valid_by_way),
		.deq_pr_by_way(DUT_deq_pr_by_way),

	    // deq feedback
		.deq_ready_by_way(tb_deq_ready_by_way)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_enq_ready_by_way !== DUT_enq_ready_by_way) begin
			$display("TB ERROR: expected_enq_ready_by_way (%0d'h%h) != DUT_enq_ready_by_way (%0d'h%h)",
				$bits(expected_enq_ready_by_way), expected_enq_ready_by_way,
				$bits(DUT_enq_ready_by_way), DUT_enq_ready_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_valid_by_way !== DUT_deq_valid_by_way) begin
			$display("TB ERROR: expected_deq_valid_by_way (%0d'h%h) != DUT_deq_valid_by_way (%0d'h%h)",
				$bits(expected_deq_valid_by_way), expected_deq_valid_by_way,
				$bits(DUT_deq_valid_by_way), DUT_deq_valid_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_pr_by_way !== DUT_deq_pr_by_way) begin
			$display("TB ERROR: expected_deq_pr_by_way (%0d'h%h) != DUT_deq_pr_by_way (%0d'h%h)",
				$bits(expected_deq_pr_by_way), expected_deq_pr_by_way,
				$bits(DUT_deq_pr_by_way), DUT_deq_pr_by_way);
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
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b0000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h43, 7'h42, 7'h41, 7'h40};
	    // deq feedback

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b0000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h43, 7'h42, 7'h41, 7'h40};
	    // deq feedback

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
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b0000;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h43, 7'h42, 7'h41, 7'h40};
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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule