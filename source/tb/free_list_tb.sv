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
		.EGRESS_BUFFER_ENTRIES(EGRESS_BUFFER_ENTRIES),
        .INIT_FILES_BY_WAY(INIT_FILES_BY_WAY)
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

        for (int way = 4; way >= 0; way--) begin
            if (expected_deq_pr_by_way[way] !== DUT_deq_pr_by_way[way]) begin
                $display("TB ERROR: expected_deq_pr_by_way[%0h] (%0d'h%h) != DUT_deq_pr_by_way[%0h] (%0d'h%h)",
                    way, $bits(expected_deq_pr_by_way[way]), expected_deq_pr_by_way[way],
                    way, $bits(DUT_deq_pr_by_way[way]), DUT_deq_pr_by_way[way]);
                num_errors++;
                tb_error = 1'b1;
            end
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
        // deq + enq stream:
        test_case = "deq + enq stream";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq cycle 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

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

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq cycle 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1110;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h47, 7'h46, 7'h45, 7'h44};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq cycle 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1101;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h4b, 7'h4a, 7'h49, 7'h44};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq cycle 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1011;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h4f, 7'h4e, 7'h49, 7'h48};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq cycle 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b0111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h53, 7'h4e, 7'h4d, 7'h4c};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b1111;
		tb_enq_pr_by_way = {7'h03, 7'h02, 7'h01, 7'h00};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h53, 7'h52, 7'h51, 7'h50};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0011;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h05, 7'h04};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h57, 7'h56, 7'h55, 7'h54};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0111;
		tb_enq_pr_by_way = {7'h7f, 7'h08, 7'h07, 7'h06};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h5b, 7'h5a, 7'h59, 7'h58};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b1000;
		tb_enq_pr_by_way = {7'h09, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h5f, 7'h5e, 7'h5d, 7'h5c};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0101;
		tb_enq_pr_by_way = {7'h7f, 7'h0b, 7'h7f, 7'h0a};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h63, 7'h62, 7'h61, 7'h60};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0001;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h0c};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h67, 7'h66, 7'h65, 7'h64};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0101;
		tb_enq_pr_by_way = {7'h7f, 7'h0e, 7'h7f, 7'h0d};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h6b, 7'h6a, 7'h69, 7'h68};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b1111;
		tb_enq_pr_by_way = {7'h12, 7'h11, 7'h10, 7'h0f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h6f, 7'h6e, 7'h6d, 7'h6c};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 8";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b1010;
		tb_enq_pr_by_way = {7'h14, 7'h7f, 7'h13, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h73, 7'h72, 7'h71, 7'h70};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 9";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0111;
		tb_enq_pr_by_way = {7'h7f, 7'h17, 7'h16, 7'h15};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h77, 7'h76, 7'h75, 7'h74};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle A";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0101;
		tb_enq_pr_by_way = {7'h7f, 7'h19, 7'h7f, 7'h18};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h7b, 7'h7a, 7'h79, 7'h78};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle B";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0110;
		tb_enq_pr_by_way = {7'h7f, 7'h1b, 7'h1a, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h7f, 7'h7e, 7'h7d, 7'h7c};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle C";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0101;
		tb_enq_pr_by_way = {7'h7f, 7'h1d, 7'h7f, 7'h1c};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h03, 7'h02, 7'h01, 7'h00}; // got lucky that the cycle when enq'd was realigned
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle D";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0011;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h1f, 7'h1e};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h04, 7'h06, 7'h0f, 7'h05};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle E";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h07, 7'h0b, 7'h13, 7'h08};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle F";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1111;
		expected_deq_pr_by_way = {7'h0c, 7'h0d, 7'h17, 7'h09};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 10";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1101;
		expected_deq_pr_by_way = {7'h11, 7'h10, 7'h51, 7'h0a};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 11";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1101;
		expected_deq_pr_by_way = {7'h14, 7'h18, 7'h51, 7'h0e};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 12";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1101;
		expected_deq_pr_by_way = {7'h15, 7'h1a, 7'h51, 7'h12};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 12";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1101;
		expected_deq_pr_by_way = {7'h1b, 7'h1d, 7'h51, 7'h16};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 13";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b1001;
		expected_deq_pr_by_way = {7'h1e, 7'h62, 7'h51, 7'h19};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 13";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b0001;
		expected_deq_pr_by_way = {7'h67, 7'h62, 7'h51, 7'h1c};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 14";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b0001;
		expected_deq_pr_by_way = {7'h67, 7'h62, 7'h51, 7'h1f};
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "deq + enq cycle 15";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid_by_way = 4'b0000;
		tb_enq_pr_by_way = {7'h7f, 7'h7f, 7'h7f, 7'h7f};
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready_by_way = 4'b1111;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready_by_way = 4'b1111;
	    // deq
		expected_deq_valid_by_way = 4'b0000;
		expected_deq_pr_by_way = {7'h67, 7'h62, 7'h51, 7'h6c};
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