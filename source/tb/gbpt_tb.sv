/*
    Filename: gbpt_tb.sv
    Author: zlagpacan
    Description: Testbench for gbpt module. 
    Spec: LOROF/spec/design/gbpt.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module gbpt_tb #(
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


    // arch state
	corep::ASID_t tb_arch_asid;

    // read req stage
	logic tb_read_req_valid;
	corep::fetch_idx_t tb_read_req_fetch_index;
	corep::GH_t tb_read_req_gh;

    // read resp stage
	logic [corep::FETCH_LANES-1:0] DUT_read_resp_taken_by_lane, expected_read_resp_taken_by_lane;

    // update
	logic tb_update_valid;
	corep::PC38_t tb_update_pc38;
	corep::GH_t tb_update_gh;
	logic tb_update_taken;

    // ----------------------------------------------------------------
    // DUT instantiation:

	gbpt #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // arch state
		.arch_asid(tb_arch_asid),

	    // read req stage
		.read_req_valid(tb_read_req_valid),
		.read_req_fetch_index(tb_read_req_fetch_index),
		.read_req_gh(tb_read_req_gh),

	    // read resp stage
		.read_resp_taken_by_lane(DUT_read_resp_taken_by_lane),

	    // update
		.update_valid(tb_update_valid),
		.update_pc38(tb_update_pc38),
		.update_gh(tb_update_gh),
		.update_taken(tb_update_taken)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_resp_taken_by_lane !== DUT_read_resp_taken_by_lane) begin
			$display("TB ERROR: expected_read_resp_taken_by_lane (%h) != DUT_read_resp_taken_by_lane (%h)",
				expected_read_resp_taken_by_lane, DUT_read_resp_taken_by_lane);
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
	    // arch state
		tb_arch_asid = 16'h0000;
	    // read req stage
		tb_read_req_valid = 1'b0;
		tb_read_req_fetch_index = 9'h000;
		tb_read_req_gh = 9'h000;
	    // read resp stage
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_gh = 9'h000;
		tb_update_taken = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_taken_by_lane = 8'b00000000;
	    // update

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // arch state
		tb_arch_asid = 16'h0000;
	    // read req stage
		tb_read_req_valid = 1'b0;
		tb_read_req_fetch_index = 9'h000;
		tb_read_req_gh = 9'h000;
	    // read resp stage
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_gh = 9'h000;
		tb_update_taken = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_taken_by_lane = 8'b00000000;
	    // update

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
	    // arch state
		tb_arch_asid = 16'h0000;
	    // read req stage
		tb_read_req_valid = 1'b0;
		tb_read_req_fetch_index = 9'h000;
		tb_read_req_gh = 9'h000;
	    // read resp stage
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_gh = 9'h000;
		tb_update_taken = 1'b0;

		@(negedge CLK);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_taken_by_lane = 8'b00000000;
	    // update

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