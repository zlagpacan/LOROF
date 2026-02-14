/*
    Filename: pht_tb.sv
    Author: zlagpacan
    Description: Testbench for pht module. 
    Spec: LOROF/spec/design/pht.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module pht_tb #(
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


    // read req stage
	logic tb_read_req_valid;
	corep::fetch_idx_t tb_read_req_fetch_idx;
	corep::gh_t tb_read_req_gh;
	corep::asid_t tb_read_req_asid;

    // read resp stage
	corep::fetch_lane_t tb_read_resp_redirect_lane;

	logic DUT_read_resp_taken, expected_read_resp_taken;

    // update
	logic tb_update_valid;
	corep::pc38_t tb_update_pc38;
	corep::gh_t tb_update_gh;
	corep::asid_t tb_update_asid;
	logic tb_update_taken;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pht #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // read req stage
		.read_req_valid(tb_read_req_valid),
		.read_req_fetch_idx(tb_read_req_fetch_idx),
		.read_req_gh(tb_read_req_gh),
		.read_req_asid(tb_read_req_asid),

	    // read resp stage
		.read_resp_redirect_lane(tb_read_resp_redirect_lane),

		.read_resp_taken(DUT_read_resp_taken),

	    // update
		.update_valid(tb_update_valid),
		.update_pc38(tb_update_pc38),
		.update_gh(tb_update_gh),
		.update_asid(tb_update_asid),
		.update_taken(tb_update_taken)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_resp_taken !== DUT_read_resp_taken) begin
			$display("TB ERROR: expected_read_resp_taken (%h) != DUT_read_resp_taken (%h)",
				expected_read_resp_taken, DUT_read_resp_taken);
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
	    // read req stage
		tb_read_req_valid = 1'b0;
		tb_read_req_fetch_idx = 9'h000;
		tb_read_req_gh = {2'h0, 9'h000, 3'h0};
		tb_read_req_asid = 16'h0000;
	    // read resp stage
		tb_read_resp_redirect_lane = 3'h0;
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_gh = {2'h0, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
		tb_update_taken = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_taken = 1'b0;
	    // update

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req stage
		tb_read_req_valid = 1'b0;
		tb_read_req_fetch_idx = 9'h000;
		tb_read_req_gh = {2'h0, 9'h000, 3'h0};
		tb_read_req_asid = 16'h0000;
	    // read resp stage
		tb_read_resp_redirect_lane = 3'h0;
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_gh = {2'h0, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
		tb_update_taken = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_taken = 1'b0;
	    // update

		check_outputs();

        // ------------------------------------------------------------
        // fill evens taken, odds not taken:
        test_case = "fill evens taken, odds not taken";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int index = 0; index < corep::PHT_SETS; index++) begin
            for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin

                @(posedge CLK); #(PERIOD/10);

                // inputs
                sub_test_case = $sformatf("index = 0x%03h, lane = %1h", index, lane);
                $display("\t- sub_test: %s", sub_test_case);

                // reset
                nRST = 1'b1;
                // read req stage
                tb_read_req_valid = 1'b0;
                tb_read_req_fetch_idx = 9'h000;
                tb_read_req_gh = {2'h0, 9'h000, 3'h0};
		        tb_read_req_asid = 16'h0000;
                // read resp stage
		        tb_read_resp_redirect_lane = 3'h0;
                // update
                tb_update_valid = 1'b1;
                tb_update_pc38 = {26'h0000000, {4'h0, index[4:0]}, lane[2], 1'b0, lane[0]};
                tb_update_gh = {index[10:9], {index[8:5], 5'h0}, 1'b0, lane[1], 1'b0};
		        tb_update_asid = 16'h0000;
                tb_update_taken = lane[2:0] >= index[2:0];

                @(negedge CLK);

                // outputs:

                // arch state
                // read req stage
                // read resp stage
		        expected_read_resp_taken = 1'b0;
                // update

                check_outputs();
            end
        end

        // ------------------------------------------------------------
        // readout:
        test_case = "readout";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%03h lane = %1h", 9'h000, 3'h0);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = ~9'h000;
        tb_read_req_gh = {2'h3, 9'h000, 3'h0};
		tb_read_req_asid = 16'hffff;
        // read resp stage
		tb_read_resp_redirect_lane = 3'h0;
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_gh = {2'h0, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_taken = 1'b0;

        @(negedge CLK);

        // outputs:

        // arch state
        // read req stage
        // read resp stage
		expected_read_resp_taken = 1'b0;
        // update

        check_outputs();

        for (int index = 0; index < corep::PHT_SETS; index++) begin

            for (int lane = (index == 0 ? 1 : 0); lane < corep::FETCH_LANES; lane++) begin

                @(posedge CLK); #(PERIOD/10);

                // inputs
                sub_test_case = $sformatf("req index = 0x%03h lane = %1h, resp index = 0x%03h lane = %1h", index, lane, (lane == 0) ? index-1 : index, {lane-1}[2:0]);
                $display("\t- sub_test: %s", sub_test_case);

                // reset
                nRST = 1'b1;
                // read req stage
                tb_read_req_valid = 1'b1;
                tb_read_req_fetch_idx = ~{index[8:5], 5'h0};
                tb_read_req_gh = {~index[10:9], {4'h0, index[4:0]}, lane[2], 1'b0, lane[0]};
                tb_read_req_asid = 16'hffff;
                // read resp stage
		        tb_read_resp_redirect_lane = {1'b0, {lane-1}[1], 1'b0};
                // update
                tb_update_valid = 1'b0;
                tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
                tb_update_gh = {2'h0, 9'h000, 3'h0};
		        tb_update_asid = 16'h0000;
                tb_update_taken = 1'b0;

                @(negedge CLK);

                // outputs:

                // arch state
                // read req stage
                // read resp stage
                expected_read_resp_taken = {lane-1}[2:0] >= {(lane == 0) ? index-1 : index}[2:0];
                // update

                check_outputs();
            end
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp index = 0x%03h lane = %1h", 9'h1ff, 3'h7);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
        tb_read_req_gh = {2'h0, 9'h000, 3'h0};
		tb_read_req_asid = 16'hffff;
        // read resp stage
		tb_read_resp_redirect_lane = 3'b010;
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_gh = {2'h0, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_taken = 1'b0;

        @(negedge CLK);

        // outputs:

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_taken = 1'b1;
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