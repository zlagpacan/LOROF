/*
    Filename: btb_tb.sv
    Author: zlagpacan
    Description: Testbench for btb module. 
    Spec: LOROF/spec/design/btb.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module btb_tb #(
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

    // read resp stage
	corep::PC38_t tb_read_resp_pc38;

	logic DUT_read_resp_hit, expected_read_resp_hit;
	corep::BTB_way_idx_t DUT_read_resp_hit_way, expected_read_resp_hit_way;
	corep::fetch_lane_t DUT_read_resp_hit_lane, expected_read_resp_hit_lane;
	logic DUT_read_resp_double_hit, expected_read_resp_double_hit;
	corep::BTB_info_t DUT_read_resp_btb_info, expected_read_resp_btb_info;

    // update
	logic tb_update_valid;
	corep::PC38_t tb_update_pc38;
	corep::BTB_info_t tb_update_btb_info;
	logic tb_update_hit;
	corep::BTB_way_idx_t tb_update_hit_way;

    // ----------------------------------------------------------------
    // DUT instantiation:

	btb #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // arch state
		.arch_asid(tb_arch_asid),

	    // read req stage
		.read_req_valid(tb_read_req_valid),
		.read_req_fetch_index(tb_read_req_fetch_index),

	    // read resp stage
		.read_resp_pc38(tb_read_resp_pc38),

		.read_resp_hit(DUT_read_resp_hit),
		.read_resp_hit_way(DUT_read_resp_hit_way),
		.read_resp_hit_lane(DUT_read_resp_hit_lane),
		.read_resp_double_hit(DUT_read_resp_double_hit),
		.read_resp_btb_info(DUT_read_resp_btb_info),

	    // update
		.update_valid(tb_update_valid),
		.update_pc38(tb_update_pc38),
		.update_btb_info(tb_update_btb_info),
		.update_hit(tb_update_hit),
		.update_hit_way(tb_update_hit_way)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_resp_hit !== DUT_read_resp_hit) begin
			$display("TB ERROR: expected_read_resp_hit (%h) != DUT_read_resp_hit (%h)",
				expected_read_resp_hit, DUT_read_resp_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_hit_way !== DUT_read_resp_hit_way) begin
			$display("TB ERROR: expected_read_resp_hit_way (%h) != DUT_read_resp_hit_way (%h)",
				expected_read_resp_hit_way, DUT_read_resp_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_hit_lane !== DUT_read_resp_hit_lane) begin
			$display("TB ERROR: expected_read_resp_hit_lane (%h) != DUT_read_resp_hit_lane (%h)",
				expected_read_resp_hit_lane, DUT_read_resp_hit_lane);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_double_hit !== DUT_read_resp_double_hit) begin
			$display("TB ERROR: expected_read_resp_double_hit (%h) != DUT_read_resp_double_hit (%h)",
				expected_read_resp_double_hit, DUT_read_resp_double_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_btb_info !== DUT_read_resp_btb_info) begin
			$display("TB ERROR: expected_read_resp_btb_info (%h) != DUT_read_resp_btb_info (%h)",
				expected_read_resp_btb_info, DUT_read_resp_btb_info);
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
	    // read resp stage
		tb_read_resp_pc38 = {26'h0000000, 9'h000, 3'h0};
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_btb_info = {3'b000, 1'b0, 15'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_hit = 1'b0;
		expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h0;
        expected_read_resp_double_hit = 1'b0;
		expected_read_resp_btb_info = {3'b000, 1'b0, 15'h000};
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
	    // read resp stage
		tb_read_resp_pc38 = {26'h0000000, 9'h000, 3'h0};
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_btb_info = {3'b000, 1'b0, 15'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_hit = 1'b0;
		expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h0;
        expected_read_resp_double_hit = 1'b0;
		expected_read_resp_btb_info = {3'b000, 1'b0, 15'h000};
	    // update

		check_outputs();

        // ------------------------------------------------------------
        // way 0,1 fill:
        test_case = "way 0,1 fill";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int index = 0; index < corep::BTB_SETS; index++) begin
            for (int way = 0; way < 2; way++) begin // hardcoded corep::BTB_ASSOC = 2

                @(posedge CLK); #(PERIOD/10);

                // inputs
                sub_test_case = $sformatf("index = 0x%03h", index);
                $display("\t- sub_test: %s", sub_test_case);

                // reset
                nRST = 1'b1;
                // arch state
                tb_arch_asid = 16'h0000;
                // read req stage
                tb_read_req_valid = 1'b0;
                tb_read_req_fetch_index = 9'h000;
                // read resp stage
                tb_read_resp_pc38 = {26'h0000000, 9'h000, 3'h0};
                // update
                tb_update_valid = 1'b1;
                tb_update_pc38 = {((way == 0) ? 26'hf0f0f0f : 26'he1e1e1e), index[8:0], index[2:0]};
                tb_update_btb_info = {index[2:0], (way == 0) ? 1'b0 : 1'b1, (way == 0) ? 15'h0f0f : 15'h1e1e};
                tb_update_hit = 1'b0;
                tb_update_hit_way = 1'b0;

                @(negedge CLK);

                // arch state
                // read req stage
                // read resp stage
                expected_read_resp_hit = 1'b0;
                expected_read_resp_hit_way = 1'b0;
                expected_read_resp_hit_lane = 3'h0;
                expected_read_resp_double_hit = 1'b0;
                expected_read_resp_btb_info = {3'b000, 1'b0, 15'h000};
                // update

                check_outputs();
            end
        end

        // ------------------------------------------------------------
        // way 0 read:
        test_case = "way 0 read";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%03h", 9'h000);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h000;
        // read resp stage
		tb_read_resp_pc38 = {26'h0000000, 9'h000, 3'h0};
        // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_btb_info = {3'b000, 1'b0, 15'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
		expected_read_resp_hit = 1'b0;
		expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h0;
        expected_read_resp_double_hit = 1'b0;
		expected_read_resp_btb_info = {3'b000, 1'b0, 15'h000};
        // update

        check_outputs();

        for (int index = 1; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%03h, resp index = 0x%03h", index, index-1);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h0000;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_index = index[8:0];
            // read resp stage
            tb_read_resp_pc38 = {26'hf0f0f0f, {index-1}[8:0], index[3] ? 3'h3 : 3'h0}; // purposelly miss on index[2:0] = 0,1,2 for index[3] == 1
            // update
            tb_update_valid = 1'b0;
		    tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		    tb_update_btb_info = {3'b000, 1'b0, 15'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // arch state
            // read req stage
            // read resp stage
            expected_read_resp_hit = {index-1}[3] ? {index-1}[2:0] >= 3 : {index-1}[2:0] > 0;
            expected_read_resp_hit_way = 1'b0;
            expected_read_resp_hit_lane = {index-1}[2:0];
            expected_read_resp_double_hit = 1'b0;
            expected_read_resp_btb_info = {{index-1}[2:0], 1'b0, 15'h0f0f};
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp index = 0x%03h", 9'h1ff);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
		tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'hf0f0f0f, 9'h1ff, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b111, 1'b0, 15'h0f0f};
        // update

        check_outputs();

        // ------------------------------------------------------------
        // way 1 read:
        test_case = "way 1 read";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%03h", 9'h000);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
		tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'hf0f0f0f, 9'h1ff, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b111, 1'b0, 15'h0f0f};
        // update

        check_outputs();

        for (int index = 1; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%03h, resp index = 0x%03h", index, index-1);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h0000;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_index = index[8:0];
            // read resp stage
            tb_read_resp_pc38 = {26'he1e1e1e, {index-1}[8:0], index[4] ? 3'h5 : 3'h0}; // purposelly miss on index[2:0] = 0,1,2,3,4 for index[3] == 1
            // update
            tb_update_valid = 1'b0;
		    tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		    tb_update_btb_info = {3'b000, 1'b0, 15'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // arch state
            // read req stage
            // read resp stage
            expected_read_resp_hit = {index-1}[4] ? {index-1}[2:0] >= 5 : {index-1}[2:0] > 0;
            expected_read_resp_hit_way = expected_read_resp_hit ? 1'b1 : 1'b0;
            expected_read_resp_hit_lane = {index-1}[2:0];
            expected_read_resp_double_hit = 1'b0;
            expected_read_resp_btb_info = expected_read_resp_hit ? {{index-1}[2:0], 1'b1, 15'h1e1e} : {{index-1}[2:0], 1'b0, 15'h0f0f};
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp index = 0x%03h", 9'h1ff);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'he1e1e1e, 9'h1ff, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b111, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        // ------------------------------------------------------------
        // touch way 0 for multiples of 5:
        test_case = "touch way 0 for multiples of 5";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int index = 0; index < corep::BTB_SETS; index += 5) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("index = 0x%03h", index[2:0]);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h0000;
            // read req stage
            tb_read_req_valid = 1'b0;
            tb_read_req_fetch_index = 9'h000;
            // read resp stage
            tb_read_resp_pc38 = {26'he1e1e1e, 9'h1ff, 3'h0};
            // update
            tb_update_valid = 1'b1;
            tb_update_pc38 = {26'hf0f0f0f, index[8:0], index[2:0]};
            tb_update_btb_info = {index[2:0], 1'b0, 15'h0f0f};
            tb_update_hit = 1'b1;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // arch state
            // read req stage
            // read resp stage
            expected_read_resp_hit = 1'b1;
            expected_read_resp_hit_way = 1'b1;
            expected_read_resp_hit_lane = 3'h7;
            expected_read_resp_double_hit = 1'b0;
            expected_read_resp_btb_info = {3'b111, 1'b1, 15'h1e1e};
            // update

            check_outputs();
        end

        // ------------------------------------------------------------
        // new way fill:
        test_case = "new way fill";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int index = 0; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("index = 0x%03h", index);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h0000;
            // read req stage
            tb_read_req_valid = 1'b0;
            tb_read_req_fetch_index = 9'h000;
            // read resp stage
            tb_read_resp_pc38 = {26'he1e1e1e, 9'h1ff, 3'h0};
            // update
            tb_update_valid = 1'b1;
            tb_update_pc38 = {26'h2222222, index[8:0], index[2:0]};
            tb_update_btb_info = {~index[2:0], 1'b0, 15'h2222};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // arch state
            // read req stage
            // read resp stage
            expected_read_resp_hit = 1'b1;
            expected_read_resp_hit_way = 1'b1;
            expected_read_resp_hit_lane = 3'h7;
            expected_read_resp_double_hit = 1'b0;
            expected_read_resp_btb_info = {3'b111, 1'b1, 15'h1e1e};
            // update

            check_outputs();
        end

        // ------------------------------------------------------------
        // new way read:
        test_case = "new way read";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%03h", 9'h000);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'he1e1e1e, 9'h1ff, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b111, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        for (int index = 1; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%03h, resp index = 0x%03h", index, index-1);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h0000;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_index = index[8:0];
            // read resp stage
            tb_read_resp_pc38 = {26'h2222222, {index-1}[8:0], 3'h0};
            // update
            tb_update_valid = 1'b0;
		    tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		    tb_update_btb_info = {3'b000, 1'b0, 15'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // arch state
            // read req stage
            // read resp stage
            expected_read_resp_hit = {index-1}[2:0] != 7;
            expected_read_resp_hit_way = expected_read_resp_hit & ({index-1} % 5 == 0) ? 1'b1 : 1'b0;
            expected_read_resp_hit_lane = {index-1}[2:0];
            expected_read_resp_double_hit = 1'b0;
            expected_read_resp_btb_info = expected_read_resp_hit | ({index-1} % 5 != 0) ? {~{index-1}[2:0], 1'b0, 15'h2222} : {{index-1}[2:0], 1'b0, 15'h0f0f};
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp index = 0x%03h", 9'h1ff);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h1ff, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h0000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'h0, 1'b0, 15'h2222};
        // update

        check_outputs();

        // ------------------------------------------------------------
        // double hit cases:
        test_case = "double hit cases";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("update index 0x006 with other 2222222 in lane 2 for way 1 -> way0: 001 @ lane 6, way1: 010 @ lane 2");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h1ff, 3'h0};
        // update
        tb_update_valid = 1'b1;
        tb_update_pc38 = {26'h2222222, 9'h006, 3'h2};
        tb_update_btb_info = {3'b010, 1'b0, 15'h6666};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'h0, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("update index 0x009 with other 2222222 in lane 4 for way 1 -> way0: 110 @ lane 1, way1: 100 @ lane 4");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h1ff, 3'h0};
        // update
        tb_update_valid = 1'b1;
        tb_update_pc38 = {26'h2222222, 9'h009, 3'h4};
        tb_update_btb_info = {3'b100, 1'b0, 15'h9999};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'h0, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 0");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h000, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_lane = 3'h7;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'h0, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 1, read resp index 0x006 lane 0 (choose way 1 @ lane 2)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_lane = 3'h2;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_double_hit = 1'b1;
        expected_read_resp_btb_info = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 2, read resp index 0x006 lane 1 (choose way 1 @ lane 2)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h1};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_lane = 3'h2;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_double_hit = 1'b1;
        expected_read_resp_btb_info = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 3, read resp index 0x006 lane 2 (choose way 1 @ lane 2)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h2};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_lane = 3'h2;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_double_hit = 1'b1;
        expected_read_resp_btb_info = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 4, read resp index 0x006 lane 3 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h3};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_lane = 3'h6;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b001, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 5, read resp index 0x006 lane 4 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h4};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_lane = 3'h6;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b001, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 6, read resp index 0x006 lane 5 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h5};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_lane = 3'h6;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b001, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 7, read resp index 0x006 lane 6 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h006;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h6};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h6;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b001, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 0, read resp index 0x006 lane 7 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h006, 3'h7};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h6;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b001, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 1, read resp index 0x009 lane 0 (choose way 0 @ lane 1)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_lane = 3'h1;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_double_hit = 1'b1;
        expected_read_resp_btb_info = {3'b110, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 2, read resp index 0x009 lane 1 (choose way 0 @ lane 1)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h1};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h1;
        expected_read_resp_double_hit = 1'b1;
        expected_read_resp_btb_info = {3'b110, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 3, read resp index 0x009 lane 2 (choose way 1 @ lane 4)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h2};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_hit_lane = 3'h4;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 4, read resp index 0x009 lane 3 (choose way 1 @ lane 4)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h3};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_hit_lane = 3'h4;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 5, read resp index 0x009 lane 4 (choose way 1 @ lane 4)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h4};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b1;
        expected_read_resp_hit_way = 1'b1;
        expected_read_resp_hit_lane = 3'h4;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 6, read resp index 0x009 lane 5 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h5};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h1;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b110, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 7, read resp index 0x009 lane 6 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 9'h009;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h6};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h1;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b110, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read resp index 0x009 lane 7 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_index = 9'h000;
        // read resp stage
        tb_read_resp_pc38 = {26'h2222222, 9'h009, 3'h7};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_hit = 1'b0;
        expected_read_resp_hit_way = 1'b0;
        expected_read_resp_hit_lane = 3'h1;
        expected_read_resp_double_hit = 1'b0;
        expected_read_resp_btb_info = {3'b110, 1'b0, 15'h2222};
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