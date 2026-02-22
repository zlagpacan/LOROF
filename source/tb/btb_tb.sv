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


    // read req stage
	logic tb_read_req_valid;
	corep::fetch_idx_t tb_read_req_fetch_idx;
	corep::asid_t tb_read_req_asid;

    // read resp0 stage
	logic tb_read_resp0_valid;
	corep::pc38_t tb_read_resp0_pc38;

	corep::fetch_lane_t DUT_read_resp0_hit_lane_way0, expected_read_resp0_hit_lane_way0;
	corep::fetch_lane_t DUT_read_resp0_hit_lane_way1, expected_read_resp0_hit_lane_way1;

    // read resp1 stage
	logic DUT_read_resp1_hit, expected_read_resp1_hit;
	logic DUT_read_resp1_double_hit, expected_read_resp1_double_hit;
	corep::btb_way_t DUT_read_resp1_hit_way, expected_read_resp1_hit_way;

	corep::fetch_lane_t DUT_read_resp1_hit_lane_way0, expected_read_resp1_hit_lane_way0;
	corep::fetch_lane_t DUT_read_resp1_hit_lane_way1, expected_read_resp1_hit_lane_way1;
	corep::btb_info_t DUT_read_resp1_btb_info_way0, expected_read_resp1_btb_info_way0;
	corep::btb_info_t DUT_read_resp1_btb_info_way1, expected_read_resp1_btb_info_way1;

    // update
	logic tb_update_valid;
	corep::pc38_t tb_update_pc38;
	corep::asid_t tb_update_asid;
	corep::btb_info_t tb_update_btb_info;
	logic tb_update_hit;
	corep::btb_way_t tb_update_hit_way;

    // ----------------------------------------------------------------
    // DUT instantiation:

	btb #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // read req stage
		.read_req_valid(tb_read_req_valid),
		.read_req_fetch_idx(tb_read_req_fetch_idx),
		.read_req_asid(tb_read_req_asid),

	    // read resp0 stage
		.read_resp0_valid(tb_read_resp0_valid),
		.read_resp0_pc38(tb_read_resp0_pc38),

		.read_resp0_hit_lane_way0(DUT_read_resp0_hit_lane_way0),
		.read_resp0_hit_lane_way1(DUT_read_resp0_hit_lane_way1),

	    // read resp1 stage
		.read_resp1_hit(DUT_read_resp1_hit),
		.read_resp1_double_hit(DUT_read_resp1_double_hit),
		.read_resp1_hit_way(DUT_read_resp1_hit_way),

		.read_resp1_hit_lane_way0(DUT_read_resp1_hit_lane_way0),
		.read_resp1_hit_lane_way1(DUT_read_resp1_hit_lane_way1),
		.read_resp1_btb_info_way0(DUT_read_resp1_btb_info_way0),
		.read_resp1_btb_info_way1(DUT_read_resp1_btb_info_way1),

	    // update
		.update_valid(tb_update_valid),
		.update_pc38(tb_update_pc38),
		.update_asid(tb_update_asid),
		.update_btb_info(tb_update_btb_info),
		.update_hit(tb_update_hit),
		.update_hit_way(tb_update_hit_way)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_resp0_hit_lane_way0 !== DUT_read_resp0_hit_lane_way0) begin
			$display("TB ERROR: expected_read_resp0_hit_lane_way0 (%h) != DUT_read_resp0_hit_lane_way0 (%h)",
				expected_read_resp0_hit_lane_way0, DUT_read_resp0_hit_lane_way0);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp0_hit_lane_way1 !== DUT_read_resp0_hit_lane_way1) begin
			$display("TB ERROR: expected_read_resp0_hit_lane_way1 (%h) != DUT_read_resp0_hit_lane_way1 (%h)",
				expected_read_resp0_hit_lane_way1, DUT_read_resp0_hit_lane_way1);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp1_hit !== DUT_read_resp1_hit) begin
			$display("TB ERROR: expected_read_resp1_hit (%h) != DUT_read_resp1_hit (%h)",
				expected_read_resp1_hit, DUT_read_resp1_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp1_double_hit !== DUT_read_resp1_double_hit) begin
			$display("TB ERROR: expected_read_resp1_double_hit (%h) != DUT_read_resp1_double_hit (%h)",
				expected_read_resp1_double_hit, DUT_read_resp1_double_hit);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp1_hit_way !== DUT_read_resp1_hit_way) begin
			$display("TB ERROR: expected_read_resp1_hit_way (%h) != DUT_read_resp1_hit_way (%h)",
				expected_read_resp1_hit_way, DUT_read_resp1_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp1_hit_lane_way0 !== DUT_read_resp1_hit_lane_way0) begin
			$display("TB ERROR: expected_read_resp1_hit_lane_way0 (%h) != DUT_read_resp1_hit_lane_way0 (%h)",
				expected_read_resp1_hit_lane_way0, DUT_read_resp1_hit_lane_way0);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp1_hit_lane_way1 !== DUT_read_resp1_hit_lane_way1) begin
			$display("TB ERROR: expected_read_resp1_hit_lane_way1 (%h) != DUT_read_resp1_hit_lane_way1 (%h)",
				expected_read_resp1_hit_lane_way1, DUT_read_resp1_hit_lane_way1);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp1_btb_info_way0 !== DUT_read_resp1_btb_info_way0) begin
			$display("TB ERROR: expected_read_resp1_btb_info_way0 (%h) != DUT_read_resp1_btb_info_way0 (%h)",
				expected_read_resp1_btb_info_way0, DUT_read_resp1_btb_info_way0);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp1_btb_info_way1 !== DUT_read_resp1_btb_info_way1) begin
			$display("TB ERROR: expected_read_resp1_btb_info_way1 (%h) != DUT_read_resp1_btb_info_way1 (%h)",
				expected_read_resp1_btb_info_way1, DUT_read_resp1_btb_info_way1);
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
		tb_read_req_asid = 16'h0000;
	    // read resp0 stage
		tb_read_resp0_valid = 1'b0;
		tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
	    // read resp1 stage
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
		tb_update_btb_info = {3'b000, 1'b0, 15'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // read req stage
	    // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h0;
		expected_read_resp0_hit_lane_way1 = 3'h0;
	    // read resp1 stage
		expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
		expected_read_resp1_hit_way = 1'b0;
		expected_read_resp1_hit_lane_way0 = 3'h0;
		expected_read_resp1_hit_lane_way1 = 3'h0;
		expected_read_resp1_btb_info_way0 = {3'b000, 1'b0, 15'h000};
		expected_read_resp1_btb_info_way1 = {3'b000, 1'b0, 15'h000};
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
		tb_read_req_asid = 16'h0000;
	    // read resp0 stage
		tb_read_resp0_valid = 1'b0;
		tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
	    // read resp1 stage
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
		tb_update_btb_info = {3'b000, 1'b0, 15'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // read req stage
	    // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h0;
		expected_read_resp0_hit_lane_way1 = 3'h0;
	    // read resp1 stage
		expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
		expected_read_resp1_hit_way = 1'b0;
		expected_read_resp1_hit_lane_way0 = 3'h0;
		expected_read_resp1_hit_lane_way1 = 3'h0;
		expected_read_resp1_btb_info_way0 = {3'b000, 1'b0, 15'h000};
		expected_read_resp1_btb_info_way1 = {3'b000, 1'b0, 15'h000};
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
                // read req stage
                tb_read_req_valid = 1'b0;
                tb_read_req_fetch_idx = 9'h000;
                tb_read_req_asid = 16'h0000;
                // read resp0 stage
                tb_read_resp0_valid = 1'b0;
                tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
	            // read resp1 stage
                // update
                tb_update_valid = 1'b1;
                tb_update_pc38 = {((way == 0) ? 26'hf0f0f0f : 26'he1e1e1e), index[8:0], index[2:0]};
		        tb_update_asid = 16'h0000;
                tb_update_btb_info = {index[2:0], (way == 0) ? 1'b0 : 1'b1, (way == 0) ? 15'h0f0f : 15'h1e1e};
                tb_update_hit = 1'b0;
                tb_update_hit_way = 1'b0;

                @(negedge CLK);

                // read req stage
	            // read resp0 stage
                expected_read_resp0_hit_lane_way0 = 3'h0;
                expected_read_resp0_hit_lane_way1 = 3'h0;
                // read resp1 stage
                expected_read_resp1_hit = 1'b0;
                expected_read_resp1_double_hit = 1'b0;
                expected_read_resp1_hit_way = 1'b0;
                expected_read_resp1_hit_lane_way0 = 3'h0;
                expected_read_resp1_hit_lane_way1 = 3'h0;
                expected_read_resp1_btb_info_way0 = {3'b000, 1'b0, 15'h000};
                expected_read_resp1_btb_info_way1 = {3'b000, 1'b0, 15'h000};
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
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
		tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
		tb_update_btb_info = {3'b000, 1'b0, 15'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h0;
		expected_read_resp0_hit_lane_way1 = 3'h0;
        // read resp1 stage
		expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
		expected_read_resp1_hit_way = 1'b0;
		expected_read_resp1_hit_lane_way0 = 3'h0;
		expected_read_resp1_hit_lane_way1 = 3'h0;
		expected_read_resp1_btb_info_way0 = {3'b000, 1'b0, 15'h000};
		expected_read_resp1_btb_info_way1 = {3'b000, 1'b0, 15'h000};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%03h, resp0 index = 0x%03h", 9'h001, 9'h000);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h001;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
		tb_read_resp0_pc38 = {26'hf0f0f0f, 9'h000, 3'h0};
        // read resp1 stage
        // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
		tb_update_btb_info = {3'b000, 1'b0, 15'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h0;
		expected_read_resp0_hit_lane_way1 = 3'h0;
        // read resp1 stage
		expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
		expected_read_resp1_hit_way = 1'b0;
		expected_read_resp1_hit_lane_way0 = 3'h0;
		expected_read_resp1_hit_lane_way1 = 3'h0;
		expected_read_resp1_btb_info_way0 = {3'b000, 1'b0, 15'h000};
		expected_read_resp1_btb_info_way1 = {3'b000, 1'b0, 15'h000};
        // update

        check_outputs();

        for (int index = 2; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%03h, resp0 index = 0x%03h, resp1 index = 0x%03h", index, index-1, index-2);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_idx = index[8:0];
		    tb_read_req_asid = 16'h0000;
            // read resp0 stage
            tb_read_resp0_valid = 1'b1;
            tb_read_resp0_pc38 = {26'hf0f0f0f, {index-1}[8:0], index[3] ? 3'h3 : 3'h0}; // purposelly miss on index[2:0] = 0,1,2 for index[3] == 1
            // read resp1 stage
            // update
            tb_update_valid = 1'b0;
		    tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		    tb_update_asid = 16'h0000;
		    tb_update_btb_info = {3'b000, 1'b0, 15'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // read req stage
            // read resp0 stage
            expected_read_resp0_hit_lane_way0 = {index-1}[2:0];
            expected_read_resp0_hit_lane_way1 = {index-1}[2:0];
            // read resp1 stage
            expected_read_resp1_hit = {index-2}[3] ? {index-2}[2:0] >= 3 : {index-2}[2:0] > 0;
            expected_read_resp1_double_hit = 1'b0;
            expected_read_resp1_hit_way = 1'b0;
            expected_read_resp1_hit_lane_way0 = {index-2}[2:0];
            expected_read_resp1_hit_lane_way1 = {index-2}[2:0];
            expected_read_resp1_btb_info_way0 = {{index-2}[2:0], 1'b0, 15'h0f0f};
            expected_read_resp1_btb_info_way1 = {{index-2}[2:0], 1'b1, 15'h1e1e};
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp0 index = 0x%03h, resp1 index = 0x%03h", 9'h1ff, 9'h1fe);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
		tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'hf0f0f0f, 9'h1ff, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h6;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b110, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp1 index = 0x%03h", 9'h1ff);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
		tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
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
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%03h, resp0 index = 0x%03h", 9'h001, 9'h000);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h001;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'he1e1e1e, 9'h000, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h0;
		expected_read_resp0_hit_lane_way1 = 3'h0;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        for (int index = 2; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%03h, resp0 index = 0x%03h, resp1 index = 0x%03h", index, index-1, index-2);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_idx = index[8:0];
		    tb_read_req_asid = 16'h0000;
            // read resp0 stage
            tb_read_resp0_valid = 1'b1;
            tb_read_resp0_pc38 = {26'he1e1e1e, {index-1}[8:0], index[4] ? 3'h5 : 3'h0}; // purposelly miss on index[2:0] = 0,1,2,3,4 for index[3] == 1
            // read resp1 stage
            // update
            tb_update_valid = 1'b0;
		    tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		    tb_update_asid = 16'h0000;
		    tb_update_btb_info = {3'b000, 1'b0, 15'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // read req stage
            // read resp0 stage
            expected_read_resp0_hit_lane_way0 = {index-1}[2:0];
            expected_read_resp0_hit_lane_way1 = {index-1}[2:0];
            // read resp1 stage
            expected_read_resp1_hit = {index-2}[4] ? {index-2}[2:0] >= 5 : {index-2}[2:0] > 0;
            expected_read_resp1_double_hit = 1'b0;
            expected_read_resp1_hit_way = expected_read_resp1_hit ? 1'b1 : 1'b0;
            expected_read_resp1_hit_lane_way0 = {index-2}[2:0];
            expected_read_resp1_hit_lane_way1 = {index-2}[2:0];
            expected_read_resp1_btb_info_way0 = {{index-2}[2:0], 1'b0, 15'h0f0f};
            expected_read_resp1_btb_info_way1 = {{index-2}[2:0], 1'b1, 15'h1e1e};
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp0 index = 0x%03h, resp1 index = 0x%03h", 9'h1ff, 9'h1fe);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'he1e1e1e, 9'h1ff, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h6;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b110, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp1 index = 0x%03h", 9'h1ff);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
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
            // read req stage
            tb_read_req_valid = 1'b0;
            tb_read_req_fetch_idx = 9'h000;
		    tb_read_req_asid = 16'h0000;
            // read resp0 stage
            tb_read_resp0_valid = 1'b0;
            tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
            // read resp1 stage
            // update
            tb_update_valid = 1'b1;
            tb_update_pc38 = {26'hf0f0f0f, index[8:0], index[2:0]};
		    tb_update_asid = 16'h0000;
            tb_update_btb_info = {index[2:0], 1'b0, 15'h0f0f};
            tb_update_hit = 1'b1;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // read req stage
            // read resp0 stage
            expected_read_resp0_hit_lane_way0 = 3'h7;
            expected_read_resp0_hit_lane_way1 = 3'h7;
            // read resp1 stage
            expected_read_resp1_hit = 1'b1;
            expected_read_resp1_double_hit = 1'b0;
            expected_read_resp1_hit_way = 1'b1;
            expected_read_resp1_hit_lane_way0 = 3'h7;
            expected_read_resp1_hit_lane_way1 = 3'h7;
            expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
            expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
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
            // read req stage
            tb_read_req_valid = 1'b0;
            tb_read_req_fetch_idx = 9'h000;
		    tb_read_req_asid = 16'h0000;
            // read resp0 stage
            tb_read_resp0_valid = 1'b0;
            tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
            // read resp1 stage
            // update
            tb_update_valid = 1'b1;
            tb_update_pc38 = {26'h2222222, index[8:0], index[2:0]};
		    tb_update_asid = 16'h0000;
            tb_update_btb_info = {~index[2:0], 1'b0, 15'h2222};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // read req stage
            // read resp0 stage
            expected_read_resp0_hit_lane_way0 = 3'h7;
            expected_read_resp0_hit_lane_way1 = 3'h7;
            // read resp1 stage
            expected_read_resp1_hit = 1'b1;
            expected_read_resp1_double_hit = 1'b0;
            expected_read_resp1_hit_way = 1'b1;
            expected_read_resp1_hit_lane_way0 = 3'h7;
            expected_read_resp1_hit_lane_way1 = 3'h7;
            expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
            expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
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
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%03h, resp0 index = 0x%03h", 9'h001, 9'h000);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h001;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h000, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h0;
		expected_read_resp0_hit_lane_way1 = 3'h0;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'b111, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'b111, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        for (int index = 2; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%03h, resp0 index = 0x%03h, resp1 index = 0x%03h", index, index-1, index-2);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_idx = index[8:0];
		    tb_read_req_asid = 16'h0000;
            // read resp0 stage
            tb_read_resp0_valid = 1'b1;
            tb_read_resp0_pc38 = {26'h2222222, {index-1}[8:0], 3'h0};
            // read resp1 stage
            // update
            tb_update_valid = 1'b0;
		    tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		    tb_update_asid = 16'h0000;
		    tb_update_btb_info = {3'b000, 1'b0, 15'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // read req stage
            // read resp0 stage
            expected_read_resp0_hit_lane_way0 = {index-1}[2:0];
            expected_read_resp0_hit_lane_way1 = {index-1}[2:0];
            // read resp1 stage
            expected_read_resp1_hit = {index-2}[2:0] != 7;
            expected_read_resp1_double_hit = 1'b0;
            expected_read_resp1_hit_way = expected_read_resp1_hit & ({index-2} % 5 == 0) ? 1'b1 : 1'b0;
            expected_read_resp1_hit_lane_way0 = {index-2}[2:0];
            expected_read_resp1_hit_lane_way1 = {index-2}[2:0];
            expected_read_resp1_btb_info_way0 = ({index-2} % 5 != 0) ? {~{index-2}[2:0], 1'b0, 15'h2222} : {{index-2}[2:0], 1'b0, 15'h0f0f};
            expected_read_resp1_btb_info_way1 = ({index-2} % 5 != 0) ? {{index-2}[2:0], 1'b1, 15'h1e1e} : {~{index-2}[2:0], 1'b0, 15'h2222};
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp0 index = 0x%03h, resp1 index = 0x%03h", 9'h1ff, 9'h1fe);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h1ff, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h0000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h6;
        expected_read_resp1_btb_info_way0 = {3'h6, 1'b0, 15'h0f0f};
        expected_read_resp1_btb_info_way1 = {3'h1, 1'b0, 15'h2222};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp index = 0x%03h", 9'h1ff);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h0000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'h0, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'h7, 1'b1, 15'h1e1e};
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
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b1;
        tb_update_pc38 = {26'h222dddd, 9'hff9, 3'h2};
		tb_update_asid = 16'hffff;
        tb_update_btb_info = {3'b010, 1'b0, 15'h6666};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'h0, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'h7, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("update index 0x009 with other 2222222 in lane 4 for way 1 -> way0: 110 @ lane 1, way1: 100 @ lane 4");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b1;
        tb_update_pc38 = {26'h2222222, 9'h009, 3'h4};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b100, 1'b0, 15'h9999};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'h0, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'h7, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 0");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h006;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h7;
		expected_read_resp0_hit_lane_way1 = 3'h7;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'h0, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'h7, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 1, read resp0 index 0x006 lane 0 (choose way 1 @ lane 2)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h006;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h006, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h7;
        expected_read_resp1_hit_lane_way1 = 3'h7;
        expected_read_resp1_btb_info_way0 = {3'h0, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'h7, 1'b1, 15'h1e1e};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 2, read resp0 index 0x006 lane 1, read resp1 index 0x006 lane 0 (choose way 1 @ lane 2)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'hff6;
		tb_read_req_asid = 16'h0ff0;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h006, 3'h1};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b1;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 3, read req index 0x006 lane 2, read resp index 0x006 lane 1 (choose way 1 @ lane 2)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h006;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222dd2, 9'h006, 3'h2};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b1;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 4, read resp0 index 0x006 lane 3, read resp1 index 0x006 lane 2 (choose way 1 @ lane 2)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h006;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h006, 3'h3};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b1;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 5, read resp0 index 0x006 lane 4, read resp1 index 0x006 lane 3 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h006;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h006, 3'h4};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 6, read resp0 index 0x006 lane 5, read resp1 index 0x006 lane 4 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h006;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h006, 3'h5};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x006 lane 7, read resp0 index 0x006 lane 6, read resp1 index 0x006 lane 5 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h006;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h006, 3'h6};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 0, read resp0 index 0x006 lane 7, read resp1 index 0x006 lane 6 (choose way 0 @ lane 6)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h006, 3'h7};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h6;
		expected_read_resp0_hit_lane_way1 = 3'h2;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 1, read resp0 index 0x009 lane 0, read resp1 index 0x006 lane 7 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h6;
        expected_read_resp1_hit_lane_way1 = 3'h2;
        expected_read_resp1_btb_info_way0 = {3'b001, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b010, 1'b0, 15'h6666};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 2, read resp0 index 0x009 lane 1, read resp1 index 0x009 lane 0 (choose way 0 @ lane 1)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h1};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b1;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 3, read resp0 index 0x009 lane 2, read resp1 index 0x009 lane 1 (choose way 0 @ lane 1)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h2};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b1;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 4, read resp0 index 0x009 lane 3, read resp1 index 0x009 lane 2 (choose way 1 @ lane 4)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h3};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 5, read resp0 index 0x009 lane 4, read resp1 index 0x009 lane 3 (choose way 1 @ lane 4)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h4};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 6, read resp0 index 0x009 lane 5, read resp1 index 0x009 lane 4 (choose way 1 @ lane 4)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h5};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b1;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b1;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read req index 0x009 lane 7, read resp0 index 0x009 lane 6, read resp1 index 0x009 lane 5 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_idx = 9'h009;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h6};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read resp0 index 0x009 lane 7, read resp1 index 0x009 lane 6 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b1;
        tb_read_resp0_pc38 = {26'h2222222, 9'h009, 3'h7};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
        // update

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read resp1 index 0x009 lane 7 (choose none)");
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_idx = 9'h000;
		tb_read_req_asid = 16'h0000;
        // read resp0 stage
        tb_read_resp0_valid = 1'b0;
        tb_read_resp0_pc38 = {26'h0000000, 9'h000, 3'h0};
        // read resp1 stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {26'h0000000, 9'h000, 3'h0};
		tb_update_asid = 16'h0000;
        tb_update_btb_info = {3'b000, 1'b0, 15'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // read req stage
        // read resp0 stage
		expected_read_resp0_hit_lane_way0 = 3'h1;
		expected_read_resp0_hit_lane_way1 = 3'h4;
        // read resp1 stage
        expected_read_resp1_hit = 1'b0;
        expected_read_resp1_double_hit = 1'b0;
        expected_read_resp1_hit_way = 1'b0;
        expected_read_resp1_hit_lane_way0 = 3'h1;
        expected_read_resp1_hit_lane_way1 = 3'h4;
        expected_read_resp1_btb_info_way0 = {3'b110, 1'b0, 15'h2222};
        expected_read_resp1_btb_info_way1 = {3'b100, 1'b0, 15'h9999};
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