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

	corep::BTB_info_t [corep::FETCH_LANES-1:0] DUT_resp_resp_btb_info_by_lane, expected_resp_resp_btb_info_by_lane;
	logic [corep::FETCH_LANES-1:0] DUT_read_resp_hit_by_lane, expected_read_resp_hit_by_lane;
	corep::BTB_way_idx_t [corep::FETCH_LANES-1:0] DUT_read_resp_hit_way_by_lane, expected_read_resp_hit_way_by_lane;

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

		.resp_resp_btb_info_by_lane(DUT_resp_resp_btb_info_by_lane),
		.read_resp_hit_by_lane(DUT_read_resp_hit_by_lane),
		.read_resp_hit_way_by_lane(DUT_read_resp_hit_way_by_lane),

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
		if (expected_resp_resp_btb_info_by_lane !== DUT_resp_resp_btb_info_by_lane) begin
			$display("TB ERROR: expected_resp_resp_btb_info_by_lane (%h) != DUT_resp_resp_btb_info_by_lane (%h)",
				expected_resp_resp_btb_info_by_lane, DUT_resp_resp_btb_info_by_lane);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_hit_by_lane !== DUT_read_resp_hit_by_lane) begin
			$display("TB ERROR: expected_read_resp_hit_by_lane (%h) != DUT_read_resp_hit_by_lane (%h)",
				expected_read_resp_hit_by_lane, DUT_read_resp_hit_by_lane);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_hit_way_by_lane !== DUT_read_resp_hit_way_by_lane) begin
			$display("TB ERROR: expected_read_resp_hit_way_by_lane (%h) != DUT_read_resp_hit_way_by_lane (%h)",
				expected_read_resp_hit_way_by_lane, DUT_read_resp_hit_way_by_lane);
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
		tb_read_req_fetch_index = 6'h00;
	    // read resp stage
		tb_read_resp_pc38 = {29'h00000000, 6'h00, 3'h0};
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
		tb_update_btb_info = {3'b000, 1'b0, 12'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_resp_resp_btb_info_by_lane = {
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000}
        };
		expected_read_resp_hit_by_lane = 8'b00000000;
		expected_read_resp_hit_way_by_lane = 8'b00000000;
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
		tb_read_req_fetch_index = 6'h00;
	    // read resp stage
		tb_read_resp_pc38 = {29'h00000000, 6'h00, 3'h0};
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
		tb_update_btb_info = {3'b000, 1'b0, 12'h000};
		tb_update_hit = 1'b0;
		tb_update_hit_way = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_resp_resp_btb_info_by_lane = {
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000}
        };
		expected_read_resp_hit_by_lane = 8'b00000000;
		expected_read_resp_hit_way_by_lane = 8'b00000000;
	    // update

		check_outputs();

        // ------------------------------------------------------------
        // way 0 fill:
        test_case = "way 0 fill";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int index = 0; index < corep::BTB_SETS; index++) begin
            for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin

                @(posedge CLK); #(PERIOD/10);

                // inputs
                sub_test_case = $sformatf("index = 0x%2h, lane = %1h", index, lane);
                $display("\t- sub_test: %s", sub_test_case);

                // reset
                nRST = 1'b1;
                // arch state
                tb_arch_asid = 16'h0000;
                // read req stage
                tb_read_req_valid = 1'b0;
                tb_read_req_fetch_index = 6'h00;
                // read resp stage
                tb_read_resp_pc38 = {29'h00000000, 6'h00, 3'h0};
                // update
                tb_update_valid = 1'b1;
                tb_update_pc38 = {(~lane[0] ? 29'h0f0f0f0f : 29'h1e1e1e1e), index[5:0], lane[2:0]};
                tb_update_btb_info = {lane[2:0], lane[0], (~lane[0] ? 12'hf0f : 12'he1e)};
                tb_update_hit = 1'b0;
                tb_update_hit_way = 1'b0;

                @(negedge CLK);

                // arch state
                // read req stage
                // read resp stage
                expected_resp_resp_btb_info_by_lane = {
                    {3'b000, 1'b0, 12'h000},
                    {3'b000, 1'b0, 12'h000},
                    {3'b000, 1'b0, 12'h000},
                    {3'b000, 1'b0, 12'h000},
                    {3'b000, 1'b0, 12'h000},
                    {3'b000, 1'b0, 12'h000},
                    {3'b000, 1'b0, 12'h000},
                    {3'b000, 1'b0, 12'h000}
                };
                expected_read_resp_hit_by_lane = 8'b00000000;
                expected_read_resp_hit_way_by_lane = 8'b00000000;
                // update

                check_outputs();
            end
        end

        // ------------------------------------------------------------
        // way 0 read for 0f:
        test_case = "way 0 read for 0f";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%2h", 6'h00);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 6'h00;
        // read resp stage
        tb_read_resp_pc38 = {29'h00000000, 6'h00, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 12'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_resp_resp_btb_info_by_lane = {
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000},
            {3'b000, 1'b0, 12'h000}
        };
        expected_read_resp_hit_by_lane = 8'b00000000;
        expected_read_resp_hit_way_by_lane = 8'b00000000;
        // update

        check_outputs();

        for (int index = 1; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%2h, resp index = 0x%2h", index, index-1);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h0000;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_index = index;
            // read resp stage
            tb_read_resp_pc38 = {29'h0f0f0f0f, {index-1}[5:0], 3'h0};
            // update
            tb_update_valid = 1'b0;
            tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
            tb_update_btb_info = {3'b000, 1'b0, 12'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // arch state
            // read req stage
            // read resp stage
            expected_resp_resp_btb_info_by_lane = {
                {3'b111, 1'b1, 12'he1e},
                {3'b110, 1'b0, 12'hf0f},
                {3'b101, 1'b1, 12'he1e},
                {3'b100, 1'b0, 12'hf0f},
                {3'b011, 1'b1, 12'he1e},
                {3'b010, 1'b0, 12'hf0f},
                {3'b001, 1'b1, 12'he1e},
                {3'b000, 1'b0, 12'hf0f}
            };
            expected_read_resp_hit_by_lane = 8'b01010100;
            expected_read_resp_hit_way_by_lane = 8'b00000000;
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp index = 0x%2h", 6'h3f);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_index = 6'h00;
        // read resp stage
        tb_read_resp_pc38 = {29'h0f0f0f0f, 6'h3f, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 12'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_resp_resp_btb_info_by_lane = {
            {3'b111, 1'b1, 12'he1e},
            {3'b110, 1'b0, 12'hf0f},
            {3'b101, 1'b1, 12'he1e},
            {3'b100, 1'b0, 12'hf0f},
            {3'b011, 1'b1, 12'he1e},
            {3'b010, 1'b0, 12'hf0f},
            {3'b001, 1'b1, 12'he1e},
            {3'b000, 1'b0, 12'hf0f}
        };
        expected_read_resp_hit_by_lane = 8'b01010100;
        expected_read_resp_hit_way_by_lane = 8'b00000000;
        // update

        check_outputs();

        // ------------------------------------------------------------
        // way 0 read for 1e:
        test_case = "way 0 read for 1e";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("req index = 0x%2h", 6'h00);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 6'h00;
        // read resp stage
        tb_read_resp_pc38 = {29'h0f0f0f0f, 6'h00, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 12'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_resp_resp_btb_info_by_lane = {
            {3'b111, 1'b1, 12'he1e},
            {3'b110, 1'b0, 12'hf0f},
            {3'b101, 1'b1, 12'he1e},
            {3'b100, 1'b0, 12'hf0f},
            {3'b011, 1'b1, 12'he1e},
            {3'b010, 1'b0, 12'hf0f},
            {3'b001, 1'b1, 12'he1e},
            {3'b000, 1'b0, 12'hf0f}
        };
        expected_read_resp_hit_by_lane = 8'b01010100;
        expected_read_resp_hit_way_by_lane = 8'b00000000;
        // update

        check_outputs();

        for (int index = 1; index < corep::BTB_SETS; index++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req index = 0x%2h, resp index = 0x%2h", index, index-1);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h0000;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_index = index;
            // read resp stage
            tb_read_resp_pc38 = {29'h1e1e1e1e, {index-1}[5:0], 3'h0};
            // update
            tb_update_valid = 1'b0;
            tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
            tb_update_btb_info = {3'b000, 1'b0, 12'h000};
            tb_update_hit = 1'b0;
            tb_update_hit_way = 1'b0;

            @(negedge CLK);

            // arch state
            // read req stage
            // read resp stage
            expected_resp_resp_btb_info_by_lane = {
                {3'b111, 1'b1, 12'he1e},
                {3'b110, 1'b0, 12'hf0f},
                {3'b101, 1'b1, 12'he1e},
                {3'b100, 1'b0, 12'hf0f},
                {3'b011, 1'b1, 12'he1e},
                {3'b010, 1'b0, 12'hf0f},
                {3'b001, 1'b1, 12'he1e},
                {3'b000, 1'b0, 12'hf0f}
            };
            expected_read_resp_hit_by_lane = 8'b10101010;
            expected_read_resp_hit_way_by_lane = 8'b00000000;
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("resp index = 0x%2h", 6'h3f);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 6'h3f;
        // read resp stage
        tb_read_resp_pc38 = {29'h1e1e1e1e, 6'h3f, 3'h0};
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {29'h00000000, 6'h00, 3'h0};
        tb_update_btb_info = {3'b000, 1'b0, 12'h000};
        tb_update_hit = 1'b0;
        tb_update_hit_way = 1'b0;

        @(negedge CLK);

        // arch state
        // read req stage
        // read resp stage
        expected_resp_resp_btb_info_by_lane = {
            {3'b111, 1'b1, 12'he1e},
            {3'b110, 1'b0, 12'hf0f},
            {3'b101, 1'b1, 12'he1e},
            {3'b100, 1'b0, 12'hf0f},
            {3'b011, 1'b1, 12'he1e},
            {3'b010, 1'b0, 12'hf0f},
            {3'b001, 1'b1, 12'he1e},
            {3'b000, 1'b0, 12'hf0f}
        };
        expected_read_resp_hit_by_lane = 8'b10101010;
        expected_read_resp_hit_way_by_lane = 8'b00000000;
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