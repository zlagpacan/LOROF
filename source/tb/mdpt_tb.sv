/*
    Filename: mdpt_tb.sv
    Author: zlagpacan
    Description: Testbench for mdpt module. 
    Spec: LOROF/spec/design/mdpt.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module mdpt_tb #(
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
	corep::asid_t tb_arch_asid;

    // read req stage
	logic tb_read_req_valid;
	corep::fetch_idx_t tb_read_req_fetch_index;

    // read resp stage
	corep::mdpt_set_t DUT_read_resp_mdp_by_lane, expected_read_resp_mdp_by_lane;

    // update
	logic tb_update_valid;
	corep::pc38_t tb_update_pc38;
	corep::mdp_t tb_update_mdp;

    // ----------------------------------------------------------------
    // DUT instantiation:

	mdpt #(
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
		.read_resp_mdp_by_lane(DUT_read_resp_mdp_by_lane),

	    // update
		.update_valid(tb_update_valid),
		.update_pc38(tb_update_pc38),
		.update_mdp(tb_update_mdp)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_resp_mdp_by_lane !== DUT_read_resp_mdp_by_lane) begin
			$display("TB ERROR: expected_read_resp_mdp_by_lane (%h) != DUT_read_resp_mdp_by_lane (%h)",
				expected_read_resp_mdp_by_lane, DUT_read_resp_mdp_by_lane);
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
		tb_read_req_fetch_index = 7'h00;
	    // read resp stage
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {28'h0000000, 7'h00, 3'h0};
		tb_update_mdp = 8'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
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
		tb_read_req_fetch_index = 7'h00;
	    // read resp stage
	    // update
		tb_update_valid = 1'b0;
		tb_update_pc38 = {28'h0000000, 7'h00, 3'h0};
		tb_update_mdp = 8'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read req stage
	    // read resp stage
		expected_read_resp_mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
	    // update

		check_outputs();

        // ------------------------------------------------------------
        // fill:
        test_case = "fill";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int index = 0; index < corep::MDPT_SETS; index++) begin
            for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin

                @(posedge CLK); #(PERIOD/10);

                // inputs
                sub_test_case = $sformatf("index = 0x%02h, lane = %1h", index[6:0], lane);
                $display("\t- sub_test: %s", sub_test_case);

                // reset
                nRST = 1'b1;
                // arch state
                tb_arch_asid = 16'h0000;
                // read req stage
                tb_read_req_valid = 1'b0;
                tb_read_req_fetch_index = 7'h00;
                // read resp stage
                // update
                tb_update_valid = 1'b1;
                tb_update_pc38 = {28'h0000000, index[6:0], lane[2:0]};
                tb_update_mdp = {lane[0], index[6:0]};

                @(negedge CLK);

                // outputs:

                // arch state
                // read req stage
                // read resp stage
                expected_read_resp_mdp_by_lane = {
                    8'h00,
                    8'h00,
                    8'h00,
                    8'h00,
                    8'h00,
                    8'h00,
                    8'h00,
                    8'h00
                };
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
        sub_test_case = $sformatf("read req 0x%02h", 7'h7f);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h007f;
        // read req stage
        tb_read_req_valid = 1'b1;
        tb_read_req_fetch_index = 7'h00;
        // read resp stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {28'h0000000, 7'h00, 3'h0};
        tb_update_mdp = 8'h00;

        @(negedge CLK);

        // outputs:

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
        // update

        check_outputs();

        for (int index = corep::MDPT_SETS-2; index >= 0; index--) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("read req 0x%02h, read resp 0x%02h", index[6:0], {index+1}[6:0]);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // arch state
            tb_arch_asid = 16'h007f;
            // read req stage
            tb_read_req_valid = 1'b1;
            tb_read_req_fetch_index = ~index[6:0];
            // read resp stage
            // update
            tb_update_valid = 1'b0;
            tb_update_pc38 = {28'h0000000, 7'h00, 3'h0};
            tb_update_mdp = 8'h00;

            @(negedge CLK);

            // outputs:

            // arch state
            // read req stage
            // read resp stage
            expected_read_resp_mdp_by_lane = {
                {1'b1, {index+1}[6:0]},
                {1'b0, {index+1}[6:0]},
                {1'b1, {index+1}[6:0]},
                {1'b0, {index+1}[6:0]},
                {1'b1, {index+1}[6:0]},
                {1'b0, {index+1}[6:0]},
                {1'b1, {index+1}[6:0]},
                {1'b0, {index+1}[6:0]}
            };
            // update

            check_outputs();
        end

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = $sformatf("read resp 0x%02h", 7'h00);
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // arch state
        tb_arch_asid = 16'h0000;
        // read req stage
        tb_read_req_valid = 1'b0;
        tb_read_req_fetch_index = 7'h00;
        // read resp stage
        // update
        tb_update_valid = 1'b0;
        tb_update_pc38 = {28'h0000000, 7'h00, 3'h0};
        tb_update_mdp = 8'h00;

        @(negedge CLK);

        // outputs:

        // arch state
        // read req stage
        // read resp stage
        expected_read_resp_mdp_by_lane = {
            {1'b1, 7'h00},
            {1'b0, 7'h00},
            {1'b1, 7'h00},
            {1'b0, 7'h00},
            {1'b1, 7'h00},
            {1'b0, 7'h00},
            {1'b1, 7'h00},
            {1'b0, 7'h00}
        };
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