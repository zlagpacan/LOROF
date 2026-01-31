/*
    Filename: upct_tb.sv
    Author: zlagpacan
    Description: Testbench for upct module. 
    Spec: LOROF/spec/design/upct.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module upct_tb #(
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


    // pc_gen read in
	logic tb_read_valid;
	corep::upct_idx_t tb_read_idx;

    // pc_gen read out
	corep::upc_t DUT_read_upc, expected_read_upc;

    // update in
	logic tb_update_valid;
	corep::upc_t tb_update_upc;

    // update out
	corep::upct_idx_t DUT_update_upct_idx, expected_update_upct_idx;

    // ----------------------------------------------------------------
    // DUT instantiation:

	upct #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // pc_gen read in
		.read_valid(tb_read_valid),
		.read_idx(tb_read_idx),

	    // pc_gen read out
		.read_upc(DUT_read_upc),

	    // update in
		.update_valid(tb_update_valid),
		.update_upc(tb_update_upc),

	    // update out
		.update_upct_idx(DUT_update_upct_idx)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_upc !== DUT_read_upc) begin
			$display("TB ERROR: expected_read_upc (%h) != DUT_read_upc (%h)",
				expected_read_upc, DUT_read_upc);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_update_upct_idx !== DUT_update_upct_idx) begin
			$display("TB ERROR: expected_update_upct_idx (%h) != DUT_update_upct_idx (%h)",
				expected_update_upct_idx, DUT_update_upct_idx);
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
	    // pc_gen read in
		tb_read_valid = 1'b0;
		tb_read_idx = 0;
	    // pc_gen read out
	    // update in
		tb_update_valid = 1'b0;
		tb_update_upc = 29'h00000000;
	    // update out

        $display("$bits(tb_update_upc) = %0d", $bits(tb_update_upc));

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // pc_gen read in
	    // pc_gen read out
		expected_read_upc = '0;
	    // update in
	    // update out
		expected_update_upct_idx = 0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen read in
		tb_read_valid = 1'b0;
		tb_read_idx = 0;
	    // pc_gen read out
	    // update in
		tb_update_valid = 1'b0;
		tb_update_upc = 29'h00000000;
	    // update out

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // pc_gen read in
	    // pc_gen read out
		expected_read_upc = '0;
	    // update in
	    // update out
		expected_update_upct_idx = 0;

		check_outputs();

        // ------------------------------------------------------------
        // update chain:
        test_case = "update chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 8; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("update chain %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // pc_gen read in
            tb_read_valid = 1'b0;
            tb_read_idx = 0;
            // pc_gen read out
            // update in
            tb_update_valid = 1'b1;
    		tb_update_upc = {9{i[2:0]}};
            // update out

            @(negedge CLK);

            // outputs:

            // pc_gen read in
            // pc_gen read out
            expected_read_upc = '0;
            // update in
            // update out
            expected_update_upct_idx = i;

            check_outputs();
        end

        // ------------------------------------------------------------
        // read chain:
        test_case = "read chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 7; i >= 0; i--) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("read chain %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // pc_gen read in
            tb_read_valid = 1'b1;
            tb_read_idx = i;
            // pc_gen read out
            // update in
            tb_update_valid = 1'b0;
    		tb_update_upc = 0;
            // update out

            @(negedge CLK);

            // outputs:

            // pc_gen read in
            // pc_gen read out
            expected_read_upc = {9{i[2:0]}};
            // update in
            // update out
            expected_update_upct_idx = {3'h0, 3'h0, 3'h1, 3'h0, 3'h3, 3'h2, 3'h1, 3'h0} >> i*3;

            check_outputs();
        end

        // ------------------------------------------------------------
        // update w/ existing chain:
        test_case = "update w/ existing chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 8; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("update w/ existing chain %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // pc_gen read in
            tb_read_valid = 1'b0;
            tb_read_idx = 0;
            // pc_gen read out
            // update in
            tb_update_valid = 1'b1;
    		tb_update_upc = {9{i[2:0]}};
            // update out

            @(negedge CLK);

            // outputs:

            // pc_gen read in
            // pc_gen read out
            expected_read_upc = '0;
            // update in
            // update out
            expected_update_upct_idx = i;

            check_outputs();
        end

        // ------------------------------------------------------------
        // update w/ new chain:
        test_case = "update w/ new chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 7; i >= 4; i--) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("update w/ new chain %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // pc_gen read in
            tb_read_valid = 1'b0;
            tb_read_idx = 0;
            // pc_gen read out
            // update in
            tb_update_valid = 1'b1;
    		tb_update_upc = {8{i[3:0]}};
            // update out

            @(negedge CLK);

            // outputs:

            // pc_gen read in
            // pc_gen read out
            expected_read_upc = (i == 7) ? 29'h00000000 : 29'h77777777;
            // update in
            // update out
            expected_update_upct_idx = {3'h0, 3'h1, 3'h2, 3'h3} >> (i-4)*3;

            check_outputs();
        end

        // ------------------------------------------------------------
        // final read chain:
        test_case = "final read chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 8; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("final read chain %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // pc_gen read in
            tb_read_valid = 1'b1;
            tb_read_idx = i;
            // pc_gen read out
            // update in
            tb_update_valid = 1'b0;
    		tb_update_upc = 29'h00000000;
            // update out

            @(negedge CLK);

            // outputs:

            // pc_gen read in
            // pc_gen read out
            expected_read_upc = (i < 4) ? {8{{7-i}[3:0]}} : {9{i[2:0]}};
            // update in
            // update out
            expected_update_upct_idx = (i < 4) ? i + 4 : i;

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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule