/*
    Filename: ras_tb.sv
    Author: zlagpacan
    Description: Testbench for ras module. 
    Spec: LOROF/spec/design/ras.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module ras_tb #(
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


    // pc_gen link control
	logic tb_link_valid;
	corep::pc38_t tb_link_pc38;

    // pc_gen return control
	logic tb_ret_valid;

	logic DUT_ret_fallback, expected_ret_fallback;
	corep::pc38_t DUT_ret_pc38, expected_ret_pc38;
	corep::ras_idx_t DUT_ret_ras_idx, expected_ret_ras_idx;
	corep::ras_cnt_t DUT_ret_ras_cnt, expected_ret_ras_cnt;

    // update control
	logic tb_update_valid;
	corep::ras_idx_t tb_update_ras_idx;
	corep::ras_cnt_t tb_update_ras_cnt;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ras #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // pc_gen link control
		.link_valid(tb_link_valid),
		.link_pc38(tb_link_pc38),

	    // pc_gen return control
		.ret_valid(tb_ret_valid),

		.ret_fallback(DUT_ret_fallback),
		.ret_pc38(DUT_ret_pc38),
		.ret_ras_idx(DUT_ret_ras_idx),
		.ret_ras_cnt(DUT_ret_ras_cnt),

	    // update control
		.update_valid(tb_update_valid),
		.update_ras_idx(tb_update_ras_idx),
		.update_ras_cnt(tb_update_ras_cnt)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ret_fallback !== DUT_ret_fallback) begin
			$display("TB ERROR: expected_ret_fallback (%h) != DUT_ret_fallback (%h)",
				expected_ret_fallback, DUT_ret_fallback);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ret_pc38 !== DUT_ret_pc38) begin
			$display("TB ERROR: expected_ret_pc38 (%h) != DUT_ret_pc38 (%h)",
				expected_ret_pc38, DUT_ret_pc38);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ret_ras_idx !== DUT_ret_ras_idx) begin
			$display("TB ERROR: expected_ret_ras_idx (%h) != DUT_ret_ras_idx (%h)",
				expected_ret_ras_idx, DUT_ret_ras_idx);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ret_ras_cnt !== DUT_ret_ras_cnt) begin
			$display("TB ERROR: expected_ret_ras_cnt (%h) != DUT_ret_ras_cnt (%h)",
				expected_ret_ras_cnt, DUT_ret_ras_cnt);
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
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = 38'h0000000000;
		expected_ret_ras_idx = 4'h0;
		expected_ret_ras_cnt = 0;
	    // update control

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = 38'h0000000000;
		expected_ret_ras_idx = 4'h0;
		expected_ret_ras_cnt = 0;
	    // update control

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "link 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b1;
		tb_link_pc38 = 38'h1111111111;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = 38'h0000000000;
		expected_ret_ras_idx = 4'h0;
		expected_ret_ras_cnt = 0;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "link 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
	    // pc_gen link control
		tb_link_valid = 1'b1;
		tb_link_pc38 = 38'h2222222222;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		expected_ret_fallback = 1'b0;
		tb_update_valid = 1'b0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'h1111111111;
		expected_ret_ras_idx = 4'h1;
		expected_ret_ras_cnt = 1;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h3333333333;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'h2222222222;
		expected_ret_ras_idx = 4'h2;
		expected_ret_ras_cnt = 2;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "link + ret 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b1;
		tb_link_pc38 = 38'h5555555555;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'h1111111111;
		expected_ret_ras_idx = 4'h1;
		expected_ret_ras_cnt = 1;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "update to E";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		tb_update_valid = 1'b1;
		tb_update_ras_idx = 4'hE;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'h5555555555;
		expected_ret_ras_idx = 4'h1;
		expected_ret_ras_cnt = 1;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "update to 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		tb_update_valid = 1'b1;
		tb_update_ras_idx = 4'h3;
		tb_update_ras_cnt = 3;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = 38'h0000000000;
		expected_ret_ras_idx = 4'hE;
		expected_ret_ras_cnt = 0;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret to 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'h0000000000;
		expected_ret_ras_idx = 4'h3;
		expected_ret_ras_cnt = 3;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret to 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'h2222222222;
		expected_ret_ras_idx = 4'h2;
		expected_ret_ras_cnt = 2;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret to 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'h5555555555;
		expected_ret_ras_idx = 4'h1;
		expected_ret_ras_cnt = 1;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "link A and fallback";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b1;
		tb_link_pc38 = 38'hAAAAAAAAAA;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = 38'h0000000000;
		expected_ret_ras_idx = 4'h0;
		expected_ret_ras_cnt = 0;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret A";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b0;
		expected_ret_pc38 = 38'hAAAAAAAAAA;
		expected_ret_ras_idx = 4'h1;
		expected_ret_ras_cnt = 1;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret fallback";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b1;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = 38'h0000000000;
		expected_ret_ras_idx = 4'h0;
		expected_ret_ras_cnt = 0;
	    // update control

		check_outputs();

        for (int i = 0; i < 21; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("link to overflow 0x%2h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // pc_gen link control
            tb_link_valid = 1'b1;
            tb_link_pc38 = {8{i[4:0]}};
            // pc_gen return control
            tb_ret_valid = 1'b0;
            // update control
            tb_update_valid = 1'b0;
            tb_update_ras_idx = 4'h0;
            tb_update_ras_cnt = 0;

            @(negedge CLK);

            // outputs:

            // pc_gen link control
            // pc_gen return control
            expected_ret_fallback = i > 0 ? 1'b0 : 1'b1;
            expected_ret_pc38 = i > 0 ? {8{{i-1}[4:0]}} : 38'h0000000000;
            expected_ret_ras_idx = i[3:0];
            expected_ret_ras_cnt = i <= 16 ? i : 16;
            // update control

            check_outputs();
        end

        for (int i = 20; i >= 5; i--) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("ret back from overflow 0x%2h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // pc_gen link control
            tb_link_valid = 1'b0;
            tb_link_pc38 = 38'h0000000000;
            // pc_gen return control
            tb_ret_valid = 1'b1;
            // update control
            tb_update_valid = 1'b0;
            tb_update_ras_idx = 4'h0;
            tb_update_ras_cnt = 0;

            @(negedge CLK);

            // outputs:

            // pc_gen link control
            // pc_gen return control
            expected_ret_fallback = i > 0 ? 1'b0 : 1'b1;
            expected_ret_pc38 = {8{i[4:0]}};
            expected_ret_ras_idx = {i+1}[3:0];
            expected_ret_ras_cnt = i - 4;
            // update control

            check_outputs();
        end

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret fallback at overflow stop 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = {8{5'h14}};
		expected_ret_ras_idx = 4'h5;
		expected_ret_ras_cnt = 0;
	    // update control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "done";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // pc_gen link control
		tb_link_valid = 1'b0;
		tb_link_pc38 = 38'h0000000000;
	    // pc_gen return control
		tb_ret_valid = 1'b0;
	    // update control
		tb_update_valid = 1'b0;
		tb_update_ras_idx = 4'h0;
		tb_update_ras_cnt = 0;

		@(negedge CLK);

		// outputs:

	    // pc_gen link control
	    // pc_gen return control
		expected_ret_fallback = 1'b1;
		expected_ret_pc38 = {8{5'h14}};
		expected_ret_ras_idx = 4'h5;
		expected_ret_ras_cnt = 0;
	    // update control

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
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule