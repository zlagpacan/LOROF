/*
    Filename: ibtb_tb.sv
    Author: zlagpacan
    Description: Testbench for ibtb module. 
    Spec: LOROF/spec/design/ibtb.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module ibtb_tb #(
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


    // read
	corep::pc38_t tb_read_src_pc38;
	corep::ibtb_gh_t tb_read_ibtb_gh;
	corep::asid_t tb_read_asid;

	corep::pc38_t DUT_read_tgt_pc38, expected_read_tgt_pc38;

    // update
	logic tb_update_valid;
	corep::pc38_t tb_update_src_pc38;
	corep::ibtb_gh_t tb_update_ibtb_gh;
	corep::asid_t tb_update_asid;
	corep::pc38_t tb_update_tgt_pc38;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ibtb #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // read
		.read_src_pc38(tb_read_src_pc38),
		.read_ibtb_gh(tb_read_ibtb_gh),
		.read_asid(tb_read_asid),

		.read_tgt_pc38(DUT_read_tgt_pc38),

	    // update
		.update_valid(tb_update_valid),
		.update_src_pc38(tb_update_src_pc38),
		.update_ibtb_gh(tb_update_ibtb_gh),
		.update_asid(tb_update_asid),
		.update_tgt_pc38(tb_update_tgt_pc38)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_tgt_pc38 !== DUT_read_tgt_pc38) begin
			$display("TB ERROR: expected_read_tgt_pc38 (%h) != DUT_read_tgt_pc38 (%h)",
				expected_read_tgt_pc38, DUT_read_tgt_pc38);
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
	    // read
		tb_read_src_pc38 = 38'h0000000000;
		tb_read_ibtb_gh = 5'h00;
        tb_read_asid = {11'h000, 5'h00};
	    // update
		tb_update_valid = 1'b0;
		tb_update_src_pc38 = 38'h0000000000;
		tb_update_ibtb_gh = 5'h00;
        tb_update_asid = {11'h000, 5'h00};
		tb_update_tgt_pc38 = 38'h0000000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read
		expected_read_tgt_pc38 = 38'h0000000000;
	    // update

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read
		tb_read_src_pc38 = 38'h0000000000;
		tb_read_ibtb_gh = 5'h00;
        tb_read_asid = {11'h000, 5'h00};
	    // update
		tb_update_valid = 1'b0;
		tb_update_src_pc38 = 38'h0000000000;
		tb_update_ibtb_gh = 5'h00;
        tb_update_asid = {11'h000, 5'h00};
		tb_update_tgt_pc38 = 38'h0000000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // arch state
	    // read
		expected_read_tgt_pc38 = 38'h0000000000;
	    // update

		check_outputs();

        // ------------------------------------------------------------
        // fill:
        test_case = "fill";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < corep::IBTB_ENTRIES; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("index = %02h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // read
            tb_read_src_pc38 = {33'h000000000, 5'h00};
            tb_read_ibtb_gh = 5'h00;
		    tb_read_asid = {11'h000, 5'h00};
            // update
            tb_update_valid = 1'b1;
            tb_update_src_pc38 = {33'h000000000, i[4], 1'b0, i[2], 1'b0, i[0]};
            tb_update_ibtb_gh = {1'b0, i[3], 1'b0, i[1], 1'b0};
		    tb_update_asid = {11'h000, 5'h00};
            tb_update_tgt_pc38 = {4{~i[4:0], i[4:0]}};

            @(negedge CLK);

            // outputs:

            // arch state
            // read
            expected_read_tgt_pc38 = i > 0 ? {4{5'h1f, 5'h00}} : 38'h0000000000;
            // update

            check_outputs();
        end

        // ------------------------------------------------------------
        // readout:
        test_case = "readout";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < corep::IBTB_ENTRIES; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("index = %02h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // read
            tb_read_src_pc38 = {33'h000000000, 1'b1, i[3], 1'b1, i[1], 1'b1};
            tb_read_ibtb_gh = {i[4], 1'b1, i[2], 1'b1, i[0]};
            tb_read_asid = {11'h000, 5'h1f};
            // update
            tb_update_valid = 1'b1;
            tb_update_src_pc38 = {33'h000000000, 5'h00};
            tb_update_ibtb_gh = 5'h00;
            tb_update_asid = {11'h000, 5'h00};
            tb_update_tgt_pc38 = 38'h0000000000;

            @(negedge CLK);

            // outputs:

            // arch state
            // read
            expected_read_tgt_pc38 = {4{~i[4:0], i[4:0]}};
            // update

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