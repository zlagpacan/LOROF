/*
    Filename: sst_tb.sv
    Author: zlagpacan
    Description: Testbench for sst module. 
    Spec: LOROF/spec/design/sst.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module sst_tb ();

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

    // new SSID check
	logic tb_new_SSID_valid;
	logic [SSID_WIDTH-1:0] DUT_new_SSID, expected_new_SSID;

    // touch check
	logic tb_touch_SSID_valid;
	logic [SSID_WIDTH-1:0] tb_touch_SSID;

    // ----------------------------------------------------------------
    // DUT instantiation:

	sst #(
        .STORE_SET_COUNT(64),
        .SSID_WIDTH($clog2(STORE_SET_COUNT))
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // new SSID check
		.new_SSID_valid(tb_new_SSID_valid),
		.new_SSID(DUT_new_SSID),

	    // touch check
		.touch_SSID_valid(tb_touch_SSID_valid),
		.touch_SSID(tb_touch_SSID)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_new_SSID !== DUT_new_SSID) begin
			$display("TB ERROR: expected_new_SSID (%h) != DUT_new_SSID (%h)",
				expected_new_SSID, DUT_new_SSID);
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
	    // new SSID check
		tb_new_SSID_valid = 1'b0;
	    // touch check
		tb_touch_SSID_valid = 1'b0;
		tb_touch_SSID = 6'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // new SSID check
		expected_new_SSID = 6'h0;
	    // touch check

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new SSID check
		tb_new_SSID_valid = 1'b0;
	    // touch check
		tb_touch_SSID_valid = 1'b0;
		tb_touch_SSID = 6'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // new SSID check
		expected_new_SSID = 6'h0;
	    // touch check

		check_outputs();

        // ------------------------------------------------------------
        // new sequence:
        test_case = "new sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 64; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("new %0h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // new SSID check
            tb_new_SSID_valid = 1'b1;
            // touch check
            tb_touch_SSID_valid = 1'b0;
            tb_touch_SSID = 6'h0;

            @(negedge CLK);

            // outputs:

            // new SSID check
            expected_new_SSID = 6'h0;
            // touch check

            check_outputs();
        end

        // ------------------------------------------------------------
        // touch sequence:
        test_case = "touch sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 64; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("touch %0h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // new SSID check
            tb_new_SSID_valid = 1'b0;
            // touch check
            tb_touch_SSID_valid = 1'b1;
            tb_touch_SSID = i + 32;

            @(negedge CLK);

            // outputs:

            // new SSID check
            expected_new_SSID = 6'h0;
            // touch check

            check_outputs();
        end

        // ------------------------------------------------------------
        // random sequence:
        test_case = "random sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 64; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("random %0h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // new SSID check
            tb_new_SSID_valid = ((i+1) % 3) == 0;
            // touch check
            tb_touch_SSID_valid = ((i+2) % 5) == 0;
            tb_touch_SSID = (i*55) + 17;

            @(negedge CLK);

            // outputs:

            // new SSID check
            expected_new_SSID = 6'h0;
            // touch check

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
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule