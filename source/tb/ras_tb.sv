/*
    Filename: ras_tb.sv
    Author: zlagpacan
    Description: Testbench for ras module. 
    Spec: LOROF/spec/design/ras.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ras_tb ();

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


    // RESP stage
	logic tb_link_RESP;
	logic [31:0] tb_link_full_PC_RESP;
	logic tb_ret_RESP;
	logic [31:0] DUT_ret_full_PC_RESP, expected_ret_full_PC_RESP;
	logic [RAS_INDEX_WIDTH-1:0] DUT_ras_index_RESP, expected_ras_index_RESP;

    // Update 0
	logic tb_update0_valid;
	logic [RAS_INDEX_WIDTH-1:0] tb_update0_ras_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ras DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // RESP stage
		.link_RESP(tb_link_RESP),
		.link_full_PC_RESP(tb_link_full_PC_RESP),
		.ret_RESP(tb_ret_RESP),
		.ret_full_PC_RESP(DUT_ret_full_PC_RESP),
		.ras_index_RESP(DUT_ras_index_RESP),

	    // Update 0
		.update0_valid(tb_update0_valid),
		.update0_ras_index(tb_update0_ras_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ret_full_PC_RESP !== DUT_ret_full_PC_RESP) begin
			$display("TB ERROR: expected_ret_full_PC_RESP (%h) != DUT_ret_full_PC_RESP (%h)",
				expected_ret_full_PC_RESP, DUT_ret_full_PC_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ras_index_RESP !== DUT_ras_index_RESP) begin
			$display("TB ERROR: expected_ras_index_RESP (%h) != DUT_ras_index_RESP (%h)",
				expected_ras_index_RESP, DUT_ras_index_RESP);
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
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b0;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h0;
		expected_ras_index_RESP = 3'h0;
	    // Update 0

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b0;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h0;
		expected_ras_index_RESP = 3'h0;
	    // Update 0

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
	    // RESP stage
		tb_link_RESP = 1'b1;
		tb_link_full_PC_RESP = 32'h11111111;
		tb_ret_RESP = 1'b0;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h0;
		expected_ras_index_RESP = 3'h0;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "link 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b1;
		tb_link_full_PC_RESP = 32'h22222222;
		tb_ret_RESP = 1'b0;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h11111110;
		expected_ras_index_RESP = 3'h1;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h33333333;
		tb_ret_RESP = 1'b1;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h22222222;
		expected_ras_index_RESP = 3'h2;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "link + ret 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b1;
		tb_link_full_PC_RESP = 32'h55555555;
		tb_ret_RESP = 1'b1;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h11111110;
		expected_ras_index_RESP = 3'h1;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "update to 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b0;
	    // Update 0
		tb_update0_valid = 1'b1;
		tb_update0_ras_index = 3'h7;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h55555554;
		expected_ras_index_RESP = 3'h1;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "update to 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b0;
	    // Update 0
		tb_update0_valid = 1'b1;
		tb_update0_ras_index = 3'h3;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h0;
		expected_ras_index_RESP = 3'h7;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret to 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b1;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h0;
		expected_ras_index_RESP = 3'h3;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret to 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b1;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h22222222;
		expected_ras_index_RESP = 3'h2;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ret to 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b1;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h55555554;
		expected_ras_index_RESP = 3'h1;
	    // Update 0

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "done";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_link_RESP = 1'b0;
		tb_link_full_PC_RESP = 32'h0;
		tb_ret_RESP = 1'b0;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_ras_index = 3'h0;

		@(negedge CLK);

		// outputs:

	    // RESP stage
		expected_ret_full_PC_RESP = 32'h0;
		expected_ras_index_RESP = 3'h0;
	    // Update 0

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