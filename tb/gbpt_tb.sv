/*
    Filename: gbpt_tb.sv
    Author: zlagpacan
    Description: Testbench for gbpt module. 
    Spec: LOROF/spec/design/gbpt.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module gbpt_tb ();

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
	logic tb_valid_RESP;
	logic [31:0] tb_full_PC_RESP;
	logic [GH_LENGTH-1:0] tb_GH_RESP;
	logic [ASID_WIDTH-1:0] tb_ASID_RESP;

    // RESTART stage
	logic DUT_pred_taken_RESTART, expected_pred_taken_RESTART;

    // Update 0
	logic tb_update0_valid;
	logic [31:0] tb_update0_start_full_PC;
	logic [GH_LENGTH-1:0] tb_update0_GH;
	logic [ASID_WIDTH-1:0] tb_update0_ASID;
	logic tb_update0_taken;

    // Update 1
	logic DUT_update1_correct, expected_update1_correct;

    // ----------------------------------------------------------------
    // DUT instantiation:

	gbpt DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // RESP stage
		.valid_RESP(tb_valid_RESP),
		.full_PC_RESP(tb_full_PC_RESP),
		.GH_RESP(tb_GH_RESP),
		.ASID_RESP(tb_ASID_RESP),

	    // RESTART stage
		.pred_taken_RESTART(DUT_pred_taken_RESTART),

	    // Update 0
		.update0_valid(tb_update0_valid),
		.update0_start_full_PC(tb_update0_start_full_PC),
		.update0_GH(tb_update0_GH),
		.update0_ASID(tb_update0_ASID),
		.update0_taken(tb_update0_taken),

	    // Update 1
		.update1_correct(DUT_update1_correct)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_pred_taken_RESTART !== DUT_pred_taken_RESTART) begin
			$display("TB ERROR: expected_pred_taken_RESTART (%h) != DUT_pred_taken_RESTART (%h)",
				expected_pred_taken_RESTART, DUT_pred_taken_RESTART);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_update1_correct !== DUT_update1_correct) begin
			$display("TB ERROR: expected_update1_correct (%h) != DUT_update1_correct (%h)",
				expected_update1_correct, DUT_update1_correct);
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
		tb_valid_RESP = 1'b0;
		tb_full_PC_RESP = 32'h0;
		tb_GH_RESP = 12'h0;
		tb_ASID_RESP = 9'h0;
	    // RESTART stage
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
		tb_update0_GH = 12'h0;
		tb_update0_ASID = 9'h0;
		tb_update0_taken = 1'b0;
	    // Update 1

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // RESP stage
	    // RESTART stage
		expected_pred_taken_RESTART = 1'b0;
	    // Update 0
	    // Update 1
		expected_update1_correct = 1'b1;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_valid_RESP = 1'b0;
		tb_full_PC_RESP = 32'h0;
		tb_GH_RESP = 12'h0;
		tb_ASID_RESP = 9'h0;
	    // RESTART stage
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
		tb_update0_GH = 12'h0;
		tb_update0_ASID = 9'h0;
		tb_update0_taken = 1'b0;
	    // Update 1

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // RESP stage
	    // RESTART stage
		expected_pred_taken_RESTART = 1'b0;
	    // Update 0
	    // Update 1
		expected_update1_correct = 1'b1;

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "default";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_valid_RESP = 1'b0;
		tb_full_PC_RESP = 32'h0;
		tb_GH_RESP = 12'h0;
		tb_ASID_RESP = 9'h0;
	    // RESTART stage
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
		tb_update0_GH = 12'h0;
		tb_update0_ASID = 9'h0;
		tb_update0_taken = 1'b0;
	    // Update 1

		@(negedge CLK);

		// outputs:

	    // RESP stage
	    // RESTART stage
		expected_pred_taken_RESTART = 1'b0;
	    // Update 0
	    // Update 1
		expected_update1_correct = 1'b1;

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