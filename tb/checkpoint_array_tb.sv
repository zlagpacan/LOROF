/*
    Filename: checkpoint_array_tb.sv
    Author: zlagpacan
    Description: Testbench for checkpoint_array module. 
    Spec: LOROF/spec/design/checkpoint_array.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module checkpoint_array_tb ();

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

    // checkpoint save
	logic tb_save_valid;
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_save_map_table;
	logic [LH_LENGTH-1:0] tb_save_LH;
	logic [GH_LENGTH-1:0] tb_save_GH;
	logic [RAS_INDEX_WIDTH-1:0] tb_save_ras_index;

	logic DUT_save_success, expected_save_success;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] DUT_save_index, expected_save_index;

    // checkpoint restore
	logic tb_restore_valid;
	logic tb_restore_index;

	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] DUT_restore_map_table, expected_restore_map_table;
	logic [LH_LENGTH-1:0] DUT_restore_LH, expected_restore_LH;
	logic [GH_LENGTH-1:0] DUT_restore_GH, expected_restore_GH;
	logic [RAS_INDEX_WIDTH-1:0] DUT_restore_ras_index, expected_restore_ras_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	checkpoint_array #(
		.CHECKPOINT_COUNT(8)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // checkpoint save
		.save_valid(tb_save_valid),
		.save_map_table(tb_save_map_table),
		.save_LH(tb_save_LH),
		.save_GH(tb_save_GH),
		.save_ras_index(tb_save_ras_index),

		.save_success(DUT_save_success),
		.save_index(DUT_save_index),

	    // checkpoint restore
		.restore_valid(tb_restore_valid),
		.restore_index(tb_restore_index),

		.restore_map_table(DUT_restore_map_table),
		.restore_LH(DUT_restore_LH),
		.restore_GH(DUT_restore_GH),
		.restore_ras_index(DUT_restore_ras_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_save_success !== DUT_save_success) begin
			$display("TB ERROR: expected_save_success (%h) != DUT_save_success (%h)",
				expected_save_success, DUT_save_success);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_save_index !== DUT_save_index) begin
			$display("TB ERROR: expected_save_index (%h) != DUT_save_index (%h)",
				expected_save_index, DUT_save_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restore_map_table !== DUT_restore_map_table) begin
			$display("TB ERROR: expected_restore_map_table (%h) != DUT_restore_map_table (%h)",
				expected_restore_map_table, DUT_restore_map_table);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restore_LH !== DUT_restore_LH) begin
			$display("TB ERROR: expected_restore_LH (%h) != DUT_restore_LH (%h)",
				expected_restore_LH, DUT_restore_LH);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restore_GH !== DUT_restore_GH) begin
			$display("TB ERROR: expected_restore_GH (%h) != DUT_restore_GH (%h)",
				expected_restore_GH, DUT_restore_GH);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restore_ras_index !== DUT_restore_ras_index) begin
			$display("TB ERROR: expected_restore_ras_index (%h) != DUT_restore_ras_index (%h)",
				expected_restore_ras_index, DUT_restore_ras_index);
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
	    // checkpoint save
		tb_save_valid = 1'b0;
		tb_save_map_table = '0;
		tb_save_LH = '0;
		tb_save_GH = '0;
		tb_save_ras_index = '0;
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_index = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // checkpoint save
		expected_save_success = 1'b0;
		expected_save_index = '0;
	    // checkpoint restore
		expected_restore_map_table = 'x;
		expected_restore_LH = 'x;
		expected_restore_GH = 'x;
		expected_restore_ras_index = 'x;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b0;
		tb_save_map_table = '0;
		tb_save_LH = '0;
		tb_save_GH = '0;
		tb_save_ras_index = '0;
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_index = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // checkpoint save
		expected_save_success = 1'b0;
		expected_save_index = '0;
	    // checkpoint restore
		expected_restore_map_table = 'x;
		expected_restore_LH = 'x;
		expected_restore_GH = 'x;
		expected_restore_ras_index = 'x;

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
	    // checkpoint save
		tb_save_valid = 1'b0;
		tb_save_map_table = '0;
		tb_save_LH = '0;
		tb_save_GH = '0;
		tb_save_ras_index = '0;
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_index = '0;

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_success = 1'b0;
		expected_save_index = '0;
	    // checkpoint restore
		expected_restore_map_table = 'x;
		expected_restore_LH = 'x;
		expected_restore_GH = 'x;
		expected_restore_ras_index = 'x;

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