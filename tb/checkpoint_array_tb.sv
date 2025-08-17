/*
    Filename: checkpoint_array_tb.sv
    Author: zlagpacan
    Description: Testbench for checkpoint_array module. 
    Spec: LOROF/spec/design/checkpoint_array.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter CHECKPOINT_COUNT = 8;
parameter CHECKPOINT_INDEX_WIDTH = $clog2(CHECKPOINT_COUNT);
parameter CHECKPOINT_THRESHOLD = 4;

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

	logic DUT_save_ready, expected_save_ready;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] DUT_save_index, expected_save_index;

    // map table restore
	logic [CHECKPOINT_INDEX_WIDTH-1:0] tb_map_table_restore_index;
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] DUT_map_table_restore_map_table, expected_map_table_restore_map_table;

    // branch info restore
	logic [CHECKPOINT_INDEX_WIDTH-1:0] tb_branch_info_restore_index;
	logic [LH_LENGTH-1:0] DUT_branch_info_restore_LH, expected_branch_info_restore_LH;
	logic [GH_LENGTH-1:0] DUT_branch_info_restore_GH, expected_branch_info_restore_GH;
	logic [RAS_INDEX_WIDTH-1:0] DUT_branch_info_restore_ras_index, expected_branch_info_restore_ras_index;

    // checkpoint clear
	logic tb_clear_valid;
	logic [CHECKPOINT_INDEX_WIDTH-1:0] tb_clear_index;

    // advertized threshold
	logic DUT_above_threshold, expected_above_threshold;

    // ----------------------------------------------------------------
    // DUT instantiation:

	checkpoint_array #(
		.CHECKPOINT_COUNT(CHECKPOINT_COUNT),
		.CHECKPOINT_INDEX_WIDTH(CHECKPOINT_INDEX_WIDTH),
		.CHECKPOINT_THRESHOLD(CHECKPOINT_THRESHOLD)
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

		.save_ready(DUT_save_ready),
		.save_index(DUT_save_index),

	    // map table restore
		.map_table_restore_index(tb_map_table_restore_index),
		.map_table_restore_map_table(DUT_map_table_restore_map_table),

	    // branch info restore
		.branch_info_restore_index(tb_branch_info_restore_index),
		.branch_info_restore_LH(DUT_branch_info_restore_LH),
		.branch_info_restore_GH(DUT_branch_info_restore_GH),
		.branch_info_restore_ras_index(DUT_branch_info_restore_ras_index),

	    // checkpoint clear
		.clear_valid(tb_clear_valid),
		.clear_index(tb_clear_index),

	    // advertized threshold
		.above_threshold(DUT_above_threshold)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_save_ready !== DUT_save_ready) begin
			$display("TB ERROR: expected_save_ready (%h) != DUT_save_ready (%h)",
				expected_save_ready, DUT_save_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_save_index !== DUT_save_index) begin
			$display("TB ERROR: expected_save_index (%h) != DUT_save_index (%h)",
				expected_save_index, DUT_save_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_map_table_restore_map_table !== DUT_map_table_restore_map_table) begin
			$display("TB ERROR: expected_map_table_restore_map_table (%h) != DUT_map_table_restore_map_table (%h)",
				expected_map_table_restore_map_table, DUT_map_table_restore_map_table);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_info_restore_LH !== DUT_branch_info_restore_LH) begin
			$display("TB ERROR: expected_branch_info_restore_LH (%h) != DUT_branch_info_restore_LH (%h)",
				expected_branch_info_restore_LH, DUT_branch_info_restore_LH);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_info_restore_GH !== DUT_branch_info_restore_GH) begin
			$display("TB ERROR: expected_branch_info_restore_GH (%h) != DUT_branch_info_restore_GH (%h)",
				expected_branch_info_restore_GH, DUT_branch_info_restore_GH);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_info_restore_ras_index !== DUT_branch_info_restore_ras_index) begin
			$display("TB ERROR: expected_branch_info_restore_ras_index (%h) != DUT_branch_info_restore_ras_index (%h)",
				expected_branch_info_restore_ras_index, DUT_branch_info_restore_ras_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_above_threshold !== DUT_above_threshold) begin
			$display("TB ERROR: expected_above_threshold (%h) != DUT_above_threshold (%h)",
				expected_above_threshold, DUT_above_threshold);
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
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 0;
	    // map table restore
		expected_map_table_restore_map_table = '0;
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b1;

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
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 0;
	    // map table restore
		expected_map_table_restore_map_table = '0;
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b1;

        // ------------------------------------------------------------
        // save chain:
        test_case = "save chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 0: AR";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i;
		end
		tb_save_LH = 8'h00;
		tb_save_GH = 12'h000;
		tb_save_ras_index = 3'h0;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = '0;
	    // map table restore
		expected_map_table_restore_map_table = '0;
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 1: AR + 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 1;
		end
		tb_save_LH = 8'h11;
		tb_save_GH = 12'h111;
		tb_save_ras_index = 3'h1;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h1;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 2: AR * 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i * 2;
		end
		tb_save_LH = 8'h22;
		tb_save_GH = 12'h222;
		tb_save_ras_index = 3'h2;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h2;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 3: AR + 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 3;
		end
		tb_save_LH = 8'h33;
		tb_save_GH = 12'h333;
		tb_save_ras_index = 3'h3;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h3;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 4: AR * 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i * 4;
		end
		tb_save_LH = 8'h44;
		tb_save_GH = 12'h444;
		tb_save_ras_index = 3'h4;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h4;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 5: AR + 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 5;
		end
		tb_save_LH = 8'h55;
		tb_save_GH = 12'h555;
		tb_save_ras_index = 3'h5;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h5;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 6: AR * 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i * 6;
		end
		tb_save_LH = 8'h66;
		tb_save_GH = 12'h666;
		tb_save_ras_index = 3'h6;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h6;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "save 7: AR + 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 7;
		end
		tb_save_LH = 8'h77;
		tb_save_GH = 12'h777;
		tb_save_ras_index = 3'h7;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h7;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "fail save 8: AR * 8";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i * 8;
		end
		tb_save_LH = 8'h88;
		tb_save_GH = 12'h888;
		tb_save_ras_index = 3'h8;
	    // map table restore
		tb_map_table_restore_index = 0;
	    // branch info restore
		tb_branch_info_restore_index = 0;
	    // checkpoint clear
		tb_clear_valid = 1'b0;
		tb_clear_index = 0;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b0;
		expected_save_index = 3'h0;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i;
		end
	    // branch info restore
		expected_branch_info_restore_LH = 8'h000;
		expected_branch_info_restore_GH = 12'h000;
		expected_branch_info_restore_ras_index = 3'h0;
	    // checkpoint clear
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // restore + save chain:
        test_case = "restore + save chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "restore 1: AR + 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b0;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 7;
		end
		tb_save_LH = 8'h77;
		tb_save_GH = 12'h777;
		tb_save_ras_index = 3'h7;
	    // map table restore
		tb_map_table_restore_index = 1;
	    // branch info restore
		tb_branch_info_restore_index = 1;
	    // checkpoint clear
		tb_clear_valid = 1'b1;
		tb_clear_index = 4;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b0;
		expected_save_index = 3'h0;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i + 1;
		end
		expected_branch_info_restore_LH = 8'h11;
		expected_branch_info_restore_GH = 12'h111;
		expected_branch_info_restore_ras_index = 3'h1;
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "restore 4: AR * 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b0;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 7;
		end
		tb_save_LH = 8'h77;
		tb_save_GH = 12'h777;
		tb_save_ras_index = 3'h7;
	    // map table restore
		tb_map_table_restore_index = 4;
	    // branch info restore
		tb_branch_info_restore_index = 4;
	    // checkpoint clear
		tb_clear_valid = 1'b1;
		tb_clear_index = 1;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h0;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i * 4;
		end
		expected_branch_info_restore_LH = 8'h44;
		expected_branch_info_restore_GH = 12'h444;
		expected_branch_info_restore_ras_index = 3'h4;
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "restore 4: AR * 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b0;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 7;
		end
		tb_save_LH = 8'h77;
		tb_save_GH = 12'h777;
		tb_save_ras_index = 3'h7;
	    // map table restore
		tb_map_table_restore_index = 2;
	    // branch info restore
		tb_branch_info_restore_index = 2;
	    // checkpoint clear
		tb_clear_valid = 1'b1;
		tb_clear_index = 2;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h0;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i * 2;
		end
		expected_branch_info_restore_LH = 8'h22;
		expected_branch_info_restore_GH = 12'h222;
		expected_branch_info_restore_ras_index = 3'h2;
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "restore 5: AR + 5; resave 1: AR + 11";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i + 11;
		end
		tb_save_LH = 8'hbb;
		tb_save_GH = 12'hbbb;
		tb_save_ras_index = 3'hb;
	    // map table restore
		tb_map_table_restore_index = 5;
	    // branch info restore
		tb_branch_info_restore_index = 7;
	    // checkpoint clear
		tb_clear_valid = 1'b1;
		tb_clear_index = 5;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h1;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i + 5;
		end
		expected_branch_info_restore_LH = 8'h77;
		expected_branch_info_restore_GH = 12'h777;
		expected_branch_info_restore_ras_index = 3'h7;
	    // advertized threshold
		expected_above_threshold = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "restore 7: AR + 7; resave 2: AR * 22";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // checkpoint save
		tb_save_valid = 1'b1;
		for (int i = 0; i < 32; i++) begin
			tb_save_map_table[i] = i * 12;
		end
		tb_save_LH = 8'hcc;
		tb_save_GH = 12'hccc;
		tb_save_ras_index = 3'hc;
	    // map table restore
		tb_map_table_restore_index = 7;
	    // branch info restore
		tb_branch_info_restore_index = 5;
	    // checkpoint clear
		tb_clear_valid = 1'b1;
		tb_clear_index = 7;
	    // advertized threshold

		@(negedge CLK);

		// outputs:

	    // checkpoint save
		expected_save_ready = 1'b1;
		expected_save_index = 3'h2;
	    // map table restore
		for (int i = 0; i < 32; i++) begin
			expected_map_table_restore_map_table[i] = i + 7;
		end
		expected_branch_info_restore_LH = 8'h55;
		expected_branch_info_restore_GH = 12'h555;
		expected_branch_info_restore_ras_index = 3'h5;
	    // advertized threshold
		expected_above_threshold = 1'b0;

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