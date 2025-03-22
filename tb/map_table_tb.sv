/*
    Filename: map_table_tb.sv
    Author: zlagpacan
    Description: Testbench for map_table module. 
    Spec: LOROF/spec/design/map_table.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module map_table_tb ();

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


    // 8x read ports
	logic [7:0][LOG_AR_COUNT-1:0] tb_read_AR_by_port;
	logic [7:0][LOG_PR_COUNT-1:0] DUT_read_PR_by_port, expected_read_PR_by_port;

    // 4x write ports
	logic [3:0] tb_write_valid_by_port;
	logic [3:0] tb_write_AR_by_port;
	logic [3:0][LOG_PR_COUNT-1:0] tb_write_PR_by_port;

    // checkpoint save
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] DUT_save_map_table, expected_save_map_table;

    // checkpoint restore
	logic tb_restore_valid;
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_restore_map_table;

    // ----------------------------------------------------------------
    // DUT instantiation:

	map_table DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // 8x read ports
		.read_AR_by_port(tb_read_AR_by_port),
		.read_PR_by_port(DUT_read_PR_by_port),

	    // 4x write ports
		.write_valid_by_port(tb_write_valid_by_port),
		.write_AR_by_port(tb_write_AR_by_port),
		.write_PR_by_port(tb_write_PR_by_port),

	    // checkpoint save
		.save_map_table(DUT_save_map_table),

	    // checkpoint restore
		.restore_valid(tb_restore_valid),
		.restore_map_table(tb_restore_map_table)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_PR_by_port !== DUT_read_PR_by_port) begin
			$display("TB ERROR: expected_read_PR_by_port (%h) != DUT_read_PR_by_port (%h)",
				expected_read_PR_by_port, DUT_read_PR_by_port);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_save_map_table !== DUT_save_map_table) begin
			$display("TB ERROR: expected_save_map_table (%h) != DUT_save_map_table (%h)",
				expected_save_map_table, DUT_save_map_table);
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
	    // 8x read ports
		tb_read_AR_by_port = {
			5'h0,
			5'h1,
			5'h2,
			5'h3,
			5'h4,
			5'h5,
			5'h6,
			5'h7
		};
	    // 4x write ports
		tb_write_valid_by_port = 4'b0000;
		tb_write_AR_by_port = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
		tb_write_PR_by_port = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};
	    // checkpoint save
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_map_table = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // 8x read ports
		expected_read_PR_by_port = {
			7'h0,
			7'h1,
			7'h2,
			7'h3,
			7'h4,
			7'h5,
			7'h6,
			7'h7
		};
	    // 4x write ports
	    // checkpoint save
		for (int i = 0; i < 32; i++) begin
			expected_save_map_table[i] = i;
		end
	    // checkpoint restore

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // 8x read ports
		tb_read_AR_by_port = {
			5'h0,
			5'h1,
			5'h2,
			5'h3,
			5'h4,
			5'h5,
			5'h6,
			5'h7
		};
	    // 4x write ports
		tb_write_valid_by_port = 4'b0000;
		tb_write_AR_by_port = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
		tb_write_PR_by_port = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};
	    // checkpoint save
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_map_table = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // 8x read ports
		expected_read_PR_by_port = {
			7'h0,
			7'h1,
			7'h2,
			7'h3,
			7'h4,
			7'h5,
			7'h6,
			7'h7
		};
	    // 4x write ports
	    // checkpoint save
		for (int i = 0; i < 32; i++) begin
			expected_save_map_table[i] = i;
		end
	    // checkpoint restore

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
	    // 8x read ports
		tb_read_AR_by_port = {
			5'h0,
			5'h1,
			5'h2,
			5'h3,
			5'h4,
			5'h5,
			5'h6,
			5'h7
		};
	    // 4x write ports
		tb_write_valid_by_port = 4'b0000;
		tb_write_AR_by_port = {
			5'h0,
			5'h0,
			5'h0,
			5'h0
		};
		tb_write_PR_by_port = {
			7'h0,
			7'h0,
			7'h0,
			7'h0
		};
	    // checkpoint save
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_map_table = '0;

		@(negedge CLK);

		// outputs:

	    // 8x read ports
		expected_read_PR_by_port = {
			7'h0,
			7'h1,
			7'h2,
			7'h3,
			7'h4,
			7'h5,
			7'h6,
			7'h7
		};
	    // 4x write ports
	    // checkpoint save
		for (int i = 0; i < 32; i++) begin
			expected_save_map_table[i] = i;
		end
	    // checkpoint restore

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