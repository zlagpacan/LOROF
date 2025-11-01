/*
    Filename: map_table_tb.sv
    Author: zlagpacan
    Description: Testbench for map_table module. 
    Spec: LOROF/spec/design/map_table.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module map_table_tb #(
	parameter MAP_TABLE_READ_PORT_COUNT = 12,
	parameter MAP_TABLE_WRITE_PORT_COUNT = 4
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


    // read ports
	logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_AR_COUNT-1:0] tb_read_AR_by_port;
	logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_PR_COUNT-1:0] DUT_read_PR_by_port, expected_read_PR_by_port;

    // write ports
	logic [MAP_TABLE_WRITE_PORT_COUNT-1:0] tb_write_valid_by_port;
	logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_AR_COUNT-1:0] tb_write_AR_by_port;
	logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_PR_COUNT-1:0] tb_write_PR_by_port;

    // checkpoint save
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] DUT_save_map_table, expected_save_map_table;

    // checkpoint restore
	logic tb_restore_valid;
	logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_restore_map_table;

    // ----------------------------------------------------------------
    // DUT instantiation:

	map_table #(
		.MAP_TABLE_READ_PORT_COUNT(12),
		.MAP_TABLE_WRITE_PORT_COUNT(4)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // 12x read ports
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
			for (int i = 0; i < AR_COUNT; i++) begin
				if (expected_save_map_table[i] !== DUT_save_map_table[i]) begin
					$display("\t\texpected_save_map_table[%0h] = %h != DUT_save_map_tabe[%0h] = %h", 
						i, expected_save_map_table[i], i, DUT_save_map_table[i]);
				end
			end
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
	    // 12x read ports
		tb_read_AR_by_port = {
			5'hb,
			5'ha,
			5'h9,
			5'h8,
			5'h7,
			5'h6,
			5'h5,
			5'h4,
			5'h3,
			5'h2,
			5'h1,
			5'h0
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

	    // 12x read ports
		expected_read_PR_by_port = {
			7'hb,
			7'ha,
			7'h9,
			7'h8,
			7'h7,
			7'h6,
			7'h5,
			7'h4,
			7'h3,
			7'h2,
			7'h1,
			7'h0
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
	    // 12x read ports
		tb_read_AR_by_port = {
			5'hb,
			5'ha,
			5'h9,
			5'h8,
			5'h7,
			5'h6,
			5'h5,
			5'h4,
			5'h3,
			5'h2,
			5'h1,
			5'h0
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

	    // 12x read ports
		expected_read_PR_by_port = {
			7'hb,
			7'ha,
			7'h9,
			7'h8,
			7'h7,
			7'h6,
			7'h5,
			7'h4,
			7'h3,
			7'h2,
			7'h1,
			7'h0
		};
	    // 4x write ports
	    // checkpoint save
		for (int j = 0; j < 32; j++) begin
			expected_save_map_table[j] = j;
		end
	    // checkpoint restore

		check_outputs();

        // ------------------------------------------------------------
        // read reset vals:
        test_case = "read reset vals";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 32; i+=12) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("read %0d:%0d", i, i+7);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// 12x read ports
			tb_read_AR_by_port = {
				{i + 11}[4:0],
				{i + 10}[4:0],
				{i + 9}[4:0],
				{i + 8}[4:0],
				{i + 7}[4:0],
				{i + 6}[4:0],
				{i + 5}[4:0],
				{i + 4}[4:0],
				{i + 3}[4:0],
				{i + 2}[4:0],
				{i + 1}[4:0],
				{i + 0}[4:0]
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

			// 12x read ports
			expected_read_PR_by_port = {
				{(i + 11) % 32}[6:0],
				{(i + 10) % 32}[6:0],
				{(i + 9) % 32}[6:0],
				{(i + 8) % 32}[6:0],
				{i + 7}[6:0],
				{i + 6}[6:0],
				{i + 5}[6:0],
				{i + 4}[6:0],
				{i + 3}[6:0],
				{i + 2}[6:0],
				{i + 1}[6:0],
				{i + 0}[6:0]
			};
			// 4x write ports
			// checkpoint save
			for (int j = 0; j < 32; j++) begin
				expected_save_map_table[j[4:0]] = j[6:0];
			end
			// checkpoint restore

			check_outputs();
		end

        // ------------------------------------------------------------
        // set all x+32:
        test_case = "set all x+32";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 32; i+=4) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("write %0d:%0d", i, i+3);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// 12x read ports
			tb_read_AR_by_port = {
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0,
				5'h0
			};
			// 4x write ports
			tb_write_valid_by_port = 4'b1111;
			tb_write_AR_by_port = {
				{i + 3}[4:0],
				{i + 2}[4:0],
				{i + 1}[4:0],
				{i + 0}[4:0]
			};
			tb_write_PR_by_port = {
				{i + 32 + 3}[6:0],
				{i + 32 + 2}[6:0],
				{i + 32 + 1}[6:0],
				{i + 32 + 0}[6:0]
			};
			// checkpoint save
			// checkpoint restore
			tb_restore_valid = 1'b0;
			tb_restore_map_table = '0;

			@(negedge CLK);

			// outputs:

			// 12x read ports
			if (i > 0) begin
				expected_read_PR_by_port = {
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20,
					7'h20
				};
			end
			else begin
				expected_read_PR_by_port = {
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0,
					7'h0
				};
			end
			// 4x write ports
			// checkpoint save
			for (int j = 0; j < 32; j++) begin
				if (j < i) begin
					expected_save_map_table[j[4:0]] = {j + 32}[6:0];
				end
				else begin
					expected_save_map_table[j[4:0]] = {j}[6:0];
				end
			end
			// checkpoint restore

			check_outputs();
		end

        // ------------------------------------------------------------
        // read x+32:
        test_case = "read x+32";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 32; i+=12) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("read %0d:%0d", i, i+7);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// 12x read ports
			tb_read_AR_by_port = {
				{i + 11}[4:0],
				{i + 10}[4:0],
				{i + 9}[4:0],
				{i + 8}[4:0],
				{i + 7}[4:0],
				{i + 6}[4:0],
				{i + 5}[4:0],
				{i + 4}[4:0],
				{i + 3}[4:0],
				{i + 2}[4:0],
				{i + 1}[4:0],
				{i + 0}[4:0]
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

			// 12x read ports
			expected_read_PR_by_port = {
				{(i + 11) % 32 + 32}[6:0],
				{(i + 10) % 32 + 32}[6:0],
				{(i + 9) % 32 + 32}[6:0],
				{(i + 8) % 32 + 32}[6:0],
				{i + 32 + 7}[6:0],
				{i + 32 + 6}[6:0],
				{i + 32 + 5}[6:0],
				{i + 32 + 4}[6:0],
				{i + 32 + 3}[6:0],
				{i + 32 + 2}[6:0],
				{i + 32 + 1}[6:0],
				{i + 32 + 0}[6:0]
			};
			// 4x write ports
			// checkpoint save
			for (int j = 0; j < 32; j++) begin
				expected_save_map_table[j[4:0]] = {j + 32}[6:0];
			end
			// checkpoint restore

			check_outputs();
		end

        // ------------------------------------------------------------
        // restore double table:
        test_case = "restore double table";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "restore double table";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// 12x read ports
		tb_read_AR_by_port = {
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0,
			5'h0
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
		tb_restore_valid = 1'b1;
		for (int j = 0; j < 32; j++) begin
			tb_restore_map_table[j] = {2 * j}[6:0];
		end

		@(negedge CLK);

		// outputs:

		// 12x read ports
		expected_read_PR_by_port = {
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20,
			7'h20
		};
		// 4x write ports
		// checkpoint save
		for (int j = 0; j < 32; j++) begin
			expected_save_map_table[j[4:0]] = {j + 32}[6:0];
		end
		// checkpoint restore

		check_outputs();

        // ------------------------------------------------------------
        // read double table:
        test_case = "read double table";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 32; i+=12) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("read %0d:%0d", i, i+7);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// 12x read ports
			tb_read_AR_by_port = {
				{i + 7}[4:0],
				{i + 6}[4:0],
				{i + 5}[4:0],
				{i + 4}[4:0],
				{i + 3}[4:0],
				{i + 2}[4:0],
				{i + 1}[4:0],
				{i + 0}[4:0]
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

			// 12x read ports
			expected_read_PR_by_port = {
				{(i + 7) * 2}[6:0],
				{(i + 6) * 2}[6:0],
				{(i + 5) * 2}[6:0],
				{(i + 4) * 2}[6:0],
				{(i + 3) * 2}[6:0],
				{(i + 2) * 2}[6:0],
				{(i + 1) * 2}[6:0],
				{(i + 0) * 2}[6:0]
			};
			// 4x write ports
			// checkpoint save
			for (int j = 0; j < 32; j++) begin
				expected_save_map_table[j[4:0]] = {j * 2}[6:0];
			end
			// checkpoint restore

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