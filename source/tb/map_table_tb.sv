/*
    Filename: map_table_tb.sv
    Author: zlagpacan
    Description: Testbench for map_table module. 
    Spec: LOROF/spec/design/map_table.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module map_table_tb #(
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

    // reg reads
	corep::ar6_t [3:0] tb_A_ar6_by_way;
	corep::pr_t [3:0] DUT_A_pr_by_way, expected_A_pr_by_way;

	corep::ar6_t [3:0] tb_B_ar6_by_way;
	corep::pr_t [3:0] DUT_B_pr_by_way, expected_B_pr_by_way;

	corep::ar5_t [3:0] tb_C_far_by_way;
	corep::pr_t [3:0] DUT_C_pr_by_way, expected_C_pr_by_way;

    // reg writes
	logic [3:0] tb_dest_write_valid_by_way;
	corep::ar6_t [3:0] tb_dest_ar6_by_way;
	corep::pr_t [3:0] DUT_dest_old_pr_by_way, expected_dest_old_pr_by_way;
	corep::pr_t [3:0] tb_dest_new_pr_by_way;

    // checkpoint save
	corep::map_table_t DUT_save_map_table, expected_save_map_table;

    // checkpoint restore
	logic tb_restore_valid;
	corep::map_table_t tb_restore_map_table;

    // ----------------------------------------------------------------
    // DUT instantiation:

	map_table #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // reg reads
		.A_ar6_by_way(tb_A_ar6_by_way),
		.A_pr_by_way(DUT_A_pr_by_way),

		.B_ar6_by_way(tb_B_ar6_by_way),
		.B_pr_by_way(DUT_B_pr_by_way),

		.C_far_by_way(tb_C_far_by_way),
		.C_pr_by_way(DUT_C_pr_by_way),

	    // reg writes
		.dest_write_valid_by_way(tb_dest_write_valid_by_way),
		.dest_ar6_by_way(tb_dest_ar6_by_way),
		.dest_old_pr_by_way(DUT_dest_old_pr_by_way),
		.dest_new_pr_by_way(tb_dest_new_pr_by_way),

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
		if (expected_A_pr_by_way !== DUT_A_pr_by_way) begin
			$display("TB ERROR: expected_A_pr_by_way (%0d'h%h) != DUT_A_pr_by_way (%0d'h%h)",
				$bits(expected_A_pr_by_way), expected_A_pr_by_way,
				$bits(DUT_A_pr_by_way), DUT_A_pr_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_pr_by_way !== DUT_B_pr_by_way) begin
			$display("TB ERROR: expected_B_pr_by_way (%0d'h%h) != DUT_B_pr_by_way (%0d'h%h)",
				$bits(expected_B_pr_by_way), expected_B_pr_by_way,
				$bits(DUT_B_pr_by_way), DUT_B_pr_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_C_pr_by_way !== DUT_C_pr_by_way) begin
			$display("TB ERROR: expected_C_pr_by_way (%0d'h%h) != DUT_C_pr_by_way (%0d'h%h)",
				$bits(expected_C_pr_by_way), expected_C_pr_by_way,
				$bits(DUT_C_pr_by_way), DUT_C_pr_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_old_pr_by_way !== DUT_dest_old_pr_by_way) begin
			$display("TB ERROR: expected_dest_old_pr_by_way (%0d'h%h) != DUT_dest_old_pr_by_way (%0d'h%h)",
				$bits(expected_dest_old_pr_by_way), expected_dest_old_pr_by_way,
				$bits(DUT_dest_old_pr_by_way), DUT_dest_old_pr_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_save_map_table !== DUT_save_map_table) begin
			$display("TB ERROR: expected_save_map_table (%0d'h%h) != DUT_save_map_table (%0d'h%h)",
				$bits(expected_save_map_table), expected_save_map_table,
				$bits(DUT_save_map_table), DUT_save_map_table);
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
	    // reg reads
		tb_A_ar6_by_way = {
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00}
        };
		tb_B_ar6_by_way = {
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00}
        };
		tb_C_far_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // reg writes
		tb_dest_write_valid_by_way = 4'b0000;
		tb_dest_ar6_by_way = {
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00}
        };
		tb_dest_new_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // checkpoint save
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_map_table.iar = {
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00
        };
		tb_restore_map_table.far = {
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00
        };

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // reg reads
		expected_A_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
		expected_B_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
		expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
	    // reg writes
		expected_dest_old_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // checkpoint save
		expected_save_map_table.iar = {
            7'h1F, 7'h1E, 7'h1D, 7'h1C,
            7'h1B, 7'h1A, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14,
            7'h13, 7'h12, 7'h11, 7'h10,
            7'h0F, 7'h0E, 7'h0D, 7'h0C,
            7'h0B, 7'h0A, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04,
            7'h03, 7'h02, 7'h01, 7'h00
        };
		expected_save_map_table.far = {
            7'h3F, 7'h3E, 7'h3D, 7'h3C,
            7'h3B, 7'h3A, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34,
            7'h33, 7'h32, 7'h31, 7'h30,
            7'h2F, 7'h2E, 7'h2D, 7'h2C,
            7'h2B, 7'h2A, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24,
            7'h23, 7'h22, 7'h21, 7'h20
        };
	    // checkpoint restore

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg reads
		tb_A_ar6_by_way = {
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00}
        };
		tb_B_ar6_by_way = {
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00}
        };
		tb_C_far_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // reg writes
		tb_dest_write_valid_by_way = 4'b0000;
		tb_dest_ar6_by_way = {
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00},
            {1'b0, 5'h00}
        };
		tb_dest_new_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // checkpoint save
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_map_table.iar = {
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00
        };
		tb_restore_map_table.far = {
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00
        };

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // reg reads
		expected_A_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
		expected_B_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
		expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
	    // reg writes
		expected_dest_old_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // checkpoint save
		expected_save_map_table.iar = {
            7'h1F, 7'h1E, 7'h1D, 7'h1C,
            7'h1B, 7'h1A, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14,
            7'h13, 7'h12, 7'h11, 7'h10,
            7'h0F, 7'h0E, 7'h0D, 7'h0C,
            7'h0B, 7'h0A, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04,
            7'h03, 7'h02, 7'h01, 7'h00
        };
		expected_save_map_table.far = {
            7'h3F, 7'h3E, 7'h3D, 7'h3C,
            7'h3B, 7'h3A, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34,
            7'h33, 7'h32, 7'h31, 7'h30,
            7'h2F, 7'h2E, 7'h2D, 7'h2C,
            7'h2B, 7'h2A, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24,
            7'h23, 7'h22, 7'h21, 7'h20
        };
	    // checkpoint restore

		check_outputs();

        // ------------------------------------------------------------
        // iar readout:
        test_case = "iar readout";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < corep::AR5_COUNT - 8; i += 4) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("cycle %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // reg reads
            tb_A_ar6_by_way = {
                1'b0, corep::ar5_t'(i+3),
                1'b0, corep::ar5_t'(i+2),
                1'b0, corep::ar5_t'(i+1),
                1'b0, corep::ar5_t'(i+0)
            };
            tb_B_ar6_by_way = {
                1'b0, corep::ar5_t'(i+7),
                1'b0, corep::ar5_t'(i+6),
                1'b0, corep::ar5_t'(i+5),
                1'b0, corep::ar5_t'(i+4)
            };
            tb_C_far_by_way = {
                corep::ar5_t'(i+3),
                corep::ar5_t'(i+2),
                corep::ar5_t'(i+1),
                corep::ar5_t'(i+0)
            };
            // reg writes
            tb_dest_write_valid_by_way = 4'b0000;
            tb_dest_ar6_by_way = {
                1'b0, corep::ar5_t'(i+11),
                1'b0, corep::ar5_t'(i+10),
                1'b0, corep::ar5_t'(i+9),
                1'b0, corep::ar5_t'(i+8)
            };
            tb_dest_new_pr_by_way = {
                7'h00,
                7'h00,
                7'h00,
                7'h00
            };
            // checkpoint save
            // checkpoint restore
            tb_restore_valid = 1'b0;
            tb_restore_map_table.iar = {
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00
            };
            tb_restore_map_table.far = {
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00
            };

            @(negedge CLK);

            // outputs:

            // reg reads
            expected_A_pr_by_way = {
                corep::pr_t'(i+3),
                corep::pr_t'(i+2),
                corep::pr_t'(i+1),
                corep::pr_t'(i+0)
            };
            expected_B_pr_by_way = {
                corep::pr_t'(i+7),
                corep::pr_t'(i+6),
                corep::pr_t'(i+5),
                corep::pr_t'(i+4)
            };
            expected_C_pr_by_way = {
                corep::pr_t'(i+35),
                corep::pr_t'(i+34),
                corep::pr_t'(i+33),
                corep::pr_t'(i+32)
            };
            // reg writes
            expected_dest_old_pr_by_way = {
                corep::pr_t'(i+11),
                corep::pr_t'(i+10),
                corep::pr_t'(i+9),
                corep::pr_t'(i+8)
            };
            // checkpoint save
            expected_save_map_table.iar = {
                7'h1F, 7'h1E, 7'h1D, 7'h1C,
                7'h1B, 7'h1A, 7'h19, 7'h18,
                7'h17, 7'h16, 7'h15, 7'h14,
                7'h13, 7'h12, 7'h11, 7'h10,
                7'h0F, 7'h0E, 7'h0D, 7'h0C,
                7'h0B, 7'h0A, 7'h09, 7'h08,
                7'h07, 7'h06, 7'h05, 7'h04,
                7'h03, 7'h02, 7'h01, 7'h00
            };
            expected_save_map_table.far = {
                7'h3F, 7'h3E, 7'h3D, 7'h3C,
                7'h3B, 7'h3A, 7'h39, 7'h38,
                7'h37, 7'h36, 7'h35, 7'h34,
                7'h33, 7'h32, 7'h31, 7'h30,
                7'h2F, 7'h2E, 7'h2D, 7'h2C,
                7'h2B, 7'h2A, 7'h29, 7'h28,
                7'h27, 7'h26, 7'h25, 7'h24,
                7'h23, 7'h22, 7'h21, 7'h20
            };
            // checkpoint restore

            check_outputs();
        end

        // ------------------------------------------------------------
        // far readout:
        test_case = "far readout";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < corep::AR5_COUNT - 12; i += 4) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("cycle %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // reg reads
            tb_A_ar6_by_way = {
                1'b1, corep::ar5_t'(i+3),
                1'b1, corep::ar5_t'(i+2),
                1'b1, corep::ar5_t'(i+1),
                1'b1, corep::ar5_t'(i+0)
            };
            tb_B_ar6_by_way = {
                1'b1, corep::ar5_t'(i+7),
                1'b1, corep::ar5_t'(i+6),
                1'b1, corep::ar5_t'(i+5),
                1'b1, corep::ar5_t'(i+4)
            };
            tb_C_far_by_way = {
                corep::ar5_t'(i+11),
                corep::ar5_t'(i+10),
                corep::ar5_t'(i+9),
                corep::ar5_t'(i+8)
            };
            // reg writes
            tb_dest_write_valid_by_way = 4'b0000;
            tb_dest_ar6_by_way = {
                1'b1, corep::ar5_t'(i+15),
                1'b1, corep::ar5_t'(i+14),
                1'b1, corep::ar5_t'(i+13),
                1'b1, corep::ar5_t'(i+12)
            };
            tb_dest_new_pr_by_way = {
                7'h00,
                7'h00,
                7'h00,
                7'h00
            };
            // checkpoint save
            // checkpoint restore
            tb_restore_valid = 1'b0;
            tb_restore_map_table.iar = {
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00
            };
            tb_restore_map_table.far = {
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00
            };

            @(negedge CLK);

            // outputs:

            // reg reads
            expected_A_pr_by_way = {
                corep::pr_t'(i+35),
                corep::pr_t'(i+34),
                corep::pr_t'(i+33),
                corep::pr_t'(i+32)
            };
            expected_B_pr_by_way = {
                corep::pr_t'(i+39),
                corep::pr_t'(i+38),
                corep::pr_t'(i+37),
                corep::pr_t'(i+36)
            };
            expected_C_pr_by_way = {
                corep::pr_t'(i+43),
                corep::pr_t'(i+42),
                corep::pr_t'(i+41),
                corep::pr_t'(i+40)
            };
            // reg writes
            expected_dest_old_pr_by_way = {
                corep::pr_t'(i+47),
                corep::pr_t'(i+46),
                corep::pr_t'(i+45),
                corep::pr_t'(i+44)
            };
            // checkpoint save
            expected_save_map_table.iar = {
                7'h1F, 7'h1E, 7'h1D, 7'h1C,
                7'h1B, 7'h1A, 7'h19, 7'h18,
                7'h17, 7'h16, 7'h15, 7'h14,
                7'h13, 7'h12, 7'h11, 7'h10,
                7'h0F, 7'h0E, 7'h0D, 7'h0C,
                7'h0B, 7'h0A, 7'h09, 7'h08,
                7'h07, 7'h06, 7'h05, 7'h04,
                7'h03, 7'h02, 7'h01, 7'h00
            };
            expected_save_map_table.far = {
                7'h3F, 7'h3E, 7'h3D, 7'h3C,
                7'h3B, 7'h3A, 7'h39, 7'h38,
                7'h37, 7'h36, 7'h35, 7'h34,
                7'h33, 7'h32, 7'h31, 7'h30,
                7'h2F, 7'h2E, 7'h2D, 7'h2C,
                7'h2B, 7'h2A, 7'h29, 7'h28,
                7'h27, 7'h26, 7'h25, 7'h24,
                7'h23, 7'h22, 7'h21, 7'h20
            };
            // checkpoint restore

            check_outputs();
        end

        // ------------------------------------------------------------
        // dep cases:
        test_case = "dep cases";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "all dest -> A";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // reg reads
        tb_A_ar6_by_way = {
            1'b1, 5'h0D,
            1'b0, 5'h09,
            1'b1, 5'h05,
            1'b0, 5'h01
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
        tb_C_far_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // reg writes
        tb_dest_write_valid_by_way = 4'b1;
        tb_dest_ar6_by_way = {
            1'b1, 5'h0D,
            1'b0, 5'h09,
            1'b1, 5'h05,
            1'b0, 5'h01
        };
        tb_dest_new_pr_by_way = {
            7'hD1,
            7'h90,
            7'h51,
            7'h10
        };
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_map_table.iar = {
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_map_table.far = {
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // reg reads
        expected_A_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
        expected_B_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
        expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
        // reg writes
        expected_dest_old_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
        // checkpoint save
        expected_save_map_table.iar = {
            7'h1F, 7'h1E, 7'h1D, 7'h1C,
            7'h1B, 7'h1A, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14,
            7'h13, 7'h12, 7'h11, 7'h10,
            7'h0F, 7'h0E, 7'h0D, 7'h0C,
            7'h0B, 7'h0A, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04,
            7'h03, 7'h02, 7'h01, 7'h00
        };
        expected_save_map_table.far = {
            7'h3F, 7'h3E, 7'h3D, 7'h3C,
            7'h3B, 7'h3A, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34,
            7'h33, 7'h32, 7'h31, 7'h30,
            7'h2F, 7'h2E, 7'h2D, 7'h2C,
            7'h2B, 7'h2A, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24,
            7'h23, 7'h22, 7'h21, 7'h20
        };
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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule