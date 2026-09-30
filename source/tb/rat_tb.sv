/*
    Filename: rat_tb.sv
    Author: zlagpacan
    Description: Testbench for rat module. 
    Spec: LOROF/spec/design/rat.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module rat_tb #(
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

    // rat reads
	corep::ar6_t [3:0] tb_A_ar6_by_way;
	corep::pr_t [3:0] DUT_A_pr_by_way, expected_A_pr_by_way;

	corep::ar6_t [3:0] tb_B_ar6_by_way;
	corep::pr_t [3:0] DUT_B_pr_by_way, expected_B_pr_by_way;

	corep::ar5_t [3:0] tb_C_ar5_by_way;
	corep::pr_t [3:0] DUT_C_pr_by_way, expected_C_pr_by_way;

    // rat writes
	logic [3:0] tb_dest_write_valid_by_way;
	corep::ar6_t [3:0] tb_dest_ar6_by_way;
	corep::pr_t [3:0] DUT_dest_old_pr_by_way, expected_dest_old_pr_by_way;
	corep::pr_t [3:0] tb_dest_new_pr_by_way;

    // instr yields
	logic [3:0] tb_instr_valid_by_way;
	logic [3:0] tb_instr_has_freg_by_way;
	logic [3:0] DUT_instr_yield_by_way, expected_instr_yield_by_way;

    // decode_unit control
	logic [3:0] tb_perform_rename_by_way;

    // checkpoint save
	corep::rat_t DUT_save_irat, expected_save_irat;
	corep::rat_t DUT_save_frat, expected_save_frat;

    // checkpoint restore
	logic tb_restore_valid;
	corep::rat_t tb_restore_irat;
	corep::rat_t tb_restore_frat;

    // ----------------------------------------------------------------
    // DUT instantiation:

	rat #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // rat reads
		.A_ar6_by_way(tb_A_ar6_by_way),
		.A_pr_by_way(DUT_A_pr_by_way),

		.B_ar6_by_way(tb_B_ar6_by_way),
		.B_pr_by_way(DUT_B_pr_by_way),

		.C_ar5_by_way(tb_C_ar5_by_way),
		.C_pr_by_way(DUT_C_pr_by_way),

	    // rat writes
		.dest_write_valid_by_way(tb_dest_write_valid_by_way),
		.dest_ar6_by_way(tb_dest_ar6_by_way),
		.dest_old_pr_by_way(DUT_dest_old_pr_by_way),
		.dest_new_pr_by_way(tb_dest_new_pr_by_way),

	    // instr yields
		.instr_valid_by_way(tb_instr_valid_by_way),
		.instr_has_freg_by_way(tb_instr_has_freg_by_way),
		.instr_yield_by_way(DUT_instr_yield_by_way),

	    // decode_unit control
		.perform_rename_by_way(tb_perform_rename_by_way),

	    // checkpoint save
		.save_irat(DUT_save_irat),
		.save_frat(DUT_save_frat),

	    // checkpoint restore
		.restore_valid(tb_restore_valid),
		.restore_irat(tb_restore_irat),
		.restore_frat(tb_restore_frat)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
        for (int way = 3; way >= 0; way--) begin
            if (expected_A_pr_by_way[way] !== DUT_A_pr_by_way[way]) begin
                $display("TB ERROR: expected_A_pr_by_way[%0h] (%0d'h%h) != DUT_A_pr_by_way[%0h] (%0d'h%h)",
                    way, $bits(expected_A_pr_by_way[way]), expected_A_pr_by_way[way],
                    way, $bits(DUT_A_pr_by_way[way]), DUT_A_pr_by_way[way]);
                num_errors++;
                tb_error = 1'b1;
            end
        end

        for (int way = 3; way >= 0; way--) begin
            if (expected_B_pr_by_way[way] !== DUT_B_pr_by_way[way]) begin
                $display("TB ERROR: expected_B_pr_by_way[%0h] (%0d'h%h) != DUT_B_pr_by_way[%0h] (%0d'h%h)",
                    way, $bits(expected_B_pr_by_way[way]), expected_B_pr_by_way[way],
                    way, $bits(DUT_B_pr_by_way[way]), DUT_B_pr_by_way[way]);
                num_errors++;
                tb_error = 1'b1;
            end
        end

        for (int way = 3; way >= 0; way--) begin
            if (expected_C_pr_by_way[way] !== DUT_C_pr_by_way[way]) begin
                $display("TB ERROR: expected_C_pr_by_way[%0h] (%0d'h%h) != DUT_C_pr_by_way[%0h] (%0d'h%h)",
                    way, $bits(expected_C_pr_by_way[way]), expected_C_pr_by_way[way],
                    way, $bits(DUT_C_pr_by_way[way]), DUT_C_pr_by_way[way]);
                num_errors++;
                tb_error = 1'b1;
            end
        end

        for (int way = 3; way >= 0; way--) begin
            if (expected_dest_old_pr_by_way[way] !== DUT_dest_old_pr_by_way[way]) begin
                $display("TB ERROR: expected_dest_old_pr_by_way[%0h] (%0d'h%h) != DUT_dest_old_pr_by_way[%0h] (%0d'h%h)",
                    way, $bits(expected_dest_old_pr_by_way[way]), expected_dest_old_pr_by_way[way],
                    way, $bits(DUT_dest_old_pr_by_way[way]), DUT_dest_old_pr_by_way[way]);
                num_errors++;
                tb_error = 1'b1;
            end
        end

		if (expected_instr_yield_by_way !== DUT_instr_yield_by_way) begin
			$display("TB ERROR: expected_instr_yield_by_way (%0d'h%h) != DUT_instr_yield_by_way (%0d'h%h)",
				$bits(expected_instr_yield_by_way), expected_instr_yield_by_way,
				$bits(DUT_instr_yield_by_way), DUT_instr_yield_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

        for (int way = 0; way < 32; way++) begin
            if (expected_save_irat[way] !== DUT_save_irat[way]) begin
                $display("TB ERROR: expected_save_irat[%0h] (%0d'h%h) != DUT_save_irat[%0h] (%0d'h%h)",
                    way, $bits(expected_save_irat[way]), expected_save_irat[way],
                    way, $bits(DUT_save_irat[way]), DUT_save_irat[way]);
                num_errors++;
                tb_error = 1'b1;
            end
        end

        for (int way = 0; way < 32; way++) begin
            if (expected_save_frat[way] !== DUT_save_frat[way]) begin
                $display("TB ERROR: expected_save_frat[%0h] (%0d'h%h) != DUT_save_frat[%0h] (%0d'h%h)",
                    way, $bits(expected_save_frat[way]), expected_save_frat[way],
                    way, $bits(DUT_save_frat[way]), DUT_save_frat[way]);
                num_errors++;
                tb_error = 1'b1;
            end
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
	    // rat reads
		tb_A_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_B_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // rat writes
		tb_dest_write_valid_by_way = 4'b0000;
		tb_dest_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_dest_new_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // instr yields
		tb_instr_valid_by_way = 4'b0000;
		tb_instr_has_freg_by_way = 4'b0000;
	    // decode_unit control
		tb_perform_rename_by_way = 4'b0000;
	    // checkpoint save
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
		tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // rat reads
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
	    // rat writes
		expected_dest_old_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // instr yields
		expected_instr_yield_by_way = 4'b1111;
	    // decode_unit control
	    // checkpoint save
		expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
        };
		expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
	    // checkpoint restore

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // rat reads
		tb_A_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_B_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // rat writes
		tb_dest_write_valid_by_way = 4'b0000;
		tb_dest_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_dest_new_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // instr yields
		tb_instr_valid_by_way = 4'b0000;
		tb_instr_has_freg_by_way = 4'b0000;
	    // decode_unit control
		tb_perform_rename_by_way = 4'b0000;
	    // checkpoint save
	    // checkpoint restore
		tb_restore_valid = 1'b0;
		tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
		tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // rat reads
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
	    // rat writes
		expected_dest_old_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // instr yields
		expected_instr_yield_by_way = 4'b1111;
	    // decode_unit control
	    // checkpoint save
		expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
        };
		expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
	    // checkpoint restore

		check_outputs();

        // ------------------------------------------------------------
        // readout:
        test_case = "readout";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 32; i += 4) begin
            int i_plus_1 = i + 1;
            int i_plus_2 = i + 2;
            int i_plus_3 = i + 3;

            int i_plus_35 = i[4:0] + 35;

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("irat readout cycle 0x%0h", i / 4);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // rat reads
            tb_A_ar6_by_way = {
                i_plus_3[5:0],
                i_plus_2[5:0],
                i_plus_1[5:0],
                i[5:0]
            };
            tb_B_ar6_by_way = {
                i_plus_3[5:0],
                i_plus_2[5:0],
                i_plus_1[5:0],
                i[5:0]
            };
            tb_C_ar5_by_way = {
                i_plus_3[4:0],
                i_plus_2[4:0],
                i_plus_1[4:0],
                i[4:0]
            };
            // rat writes
            tb_dest_write_valid_by_way = 4'b0000;
            tb_dest_ar6_by_way = {
                i_plus_3[5:0],
                i_plus_2[5:0],
                i_plus_1[5:0],
                i[5:0]
            };
            tb_dest_new_pr_by_way = {
                7'h00,
                7'h00,
                7'h00,
                7'h00
            };
            // instr yields
            tb_instr_valid_by_way = 4'b0000;
            tb_instr_has_freg_by_way = 4'b0000;
            // decode_unit control
            tb_perform_rename_by_way = 4'b0000;
            // checkpoint save
            // checkpoint restore
            tb_restore_valid = 1'b0;
            tb_restore_irat = {
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
            };
            tb_restore_frat = {
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
            };

            @(negedge CLK);

            // outputs:

            // rat reads
            expected_A_pr_by_way = {
                i_plus_3[6:0],
                i_plus_2[6:0],
                i_plus_1[6:0],
                i[6:0]
            };
            expected_B_pr_by_way = {
                i_plus_3[6:0],
                i_plus_2[6:0],
                i_plus_1[6:0],
                i[6:0]
            };
            expected_C_pr_by_way = {
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0]
            };
            // rat writes
            expected_dest_old_pr_by_way = {
                i_plus_3[6:0],
                i_plus_2[6:0],
                i_plus_1[6:0],
                i[6:0]
            };
            // instr yields
            expected_instr_yield_by_way = 4'b1111;
            // decode_unit control
            // checkpoint save
            expected_save_irat = {
                7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
                7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
                7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
                7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
            };
            expected_save_frat = {
                7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
                7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
                7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
                7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
            };
            // checkpoint restore

            check_outputs();
        end

        for (int i = 0; i < 32; i += 4) begin
            int i_plus_1 = i + 1;
            int i_plus_2 = i + 2;
            int i_plus_3 = i + 3;

            int i_plus_35 = i[4:0] + 35;

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("frat readout cycle 0x%0h", i / 4);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // rat reads
            tb_A_ar6_by_way = {
                i_plus_3[5:0] + 6'h20,
                i_plus_2[5:0] + 6'h20,
                i_plus_1[5:0] + 6'h20,
                i[5:0] + 6'h20
            };
            tb_B_ar6_by_way = {
                i_plus_3[5:0] + 6'h20,
                i_plus_2[5:0] + 6'h20,
                i_plus_1[5:0] + 6'h20,
                i[5:0] + 6'h20
            };
            tb_C_ar5_by_way = {
                i_plus_3[4:0],
                i_plus_2[4:0],
                i_plus_1[4:0],
                i[4:0]
            };
            // rat writes
            tb_dest_write_valid_by_way = 4'b0000;
            tb_dest_ar6_by_way = {
                i_plus_3[5:0] + 6'h20,
                i_plus_2[5:0] + 6'h20,
                i_plus_1[5:0] + 6'h20,
                i[5:0] + 6'h20
            };
            tb_dest_new_pr_by_way = {
                7'h00,
                7'h00,
                7'h00,
                7'h00
            };
            // instr yields
            tb_instr_valid_by_way = 4'b0000;
            tb_instr_has_freg_by_way = 4'b0000;
            // decode_unit control
            tb_perform_rename_by_way = 4'b0000;
            // checkpoint save
            // checkpoint restore
            tb_restore_valid = 1'b0;
            tb_restore_irat = {
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
            };
            tb_restore_frat = {
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
                7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
            };

            @(negedge CLK);

            // outputs:

            // rat reads
            expected_A_pr_by_way = {
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0]
            };
            expected_B_pr_by_way = {
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0]
            };
            expected_C_pr_by_way = {
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0]
            };
            // rat writes
            expected_dest_old_pr_by_way = {
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0],
                i_plus_35[6:0]
            };
            // instr yields
            expected_instr_yield_by_way = 4'b1111;
            // decode_unit control
            // checkpoint save
            expected_save_irat = {
                7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
                7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
                7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
                7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
            };
            expected_save_frat = {
                7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
                7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
                7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
                7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
            };
            // checkpoint restore

            check_outputs();
        end

        // ------------------------------------------------------------
        // irat writes:
        test_case = "irat writes";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "irat writes cycle 0";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h03,
            1'b0, 5'h02,
            1'b0, 5'h01,
            1'b0, 5'h00
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h02,
            1'b0, 5'h01,
            1'b0, 5'h01,
            1'b0, 5'h02
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h03,
            1'b0, 5'h02,
            1'b0, 5'h01,
            1'b0, 5'h00
        };
        tb_dest_new_pr_by_way = {
            7'h43,
            7'h42,
            7'h41,
            7'h40
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b0000;
        // decode_unit control
        tb_perform_rename_by_way = 4'b1111;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h03,
            7'h02,
            7'h01,
            7'h00
        };
        expected_B_pr_by_way = {
            7'h42,
            7'h41,
            7'h01,
            7'h02
        };
        expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h03,
            7'h02,
            7'h01,
            7'h00
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "irat writes cycle 1";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h04,
            1'b0, 5'h04,
            1'b0, 5'h04,
            1'b0, 5'h04
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h04,
            1'b0, 5'h04,
            1'b0, 5'h04,
            1'b0, 5'h04
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h04,
            1'b0, 5'h04,
            1'b0, 5'h04,
            1'b0, 5'h04
        };
        tb_dest_new_pr_by_way = {
            7'h44,
            7'h54,
            7'h64,
            7'h74
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b0000;
        // decode_unit control
        tb_perform_rename_by_way = 4'b1111;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h54,
            7'h64,
            7'h74,
            7'h04
        };
        expected_B_pr_by_way = {
            7'h54,
            7'h64,
            7'h74,
            7'h04
        };
        expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h54,
            7'h64,
            7'h74,
            7'h04
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "irat writes cycle 2";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h05,
            1'b0, 5'h05,
            1'b0, 5'h05,
            1'b0, 5'h05
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h05,
            1'b0, 5'h05,
            1'b0, 5'h05,
            1'b0, 5'h05
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b0111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h05,
            1'b0, 5'h05,
            1'b0, 5'h05,
            1'b0, 5'h05
        };
        tb_dest_new_pr_by_way = {
            7'h75,
            7'h45,
            7'h75,
            7'h55
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1101;
        tb_instr_has_freg_by_way = 4'b0000;
        // decode_unit control
        tb_perform_rename_by_way = 4'b1111;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h45,
            7'h55,
            7'h55,
            7'h05
        };
        expected_B_pr_by_way = {
            7'h45,
            7'h55,
            7'h55,
            7'h05
        };
        expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h45,
            7'h55,
            7'h55,
            7'h05
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h44, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "irat writes cycle 3";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h06,
            1'b0, 5'h06,
            1'b0, 5'h06,
            1'b0, 5'h06
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h06,
            1'b0, 5'h06,
            1'b0, 5'h06,
            1'b0, 5'h06
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h06,
            1'b0, 5'h06,
            1'b0, 5'h06,
            1'b0, 5'h06
        };
        tb_dest_new_pr_by_way = {
            7'h76,
            7'h66,
            7'h46,
            7'h56
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b0000;
        // decode_unit control
        tb_perform_rename_by_way = 4'b0011;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h66,
            7'h46,
            7'h56,
            7'h06
        };
        expected_B_pr_by_way = {
            7'h66,
            7'h46,
            7'h56,
            7'h06
        };
        expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h66,
            7'h46,
            7'h56,
            7'h06
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h45, 7'h44, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        // checkpoint restore

        check_outputs();

        // ------------------------------------------------------------
        // frat writes:
        test_case = "frat writes";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "frat writes cycle 0";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b1, 5'h00,
            1'b0, 5'h02,
            1'b1, 5'h00,
            1'b0, 5'h00
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h03,
            1'b1, 5'h00,
            1'b0, 5'h01,
            1'b1, 5'h00
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h07,
            1'b1, 5'h00,
            1'b1, 5'h00,
            1'b1, 5'h00
        };
        tb_dest_new_pr_by_way = {
            7'h47,
            7'h50,
            7'h60,
            7'h70
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b0111;
        // decode_unit control
        tb_perform_rename_by_way = 4'b0001;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h50,
            7'h42,
            7'h70,
            7'h40
        };
        expected_B_pr_by_way = {
            7'h43,
            7'h60,
            7'h41,
            7'h20
        };
        expected_C_pr_by_way = {
            7'h20,
            7'h20,
            7'h20,
            7'h20
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h07,
            7'h60,
            7'h70,
            7'h20
        };
        // instr yields
        expected_instr_yield_by_way = 4'b0001;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h46, 7'h45, 7'h44, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "frat writes cycle 1";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b1, 5'h00,
            1'b0, 5'h02,
            1'b1, 5'h00,
            1'b0, 5'h00
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h03,
            1'b1, 5'h00,
            1'b0, 5'h01,
            1'b1, 5'h00
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h07,
            1'b1, 5'h00,
            1'b1, 5'h00,
            1'b1, 5'h00
        };
        tb_dest_new_pr_by_way = {
            7'h47,
            7'h50,
            7'h60,
            7'h70
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1110;
        tb_instr_has_freg_by_way = 4'b0111;
        // decode_unit control
        tb_perform_rename_by_way = 4'b0010;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h50,
            7'h42,
            7'h70,
            7'h40
        };
        expected_B_pr_by_way = {
            7'h43,
            7'h60,
            7'h41,
            7'h21
        };
        expected_C_pr_by_way = {
            7'h70,
            7'h70,
            7'h70,
            7'h70
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h07,
            7'h60,
            7'h70,
            7'h70
        };
        // instr yields
        expected_instr_yield_by_way = 4'b0011;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h46, 7'h45, 7'h44, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h70
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "frat writes cycle 2";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b1, 5'h00,
            1'b0, 5'h02,
            1'b1, 5'h00,
            1'b0, 5'h00
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h03,
            1'b1, 5'h00,
            1'b0, 5'h01,
            1'b1, 5'h00
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h07,
            1'b1, 5'h00,
            1'b1, 5'h00,
            1'b1, 5'h00
        };
        tb_dest_new_pr_by_way = {
            7'h47,
            7'h50,
            7'h60,
            7'h70
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1100;
        tb_instr_has_freg_by_way = 4'b0111;
        // decode_unit control
        tb_perform_rename_by_way = 4'b1100;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h50,
            7'h42,
            7'h22,
            7'h40
        };
        expected_B_pr_by_way = {
            7'h43,
            7'h60,
            7'h41,
            7'h60
        };
        expected_C_pr_by_way = {
            7'h60,
            7'h60,
            7'h60,
            7'h60
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h07,
            7'h60,
            7'h60,
            7'h60
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h46, 7'h45, 7'h44, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h60
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "frat writes cycle 3";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h08,
            1'b0, 5'h08,
            1'b1, 5'h00,
            1'b0, 5'h08
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h08,
            1'b0, 5'h08,
            1'b1, 5'h01,
            1'b0, 5'h08
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h02,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1111;
        tb_dest_ar6_by_way = {
            1'b0, 5'h08,
            1'b0, 5'h08,
            1'b1, 5'h03,
            1'b0, 5'h08
        };
        tb_dest_new_pr_by_way = {
            7'h48,
            7'h58,
            7'h63,
            7'h68
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b0010;
        // decode_unit control
        tb_perform_rename_by_way = 4'b1111;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h58,
            7'h68,
            7'h50,
            7'h08
        };
        expected_B_pr_by_way = {
            7'h58,
            7'h68,
            7'h21,
            7'h08
        };
        expected_C_pr_by_way = {
            7'h22,
            7'h22,
            7'h22,
            7'h22
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h58,
            7'h68,
            7'h23,
            7'h08
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h47, 7'h46, 7'h45, 7'h44, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h50
        };
        // checkpoint restore

        check_outputs();

        // ------------------------------------------------------------
        // restore:
        test_case = "restore";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "restore valid";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h09,
            1'b1, 5'h00,
            1'b0, 5'h09,
            1'b0, 5'h09
        };
        tb_B_ar6_by_way = {
            1'b1, 5'h01,
            1'b0, 5'h09,
            1'b0, 5'h09,
            1'b0, 5'h09
        };
        tb_C_ar5_by_way = {
            5'h1d,
            5'h01,
            5'h1e,
            5'h1f
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b1101;
        tb_dest_ar6_by_way = {
            1'b0, 5'h09,
            1'b0, 5'h09,
            1'b0, 5'h09,
            1'b0, 5'h09
        };
        tb_dest_new_pr_by_way = {
            7'h49,
            7'h59,
            7'h69,
            7'h79
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b1100;
        // decode_unit control
        tb_perform_rename_by_way = 4'b0111;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b1;
        tb_restore_irat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        tb_restore_frat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h59,
            7'h50,
            7'h79,
            7'h09
        };
        expected_B_pr_by_way = {
            7'h29,
            7'h79,
            7'h79,
            7'h09
        };
        expected_C_pr_by_way = {
            7'h21,
            7'h21,
            7'h21,
            7'h21
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h59,
            7'h79,
            7'h79,
            7'h09
        };
        // instr yields
        expected_instr_yield_by_way = 4'b0111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h48,
            7'h47, 7'h46, 7'h45, 7'h44, 7'h43, 7'h42, 7'h41, 7'h40
        };
        expected_save_frat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h63, 7'h22, 7'h21, 7'h50
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "restore readout";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h03,
            1'b0, 5'h02,
            1'b0, 5'h01,
            1'b0, 5'h00
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h13,
            1'b0, 5'h12,
            1'b0, 5'h11,
            1'b0, 5'h10
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b0000;
        tb_dest_ar6_by_way = {
            1'b0, 5'h1B,
            1'b0, 5'h1A,
            1'b0, 5'h19,
            1'b0, 5'h18
        };
        tb_dest_new_pr_by_way = {
            7'h40,
            7'h40,
            7'h40,
            7'h40
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b0000;
        // decode_unit control
        tb_perform_rename_by_way = 4'b1111;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h23,
            7'h22,
            7'h21,
            7'h20
        };
        expected_B_pr_by_way = {
            7'h33,
            7'h32,
            7'h31,
            7'h30
        };
        expected_C_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h3B,
            7'h3A,
            7'h39,
            7'h38
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        expected_save_frat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
        };
        // checkpoint restore

        check_outputs();

        @(posedge CLK); #(PERIOD/10);

        // inputs
        sub_test_case = "restore readout again";
        $display("\t- sub_test: %s", sub_test_case);

        // reset
        nRST = 1'b1;
        // rat reads
        tb_A_ar6_by_way = {
            1'b0, 5'h03,
            1'b0, 5'h02,
            1'b0, 5'h01,
            1'b0, 5'h00
        };
        tb_B_ar6_by_way = {
            1'b0, 5'h13,
            1'b0, 5'h12,
            1'b0, 5'h11,
            1'b0, 5'h10
        };
        tb_C_ar5_by_way = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
        // rat writes
        tb_dest_write_valid_by_way = 4'b0000;
        tb_dest_ar6_by_way = {
            1'b0, 5'h1B,
            1'b0, 5'h1A,
            1'b0, 5'h19,
            1'b0, 5'h18
        };
        tb_dest_new_pr_by_way = {
            7'h40,
            7'h40,
            7'h40,
            7'h40
        };
        // instr yields
        tb_instr_valid_by_way = 4'b1111;
        tb_instr_has_freg_by_way = 4'b0000;
        // decode_unit control
        tb_perform_rename_by_way = 4'b1111;
        // checkpoint save
        // checkpoint restore
        tb_restore_valid = 1'b0;
        tb_restore_irat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };
        tb_restore_frat = {
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00,
            7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00, 7'h00
        };

        @(negedge CLK);

        // outputs:

        // rat reads
        expected_A_pr_by_way = {
            7'h23,
            7'h22,
            7'h21,
            7'h20
        };
        expected_B_pr_by_way = {
            7'h33,
            7'h32,
            7'h31,
            7'h30
        };
        expected_C_pr_by_way = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
        // rat writes
        expected_dest_old_pr_by_way = {
            7'h3B,
            7'h3A,
            7'h39,
            7'h38
        };
        // instr yields
        expected_instr_yield_by_way = 4'b1111;
        // decode_unit control
        // checkpoint save
        expected_save_irat = {
            7'h3f, 7'h3e, 7'h3d, 7'h3c, 7'h3b, 7'h3a, 7'h39, 7'h38,
            7'h37, 7'h36, 7'h35, 7'h34, 7'h33, 7'h32, 7'h31, 7'h30,
            7'h2f, 7'h2e, 7'h2d, 7'h2c, 7'h2b, 7'h2a, 7'h29, 7'h28,
            7'h27, 7'h26, 7'h25, 7'h24, 7'h23, 7'h22, 7'h21, 7'h20
        };
        expected_save_frat = {
            7'h1f, 7'h1e, 7'h1d, 7'h1c, 7'h1b, 7'h1a, 7'h19, 7'h18,
            7'h17, 7'h16, 7'h15, 7'h14, 7'h13, 7'h12, 7'h11, 7'h10,
            7'h0f, 7'h0e, 7'h0d, 7'h0c, 7'h0b, 7'h0a, 7'h09, 7'h08,
            7'h07, 7'h06, 7'h05, 7'h04, 7'h03, 7'h02, 7'h01, 7'h00
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