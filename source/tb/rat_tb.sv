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

		if (expected_instr_yield_by_way !== DUT_instr_yield_by_way) begin
			$display("TB ERROR: expected_instr_yield_by_way (%0d'h%h) != DUT_instr_yield_by_way (%0d'h%h)",
				$bits(expected_instr_yield_by_way), expected_instr_yield_by_way,
				$bits(DUT_instr_yield_by_way), DUT_instr_yield_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_save_irat !== DUT_save_irat) begin
			$display("TB ERROR: expected_save_irat (%0d'h%h) != DUT_save_irat (%0d'h%h)",
				$bits(expected_save_irat), expected_save_irat,
				$bits(DUT_save_irat), DUT_save_irat);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_save_frat !== DUT_save_frat) begin
			$display("TB ERROR: expected_save_frat (%0d'h%h) != DUT_save_frat (%0d'h%h)",
				$bits(expected_save_frat), expected_save_frat,
				$bits(DUT_save_frat), DUT_save_frat);
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
	    // rat reads
		tb_A_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_B_ar6_by_way = {
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00
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
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00
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
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00
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
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00
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
	    // rat reads
		tb_A_ar6_by_way = {
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00,
            1'b0, 5'h00
        };
		tb_B_ar6_by_way = {
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00
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
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00,
            1'b0, 6'h00
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