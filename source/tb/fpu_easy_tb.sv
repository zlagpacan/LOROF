/*
    Filename: fpu_easy_tb.sv
    Author: zlagpacan
    Description: Testbench for fpu_easy module. 
    Spec: LOROF/spec/design/fpu_easy.md
*/

`timescale 1ns/100ps

`include "fpp.vh"

module fpu_easy_tb #(
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
    // fully comb

    // instr components
	logic [6:0] tb_funct7;
	logic [2:0] tb_funct3;

    // operands
	fpp::double_t tb_A_d;
	fpp::double_t tb_B_d;

	fpp::single_t tb_A_s_boxed;
	fpp::single_t tb_B_s_boxed;

    // outputs
	fpp::double_t DUT_result_d, expected_result_d;
	fpp::fpu_except_t DUT_except, expected_except;

    // ----------------------------------------------------------------
    // DUT instantiation:

	fpu_easy #(
	) DUT (
	    // fully comb

	    // instr components
		.funct7(tb_funct7),
		.funct3(tb_funct3),

	    // operands
		.A_d(tb_A_d),
		.B_d(tb_B_d),

		.A_s_boxed(tb_A_s_boxed),
		.B_s_boxed(tb_B_s_boxed),

	    // outputs
		.result_d(DUT_result_d),
		.except(DUT_except)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_result_d !== DUT_result_d) begin
			$display("TB ERROR: expected_result_d (%0d'h%h) != DUT_result_d (%0d'h%h)",
				$bits(expected_result_d), expected_result_d,
				$bits(DUT_result_d), DUT_result_d);
            $display("\texpected_result_d.sign (1'b%01b) | DUT_result_d.sign (1'b%01b)",
                expected_result_d.sign, DUT_result_d.sign);
            $display("\texpected_result_d.exp (11'h%03h) | DUT_result_d.exp (11'h%03h)",
                expected_result_d.exp, DUT_result_d.exp);
            $display("\texpected_result_d.mant (52'h%013h) | DUT_result_d.mant (52'h%013h)",
                expected_result_d.mant, DUT_result_d.mant);
            $display("\texpected_result_d.mant.upper (20'h%05h) | DUT_result_d.mant.upper (20'h%05h)",
                expected_result_d.mant.upper, DUT_result_d.mant.upper);
            $display("\texpected_result_d.mant.single.sign (1'b%01b) | DUT_result_d.mant.single.sign (1'b%01b)",
                expected_result_d.mant.single.sign, DUT_result_d.mant.single.sign);
            $display("\texpected_result_d.mant.single.exp (8'h%02h) | DUT_result_d.mant.single.exp (8'h%02h)",
                expected_result_d.mant.single.exp, DUT_result_d.mant.single.exp);
            $display("\texpected_result_d.mant.single.mant (23'h%06h) | DUT_result_d.mant.single.mant (23'h%06h)",
                expected_result_d.mant.single.mant, DUT_result_d.mant.single.mant);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_except !== DUT_except) begin
			$display("TB ERROR: expected_except (%0d'h%h) != DUT_except (%0d'h%h)",
				$bits(expected_except), expected_except,
				$bits(DUT_except), DUT_except);
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
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0000000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0; // double cNaN
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0000000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0; // double cNaN
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FSGNJ.S:
        test_case = "FSGNJ.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.S pos pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b0;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.S pos neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.S neg pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b0;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.S neg neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FSGNJN.S:
        test_case = "FSGNJN.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.S pos pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b0;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.S pos neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.S neg pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b0;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.S neg neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FSGNJX.S:
        test_case = "FSGNJX.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.S pos pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b0;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.S pos neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.S neg pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b0;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.S neg neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h12;
        tb_A_d.mant.single.mant = 23'h345678;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'h9a;
        tb_B_d.mant.single.mant = 23'hbcdef0;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h12;
		expected_result_d.mant.single.mant = 23'h345678;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMIN.S:
        test_case = "FMIN.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.S small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S qNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S big pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S sNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S big pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000010;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S big sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000100;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h001000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.S big sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h100000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h010000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMAX.S:
        test_case = "FMAX.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.S small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S qNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S big pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S sNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S big pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000010;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S big sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000100;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h001000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.S big sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010100;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h100000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h010000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'hFF;
		expected_result_d.mant.single.mant = 23'h400000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMV.X.W:
        test_case = "FMV.X.W";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.X.W big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'haa;
        tb_A_d.mant.single.mant = 23'hbbbbbb;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.X.W small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h11;
        tb_A_d.mant.single.mant = 23'h222222;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FEQ.S:
        test_case = "FEQ.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S big neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S -0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S +0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S sNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S sNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S qNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S qNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.S small neg qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FLT.S:
        test_case = "FLT.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S big neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S -0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S +0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S sNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S sNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S qNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S qNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.S small neg qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FLE.S:
        test_case = "FLE.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S big neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S -0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S +0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S sNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S sNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S qNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S qNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.S small neg qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FCLASS.S:
        test_case = "FCLASS.S";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000002;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000002;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S subnormal neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000004;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000008;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000010;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S subnormal pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000020;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000040;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000040;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000080;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000100;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.S qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110000;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'hFF;
        tb_A_d.mant.single.mant = 23'h7FFFFF;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000200;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMV.W.X:
        test_case = "FMV.W.X";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.W.X big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1111000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant.upper = 20'h00000;
        tb_A_d.mant.single.sign = 1'b0;
        tb_A_d.mant.single.exp = 8'haa;
        tb_A_d.mant.single.mant = 23'hbbbbbb;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'haa;
		expected_result_d.mant.single.mant = 23'hbbbbbb;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.W.X small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1111000;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant.upper = 20'hFFFFF;
        tb_A_d.mant.single.sign = 1'b1;
        tb_A_d.mant.single.exp = 8'h11;
        tb_A_d.mant.single.mant = 23'h222222;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant.upper = 20'hFFFFF;
		expected_result_d.mant.single.sign = 1'b1;
		expected_result_d.mant.single.exp = 8'h11;
		expected_result_d.mant.single.mant = 23'h222222;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FSGNJ.D:
        test_case = "FSGNJ.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.D pos pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.D pos neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.D neg pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJ.D neg neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FSGNJN.D:
        test_case = "FSGNJN.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.D pos pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.D pos neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.D neg pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJN.D neg neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FSGNJX.D:
        test_case = "FSGNJX.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.D pos pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.D pos neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.D neg pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FSGNJX.D neg neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h00_0000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h00_0000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMIN.D:
        test_case = "FMIN.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMIN.D small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D qNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D big pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D sNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h4_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D big pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000010;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0010;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000100;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0100;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h001000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMIN.D big sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_1000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0001_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h100000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h010000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMAX.D:
        test_case = "FMAX.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMAX.D small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D qNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D big pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D sNaN big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h4_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D big pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000010;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D big sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0010;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000100;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0100;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h001000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		// inputs
		sub_test_case = "FMAX.D big sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b0010101;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_1000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0001_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h100000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h010000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h7FF;
		expected_result_d.mant = 52'h8_0000_0000_0000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMV.X.D:
        test_case = "FMV.X.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.X.D big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'haaa;
		expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.X.D small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
		expected_result_d.exp = 11'h111;
		expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FEQ.D:
        test_case = "FEQ.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D big neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D -0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D +0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0010;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0100;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_1000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0001_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0010_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0100_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_1000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D sNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D sNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D qNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D qNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FEQ.D small neg qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b010;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FLT.D:
        test_case = "FLT.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D big neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D -0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D +0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0010;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0100;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_1000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0001_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0010_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0100_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_1000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D sNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D sNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D qNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D qNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLT.D small neg qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FLE.D:
        test_case = "FLE.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big pos small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big pos big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big neg small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big neg big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big pos small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big pos big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big neg small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D big neg big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'haaa;
        tb_B_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'haa;
        tb_B_s_boxed.mant = 23'hbbbbbb;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +inf -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +inf +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +inf small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +inf small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +0.0 -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +0.0 +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D -0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +0.0 small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D +0.0 small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h000;
        tb_B_d.mant = 52'h0_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D sNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0010;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D sNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0100;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_1000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D qNaN sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0001_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0010_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D qNaN qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0100_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_1000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D sNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D sNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h0_0000_0000_0001;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h000001;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D qNaN small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D qNaN small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7FF;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h111;
        tb_B_d.mant = 52'h2_2323_2323_2323;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b1;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small pos qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FLE.D small neg qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1010001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b0;
        tb_B_d.exp = 11'h7FF;
        tb_B_d.mant = 52'h8_0000_0000_0000;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'hFF;
        tb_B_s_boxed.mant = 23'h400000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000000;

		expected_except.NV = 1'b1;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FCLASS.D:
        test_case = "FCLASS.D";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D -inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000001;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D big neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000002;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000002;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D subnormal neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000004;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D -0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b1;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000008;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D +0.0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000010;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D subnormal pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h000;
        tb_A_d.mant = 52'h0_0000_0000_0001;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000020;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D small pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h11;
        tb_A_s_boxed.mant = 23'h222222;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000040;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'haa;
        tb_A_s_boxed.mant = 23'hbbbbbb;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000040;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D +inf";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant = 52'h0_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000080;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D sNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant = 52'h4_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h000001;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000100;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FCLASS.D qNaN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1110001;
		tb_funct3 = 3'b001;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h7ff;
        tb_A_d.mant = 52'h8_0000_0000_0000;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'hFF;
        tb_A_s_boxed.mant = 23'h400000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h11;
        tb_B_s_boxed.mant = 23'h222222;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
		expected_result_d.exp = 11'h000;
		expected_result_d.mant.upper = 20'h00000;
		expected_result_d.mant.single.sign = 1'b0;
		expected_result_d.mant.single.exp = 8'h00;
		expected_result_d.mant.single.mant = 23'h000200;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

        // ------------------------------------------------------------
        // FMV.D.X:
        test_case = "FMV.D.X";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.D.X big pos";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1111001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b0;
        tb_A_d.exp = 11'haaa;
        tb_A_d.mant = 52'hb_bcbc_bcbc_bcbc;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b0;
        expected_result_d.exp = 11'haaa;
        expected_result_d.mant = 52'hb_bcbc_bcbc_bcbc;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "FMV.D.X small neg";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // fully comb
	    // instr components
		tb_funct7 = 7'b1111001;
		tb_funct3 = 3'b000;
	    // operands

		tb_A_d.sign = 1'b1;
        tb_A_d.exp = 11'h111;
        tb_A_d.mant = 52'h2_2323_2323_2323;

		tb_B_d.sign = 1'b1;
        tb_B_d.exp = 11'h7ff;
        tb_B_d.mant.upper = 20'hFFFFF;
        tb_B_d.mant.single.sign = 1'b1;
        tb_B_d.mant.single.exp = 8'hFF;
        tb_B_d.mant.single.mant = 23'h7FFFFF;

		tb_A_s_boxed.sign = 1'b0;
        tb_A_s_boxed.exp = 8'h00;
        tb_A_s_boxed.mant = 23'h000000;

		tb_B_s_boxed.sign = 1'b0;
        tb_B_s_boxed.exp = 8'h00;
        tb_B_s_boxed.mant = 23'h000000;

	    // outputs

		@(negedge CLK);

		// outputs:

	    // fully comb
	    // instr components
	    // operands
	    // outputs

		expected_result_d.sign = 1'b1;
        expected_result_d.exp = 11'h111;
        expected_result_d.mant = 52'h2_2323_2323_2323;

		expected_except.NV = 1'b0;
		expected_except.DZ = 1'b0;
		expected_except.OF = 1'b0;
		expected_except.UF = 1'b0;
		expected_except.NX = 1'b0;

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