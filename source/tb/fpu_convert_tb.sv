/*
    Filename: fpu_convert_tb.sv
    Author: zlagpacan
    Description: Testbench for fpu_convert module. 
    Spec: LOROF/spec/design/fpu_convert.md
*/

`timescale 1ns/100ps

`include "fpp.vh"
`include "corep.vh"

module fpu_convert_tb #(
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

    // input control
	logic tb_in_valid;
	corep::pr_t tb_in_dest_pr;
	corep::rob_idx_t tb_in_rob_idx;

	logic DUT_in_ready, expected_in_ready;

    // instr components
	logic [6:0] tb_in_funct7;
	logic [4:0] tb_in_funct5;
	logic [2:0] tb_in_instr_rm;
	logic [2:0] tb_in_fcsr_rm;

    // fp input
	fpp::double_t tb_in_A_d;
	fpp::single_t tb_in_A_s_boxed;

    // output control
	logic DUT_out_valid, expected_out_valid;
	corep::pr_t DUT_out_dest_pr, expected_out_dest_pr;
	corep::rob_idx_t DUT_out_rob_idx, expected_out_rob_idx;

	logic tb_out_ready;

    // fp output
	fpp::double_t DUT_out_result_d, expected_out_result_d;
	fpp::fpu_except_t DUT_out_except, expected_out_except;

    // ----------------------------------------------------------------
    // DUT instantiation:

	fpu_convert #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // input control
		.in_valid(tb_in_valid),
		.in_dest_pr(tb_in_dest_pr),
		.in_rob_idx(tb_in_rob_idx),

		.in_ready(DUT_in_ready),

	    // instr components
		.in_funct7(tb_in_funct7),
		.in_funct5(tb_in_funct5),
		.in_instr_rm(tb_in_instr_rm),
		.in_fcsr_rm(tb_in_fcsr_rm),

	    // fp input
		.in_A_d(tb_in_A_d),
		.in_A_s_boxed(tb_in_A_s_boxed),

	    // output control
		.out_valid(DUT_out_valid),
		.out_dest_pr(DUT_out_dest_pr),
		.out_rob_idx(DUT_out_rob_idx),

		.out_ready(tb_out_ready),

	    // fp output
		.out_result_d(DUT_out_result_d),
		.out_except(DUT_out_except)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_in_ready !== DUT_in_ready) begin
			$display("TB ERROR: expected_in_ready (%0d'h%h) != DUT_in_ready (%0d'h%h)",
				$bits(expected_in_ready), expected_in_ready,
				$bits(DUT_in_ready), DUT_in_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_out_valid !== DUT_out_valid) begin
			$display("TB ERROR: expected_out_valid (%0d'h%h) != DUT_out_valid (%0d'h%h)",
				$bits(expected_out_valid), expected_out_valid,
				$bits(DUT_out_valid), DUT_out_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_out_dest_pr !== DUT_out_dest_pr) begin
			$display("TB ERROR: expected_out_dest_pr (%0d'h%h) != DUT_out_dest_pr (%0d'h%h)",
				$bits(expected_out_dest_pr), expected_out_dest_pr,
				$bits(DUT_out_dest_pr), DUT_out_dest_pr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_out_rob_idx !== DUT_out_rob_idx) begin
			$display("TB ERROR: expected_out_rob_idx (%0d'h%h) != DUT_out_rob_idx (%0d'h%h)",
				$bits(expected_out_rob_idx), expected_out_rob_idx,
				$bits(DUT_out_rob_idx), DUT_out_rob_idx);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_out_result_d !== DUT_out_result_d) begin
			$display("TB ERROR: expected_out_result_d (%0d'h%h) != DUT_out_result_d (%0d'h%h)",
				$bits(expected_out_result_d), expected_out_result_d,
				$bits(DUT_out_result_d), DUT_out_result_d);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_out_except !== DUT_out_except) begin
			$display("TB ERROR: expected_out_except (%0d'h%h) != DUT_out_except (%0d'h%h)",
				$bits(expected_out_except), expected_out_except,
				$bits(DUT_out_except), DUT_out_except);
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
	    // input control
		tb_in_valid = 1'b0;
		tb_in_dest_pr = 7'h00;
		tb_in_rob_idx = 7'h00;
	    // instr components
		tb_in_funct7 = 7'b0000000;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_DYN;
		tb_in_fcsr_rm = fpp::RM_RNE;
	    // fp input
		tb_in_A_d = 64'h0;
		tb_in_A_s_boxed = 32'h0;
	    // output control
		tb_out_ready = 1'b1;
	    // fp output

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // input control
		expected_in_ready = 1'b1;
	    // instr components
	    // fp input
	    // output control
		expected_out_valid = 1'b0;
		expected_out_dest_pr = 7'h00;
		expected_out_rob_idx = 7'h00;
	    // fp output
		expected_out_result_d = 64'h0;
		expected_out_except.NV = 1'b0;
		expected_out_except.DZ = 1'b0;
		expected_out_except.OF = 1'b0;
		expected_out_except.UF = 1'b0;
		expected_out_except.NX = 1'b0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input control
		tb_in_valid = 1'b0;
		tb_in_dest_pr = 7'h00;
		tb_in_rob_idx = 7'h00;
	    // instr components
		tb_in_funct7 = 7'b0000000;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_DYN;
		tb_in_fcsr_rm = fpp::RM_RNE;
	    // fp input
		tb_in_A_d = 64'h0;
		tb_in_A_s_boxed = 32'h0;
	    // output control
		tb_out_ready = 1'b1;
	    // fp output

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // input control
		expected_in_ready = 1'b1;
	    // instr components
	    // fp input
	    // output control
		expected_out_valid = 1'b0;
		expected_out_dest_pr = 7'h00;
		expected_out_rob_idx = 7'h00;
	    // fp output
		expected_out_result_d = 64'h0;
		expected_out_except.NV = 1'b0;
		expected_out_except.DZ = 1'b0;
		expected_out_except.OF = 1'b0;
		expected_out_except.UF = 1'b0;
		expected_out_except.NX = 1'b0;

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
	    // input control
		tb_in_valid = 1'b0;
		tb_in_dest_pr = 7'h00;
		tb_in_rob_idx = 7'h00;
	    // instr components
		tb_in_funct7 = 7'b0000000;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_DYN;
		tb_in_fcsr_rm = fpp::RM_RNE;
	    // fp input
		tb_in_A_d = 64'h0;
		tb_in_A_s_boxed = 32'h0;
	    // output control
		tb_out_ready = 1'b1;
	    // fp output

		@(negedge CLK);

		// outputs:

	    // input control
		expected_in_ready = 1'b1;
	    // instr components
	    // fp input
	    // output control
		expected_out_valid = 1'b0;
		expected_out_dest_pr = 7'h00;
		expected_out_rob_idx = 7'h00;
	    // fp output
		expected_out_result_d = 64'h0;
		expected_out_except.NV = 1'b0;
		expected_out_except.DZ = 1'b0;
		expected_out_except.OF = 1'b0;
		expected_out_except.UF = 1'b0;
		expected_out_except.NX = 1'b0;

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