/*
    Filename: fpu_top_tb.sv
    Author: zlagpacan
    Description: Testbench for fpu_top module. 
    Spec: LOROF/spec/design/fpu_top.md
*/

`timescale 1ns/100ps

`include "fpp.vh"
`include "corep.vh"

module fpu_top_tb #(
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

    // Input instruction and transaction metadata
	logic tb_in_valid;
	logic DUT_in_ready, expected_in_ready;
	logic [4:0] tb_in_opcode5;
	logic [4:0] tb_in_funct5_op;
	logic tb_in_fmt;
	logic [4:0] tb_in_rs2;
	logic [2:0] tb_in_funct3;
	corep::pr_t tb_in_dest_pr;
	corep::rob_idx_t tb_in_rob_idx;
	logic [2:0] tb_in_fcsr_rm;

    // Decoded operands, with single precision values already NaN-box checked
	fpp::double_t tb_in_A_d;
	fpp::single_t tb_in_A_s_boxed;
	fpp::double_t tb_in_B_d;
	fpp::single_t tb_in_B_s_boxed;
	fpp::double_t tb_in_C_d;
	fpp::single_t tb_in_C_s_boxed;

    // Unified result interface
	logic DUT_out_valid, expected_out_valid;
	logic tb_out_ready;
	corep::pr_t DUT_out_dest_pr, expected_out_dest_pr;
	corep::rob_idx_t DUT_out_rob_idx, expected_out_rob_idx;
	fpp::double_t DUT_out_result_d, expected_out_result_d;
	fpp::fpu_except_t DUT_out_except, expected_out_except;

    // ----------------------------------------------------------------
    // DUT instantiation:

	fpu_top #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // Input instruction and transaction metadata
		.in_valid(tb_in_valid),
		.in_ready(DUT_in_ready),
		.in_opcode5(tb_in_opcode5),
		.in_funct5_op(tb_in_funct5_op),
		.in_fmt(tb_in_fmt),
		.in_rs2(tb_in_rs2),
		.in_funct3(tb_in_funct3),
		.in_dest_pr(tb_in_dest_pr),
		.in_rob_idx(tb_in_rob_idx),
		.in_fcsr_rm(tb_in_fcsr_rm),

	    // Decoded operands, with single precision values already NaN-box checked
		.in_A_d(tb_in_A_d),
		.in_A_s_boxed(tb_in_A_s_boxed),
		.in_B_d(tb_in_B_d),
		.in_B_s_boxed(tb_in_B_s_boxed),
		.in_C_d(tb_in_C_d),
		.in_C_s_boxed(tb_in_C_s_boxed),

	    // Unified result interface
		.out_valid(DUT_out_valid),
		.out_ready(tb_out_ready),
		.out_dest_pr(DUT_out_dest_pr),
		.out_rob_idx(DUT_out_rob_idx),
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
        integer cycle;

        // ------------------------------------------------------------
        // reset:
        test_case = "reset";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        sub_test_case = "assert reset";
        $display("\t- sub_test: %s", sub_test_case);
        nRST = 1'b0;
        tb_in_valid = 1'b0;
        tb_in_opcode5 = 5'b10100;
        tb_in_funct5_op = 5'b00000;
        tb_in_fmt = 1'b0;
        tb_in_rs2 = 5'b00000;
        tb_in_funct3 = fpp::RM_RNE;
        tb_in_dest_pr = '0;
        tb_in_rob_idx = '0;
        tb_in_fcsr_rm = fpp::RM_RNE;
        tb_in_A_d = '0;
        tb_in_A_s_boxed = '0;
        tb_in_B_d = '0;
        tb_in_B_s_boxed = '0;
        tb_in_C_d = '0;
        tb_in_C_s_boxed = '0;
        tb_out_ready = 1'b1;
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;

        @(posedge CLK); #(PERIOD/10);
        check_outputs();

        // ------------------------------------------------------------
        // arithmetic instruction:
        test_case = "arithmetic operation";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(negedge CLK);
        sub_test_case = "FADD.S 1.0 + 2.0";
        $display("\t- sub_test: %s", sub_test_case);
        nRST = 1'b1;
        tb_in_valid = 1'b1;
        tb_in_opcode5 = 5'b10100;
        tb_in_funct5_op = 5'b00000;
        tb_in_fmt = 1'b0;
        tb_in_rs2 = 5'b00000;
        tb_in_funct3 = fpp::RM_RNE;
        tb_in_dest_pr = 7'h11;
        tb_in_rob_idx = 7'h21;
        tb_in_A_s_boxed = 32'h3f800000;
        tb_in_B_s_boxed = 32'h40000000;
        tb_out_ready = 1'b1;

        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();

        @(negedge CLK); tb_in_valid = 1'b0;
        for (cycle = 0; cycle < 8; cycle = cycle + 1) begin
            @(posedge CLK); #(PERIOD/10);
            expected_in_ready = 1'b1;
            expected_out_valid = 1'b0;
            expected_out_dest_pr = '0;
            expected_out_rob_idx = '0;
            expected_out_result_d = '0;
            expected_out_except = '0;
            check_outputs();
        end
        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b1;
        expected_out_dest_pr = 7'h11;
        expected_out_rob_idx = 7'h21;
        expected_out_result_d = 64'hffffffff40400000;
        expected_out_except = '0;
        check_outputs();
        @(posedge CLK); #(PERIOD/10);
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();

        // ------------------------------------------------------------
        // conversion instruction:
        test_case = "conversion operation";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(negedge CLK);
        sub_test_case = "FCVT.D.S 1.5";
        $display("\t- sub_test: %s", sub_test_case);
        tb_in_valid = 1'b1;
        tb_in_opcode5 = 5'b10100;
        tb_in_funct5_op = 5'b01000;
        tb_in_fmt = 1'b1;
        tb_in_rs2 = 5'b00001;
        tb_in_funct3 = fpp::RM_RNE;
        tb_in_dest_pr = 7'h12;
        tb_in_rob_idx = 7'h22;
        tb_in_A_s_boxed = 32'h3fc00000;

        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();

        @(negedge CLK); tb_in_valid = 1'b0;
        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();
        @(posedge CLK); #(PERIOD/10);
        expected_out_valid = 1'b1;
        expected_out_dest_pr = 7'h12;
        expected_out_rob_idx = 7'h22;
        expected_out_result_d = 64'h3ff8000000000000;
        expected_out_except = '0;
        check_outputs();
        @(posedge CLK); #(PERIOD/10);
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();

        // ------------------------------------------------------------
        // fused instruction and output backpressure:
        test_case = "fused operation and backpressure";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(negedge CLK);
        sub_test_case = "FMADD.S 2.0 * 3.0 + 4.0 held at output";
        $display("\t- sub_test: %s", sub_test_case);
        tb_in_valid = 1'b1;
        tb_in_opcode5 = 5'b10000;
        tb_in_funct5_op = 5'b00000;
        tb_in_fmt = 1'b0;
        tb_in_rs2 = 5'b00000;
        tb_in_funct3 = fpp::RM_RNE;
        tb_in_dest_pr = 7'h13;
        tb_in_rob_idx = 7'h23;
        tb_in_A_s_boxed = 32'h40000000;
        tb_in_B_s_boxed = 32'h40400000;
        tb_in_C_s_boxed = 32'h40800000;
        tb_out_ready = 1'b0;

        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();

        @(negedge CLK); tb_in_valid = 1'b0;
        for (cycle = 0; cycle < 12; cycle = cycle + 1) begin
            @(posedge CLK); #(PERIOD/10);
            expected_in_ready = 1'b1;
            expected_out_valid = 1'b0;
            expected_out_dest_pr = '0;
            expected_out_rob_idx = '0;
            expected_out_result_d = '0;
            expected_out_except = '0;
            check_outputs();
        end
        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b1;
        expected_out_dest_pr = 7'h13;
        expected_out_rob_idx = 7'h23;
        expected_out_result_d = 64'hffffffff41200000;
        expected_out_except = '0;
        check_outputs();

        sub_test_case = "FMADD.S output remains stable while out_ready is low";
        $display("\t- sub_test: %s", sub_test_case);
        repeat (3) begin
            @(posedge CLK); #(PERIOD/10);
            expected_in_ready = 1'b1;
            expected_out_valid = 1'b1;
            expected_out_dest_pr = 7'h13;
            expected_out_rob_idx = 7'h23;
            expected_out_result_d = 64'hffffffff41200000;
            expected_out_except = '0;
            check_outputs();
        end

        @(negedge CLK); tb_out_ready = 1'b1;
        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();

        // ------------------------------------------------------------
        // easy instruction:
        test_case = "easy operation";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(negedge CLK);
        sub_test_case = "FSGNJ.S copies negative sign";
        $display("\t- sub_test: %s", sub_test_case);
        tb_in_valid = 1'b1;
        tb_in_opcode5 = 5'b10100;
        tb_in_funct5_op = 5'b00100;
        tb_in_fmt = 1'b0;
        tb_in_rs2 = 5'b00000;
        tb_in_funct3 = 3'b000;
        tb_in_dest_pr = 7'h14;
        tb_in_rob_idx = 7'h24;
        tb_in_A_d = 64'hffffffff3f800000;
        tb_in_A_s_boxed = 32'h3f800000;
        tb_in_B_d = 64'hffffffffc0000000;
        tb_in_B_s_boxed = 32'hc0000000;
        tb_out_ready = 1'b1;

        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b1;
        expected_out_dest_pr = 7'h14;
        expected_out_rob_idx = 7'h24;
        expected_out_result_d = 64'hffffffffbf800000;
        expected_out_except = '0;
        check_outputs();

        @(negedge CLK); tb_in_valid = 1'b0;
        @(posedge CLK); #(PERIOD/10);
        expected_in_ready = 1'b1;
        expected_out_valid = 1'b0;
        expected_out_dest_pr = '0;
        expected_out_rob_idx = '0;
        expected_out_result_d = '0;
        expected_out_except = '0;
        check_outputs();

        // ------------------------------------------------------------
        // finish:
        @(posedge CLK); #(PERIOD/10);
        test_case = "finish";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        $display();
        if (num_errors) $display("FAIL: %0d tests fail", num_errors);
        else $display("SUCCESS: all tests pass");
        $display();
        $finish();
    end

endmodule
