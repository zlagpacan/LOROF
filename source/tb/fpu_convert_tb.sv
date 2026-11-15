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

	
initial begin
	nRST = 1'b0;
	tb_in_valid = 1'b0;
	tb_in_dest_pr = '0;
	tb_in_rob_idx = '0;
	tb_in_funct7 = '0;
	tb_in_funct5 = '0;
	tb_in_instr_rm = fpp::RM_DYN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = '0;
	tb_in_A_s_boxed = '0;
	tb_out_ready = 1'b1;
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b0;
	expected_out_dest_pr = '0;
	expected_out_rob_idx = '0;
	expected_out_result_d = '0;
	expected_out_except = '0;

	// reset
	test_case = "reset";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	nRST = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	check_outputs();
	nRST = 1'b1;

	// Fill both stages, block the output, and check each stalled cycle.
	test_case = "pipeline backpressure";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(negedge CLK);
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h11;
	tb_in_rob_idx = 7'h21;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h3f800000;
	tb_out_ready = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	@(negedge CLK);
	tb_in_dest_pr = 7'h12;
	tb_in_rob_idx = 7'h22;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h40000000;
	@(posedge CLK); #(PERIOD / 10);
	expected_in_ready = 1'b0;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h11;
	expected_out_rob_idx = 7'h21;
	expected_out_result_d = 64'h3ff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(negedge CLK);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	expected_in_ready = 1'b0;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h11;
	expected_out_rob_idx = 7'h21;
	expected_out_result_d = 64'h3ff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(posedge CLK); #(PERIOD / 10);
	expected_in_ready = 1'b0;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h11;
	expected_out_rob_idx = 7'h21;
	expected_out_result_d = 64'h3ff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(posedge CLK); #(PERIOD / 10);
	expected_in_ready = 1'b0;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h11;
	expected_out_rob_idx = 7'h21;
	expected_out_result_d = 64'h3ff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(negedge CLK);
	tb_out_ready = 1'b1;
	@(posedge CLK); #(PERIOD / 10);
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h12;
	expected_out_rob_idx = 7'h22;
	expected_out_result_d = 64'h4000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	// Two consecutive inputs produce two consecutive output cycles.
	test_case = "pipeline throughput";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(negedge CLK);
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h31;
	tb_in_rob_idx = 7'h41;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h3f800000;
	tb_out_ready = 1'b1;
	@(posedge CLK); #(PERIOD / 10);
	@(negedge CLK);
	tb_in_dest_pr = 7'h32;
	tb_in_rob_idx = 7'h42;
	tb_in_A_s_boxed = 32'h40000000;
	@(posedge CLK); #(PERIOD / 10);
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h31;
	expected_out_rob_idx = 7'h41;
	expected_out_result_d = 64'h3ff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(negedge CLK);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h32;
	expected_out_rob_idx = 7'h42;
	expected_out_result_d = 64'h4000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	test_case = "FCVT.D.S";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive zero";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative zero";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h80000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h8000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive one";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h3f800000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h3ff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative two";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'hc0000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hc000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "smallest normal";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h00800000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h3810000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "largest normal";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h7f7fffff;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h47efffffe0000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "smallest subnormal";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h00000001;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h36a0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "subnormal with two set bits";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h00400001;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h3800000040000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "largest subnormal";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h007fffff;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h380fffffc0000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h7f800000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7ff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'hff800000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hfff0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "quiet NaN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h7fc00001;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7ff8000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "signaling NaN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h7f800001;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7ff8000000000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	test_case = "FCVT.S.D";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive zero";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative zero";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff80000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive one";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative two";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hc000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffc0000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7f800000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hfff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffff800000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "quiet NaN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7fc00000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "signaling NaN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7fc00000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "smallest double subnormal RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000000;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "smallest double subnormal RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000001;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative tiny RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff80000001;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative tiny RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff80000000;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "half min subnormal RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3690000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000000;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "just above half min subnormal RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3690000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000001;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "half min subnormal RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3690000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000000;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "half min subnormal RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3690000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000000;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "half min subnormal RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3690000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000001;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "half min subnormal RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3690000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000001;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "1.5 min subnormals RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h36a8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000002;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "1.5 min subnormals RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h36a8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000001;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "1.5 min subnormals RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h36a8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000001;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "1.5 min subnormals RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h36a8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000002;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "1.5 min subnormals RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h36a8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000002;
	expected_out_except = 5'b00011;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "just below min normal rounds to min normal";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h380fffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "minimum normal";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3810000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00800000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "largest finite single exact";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h47efffffe0000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7f7fffff;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "next double above largest single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h47efffffe0000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7f7fffff;
	expected_out_except = 5'b00101;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive halfway to next single RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive halfway to next single RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive halfway to next single RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive halfway to next single RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "positive halfway to next single RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative halfway to next single RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffbf800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative halfway to next single RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffbf800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative halfway to next single RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffbf800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative halfway to next single RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffbf800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative halfway to next single RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffbf800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "dynamic rounding uses FCSR RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_DYN;
	tb_in_fcsr_rm = fpp::RM_RUP;
	tb_in_A_d = 64'h3ff0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "predecessor of 2 rounds up";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fffffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff40000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "2^128 overflow RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h47f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7f800000;
	expected_out_except = 5'b00101;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "2^128 overflow RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h47f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7f7fffff;
	expected_out_except = 5'b00101;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "2^128 overflow RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h47f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7f7fffff;
	expected_out_except = 5'b00101;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "2^128 overflow RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h47f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff7f800000;
	expected_out_except = 5'b00101;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative 2^128 overflow RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hc7f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffff800000;
	expected_out_except = 5'b00101;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "negative 2^128 overflow RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hc7f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffff7fffff;
	expected_out_except = 5'b00101;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	test_case = "FCVT integer to FP";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W zero to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff00000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W one to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff3f800000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative one to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hffffffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffbf800000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W signed minimum to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000080000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffcf000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W signed maximum to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h000000007fffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4f000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU maximum to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000ffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4f800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU maximum to double exact";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000ffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h41efffffffe00000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative two to double";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000fffffffe;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hc000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W zero to double";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L signed minimum to double";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hc3e0000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L signed maximum to double";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7fffffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h43e0000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU maximum to double";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hffffffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h43f0000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L signed minimum to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffdf000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L signed maximum to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7fffffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff5f000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU maximum to single";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hffffffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff5f800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 2^24+1 RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000001000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4b800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 2^24+1 RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000001000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4b800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 2^24+1 RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000001000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4b800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 2^24+1 RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000001000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4b800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 2^24+1 RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000001000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4b800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 2^24+1 RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000feffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffcb800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 2^24+1 RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000feffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffcb800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 2^24+1 RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000feffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffcb800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 2^24+1 RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000feffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffcb800000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 2^24+1 RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h00000000feffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffcb800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L 2^53+1 RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0020000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h4340000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L 2^53+1 RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0020000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h4340000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L 2^53+1 RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0020000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h4340000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L 2^53+1 RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0020000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h4340000000000001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L 2^53+1 RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0020000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h4340000000000001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W halfway dynamic FCSR RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1101000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_DYN;
	tb_in_fcsr_rm = fpp::RM_RUP;
	tb_in_A_d = 64'h0000000001000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff4b800001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	test_case = "FCVT FP to integer";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W positive zero";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative zero";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 0.5 RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fe0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 0.5 RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fe0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 0.5 RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fe0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 0.5 RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fe0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 0.5 RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fe0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 1.5 RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000002;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 1.5 RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 1.5 RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 1.5 RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000002;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 1.5 RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000002;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 1.5 dynamic FCSR RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_DYN;
	tb_in_fcsr_rm = fpp::RM_RUP;
	tb_in_A_d = 64'h3ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000002;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 1.5 RNE";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hfffffffffffffffe;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 1.5 RTZ";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RTZ;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 1.5 RDN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RDN;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hfffffffffffffffe;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 1.5 RUP";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative 1.5 RMM";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RMM;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hfffffffffffffffe;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 0.25 RNE sticky path";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fd0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W 0.25 RUP sticky path";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RUP;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3fd0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000001;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W single 1.5";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000000;
	tb_in_A_s_boxed = 32'h3fc00000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000002;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU single 1.5";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100000;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0000000000000000;
	tb_in_A_s_boxed = 32'h3fc00000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000002;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L double 1.5";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h3ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000002;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU negative zero valid";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU negative half rounds zero";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbfe0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00001;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU negative one invalid";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W signed maximum exact";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h41dfffffffc00000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h000000007fffffff;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W positive 2^31 saturates";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h41e0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h000000007fffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W signed minimum exact";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hc1e0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff80000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W below signed minimum saturates";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hc1e0000010000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff80000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU maximum exact";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h41efffffffe00000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU 2^32 saturates";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h41f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L signed maximum exact";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h43dfffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7ffffffffffffc00;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L positive 2^63 saturates";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h43e0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7fffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L signed minimum exact";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hc3e0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h8000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L below signed minimum saturates";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hc3e0000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h8000000000000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU max representable below 2^64";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h43efffffffffffff;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hfffffffffffff800;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU 2^64 saturates";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h43f0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU negative zero valid";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h8000000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b00000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU negative one invalid";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hbff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W quiet NaN signed32";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h000000007fffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W signaling NaN signed32";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h000000007fffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU quiet NaN unsigned32";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L signaling NaN signed64";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000001;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7fffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU quiet NaN unsigned64";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff8000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W positive infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h000000007fffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "W negative infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hfff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffff80000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU positive infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "WU negative infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00001;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hfff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L positive infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7fffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "L negative infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00010;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hfff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h8000000000000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU positive infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h7ff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'hffffffffffffffff;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "LU negative infinity";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b1100001;
	tb_in_funct5 = 5'b00011;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'hfff0000000000000;
	tb_in_A_s_boxed = 32'h00000000;
	tb_out_ready = 1'b1;

	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h0000000000000000;
	expected_out_except = 5'b10000;
	check_outputs();

	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	test_case = "default decode";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(posedge CLK); #(PERIOD / 10);
	// inputs
	sub_test_case = "unsupported funct7 returns canonical NaN";
	$display("\t- sub_test: %s", sub_test_case);
	nRST = 1'b1;
	tb_in_valid = 1'b1;
	tb_in_dest_pr = 7'h35;
	tb_in_rob_idx = 7'h52;
	tb_in_funct7 = 7'b0000000;
	tb_in_funct5 = 5'b00000;
	tb_in_instr_rm = fpp::RM_RNE;
	tb_in_fcsr_rm = fpp::RM_RNE;
	tb_in_A_d = 64'h0;
	tb_in_A_s_boxed = 32'h0;
	tb_out_ready = 1'b1;
	@(posedge CLK); #(PERIOD / 10);
	tb_in_valid = 1'b0;
	@(posedge CLK); #(PERIOD / 10);
	// outputs
	expected_in_ready = 1'b1;
	expected_out_valid = 1'b1;
	expected_out_dest_pr = 7'h35;
	expected_out_rob_idx = 7'h52;
	expected_out_result_d = 64'h7ff8000000000000;
	expected_out_except = 5'b00000;
	check_outputs();
	@(posedge CLK); #(PERIOD / 10);
	expected_out_valid = 1'b0;
	check_outputs();

	test_case = "finish";
	$display("\ntest %0d: %s", test_num, test_case);
	test_num++;
	@(posedge CLK); #(PERIOD / 10);
	$display();
	if (num_errors) $display("FAIL: %0d errors", num_errors);
	else $display("SUCCESS: all tests pass");
	$finish;
end

endmodule
