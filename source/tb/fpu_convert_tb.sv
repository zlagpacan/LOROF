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

	task run_case();
	begin
		$display("\t- sub_test: %s", sub_test_case);
		@(negedge CLK);
		tb_in_valid = 1'b1;
		tb_in_dest_pr = 7'h35;
		tb_in_rob_idx = 7'h52;
		tb_out_ready = 1'b1;
		@(posedge CLK); #1;
		if (DUT_in_ready !== 1'b1) begin
			$display("TB ERROR: input unexpectedly stalled for %s", sub_test_case);
			num_errors++;
		end
		// The request was accepted on this edge; drop valid before the next
		// edge so the same transaction is not submitted twice.
		tb_in_valid = 1'b0;
		@(posedge CLK); #1;
		expected_in_ready = 1'b1;
		expected_out_valid = 1'b1;
		expected_out_dest_pr = 7'h35;
		expected_out_rob_idx = 7'h52;
		check_outputs();
		@(negedge CLK);
		tb_in_valid = 1'b0;
		@(posedge CLK); #1;
		expected_out_valid = 1'b0;
		check_outputs();
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

		test_case = "reset and pipeline backpressure";
		$display("\ntest %0d: %s", test_num++, test_case);
		repeat (2) @(posedge CLK);
		#1;
		check_outputs();
		nRST = 1'b1;

		// Fill both elastic stages, then hold the output and verify that
		// valid/data/metadata stay stable while input ready is deasserted.
		@(negedge CLK);
		tb_in_valid = 1'b1;
		tb_in_dest_pr = 7'h11;
		tb_in_rob_idx = 7'h21;
		tb_in_funct7 = 7'b0100001; // FCVT.D.S, +1.0
		tb_in_A_s_boxed = 32'h3f800000;
		tb_out_ready = 1'b0;
		@(posedge CLK);
		@(negedge CLK);
		tb_in_dest_pr = 7'h12;
		tb_in_rob_idx = 7'h22;
		tb_in_A_s_boxed = 32'h40000000;
		@(posedge CLK); #1;
		if (DUT_out_valid !== 1'b1 || DUT_in_ready !== 1'b0 ||
			DUT_out_result_d !== 64'h3ff0000000000000 ||
			DUT_out_dest_pr !== 7'h11 || DUT_out_rob_idx !== 7'h21) begin
			$display("TB ERROR: first transaction/backpressure state incorrect");
			num_errors++;
		end
		@(negedge CLK);
		tb_in_valid = 1'b0;
		repeat (3) begin
			@(posedge CLK); #1;
			if (DUT_out_valid !== 1'b1 || DUT_in_ready !== 1'b0 ||
				DUT_out_result_d !== 64'h3ff0000000000000 ||
				DUT_out_dest_pr !== 7'h11 || DUT_out_rob_idx !== 7'h21) begin
				$display("TB ERROR: output changed while backpressured");
				num_errors++;
			end
		end
		@(negedge CLK);
		tb_out_ready = 1'b1;
		@(posedge CLK); #1;
		if (DUT_out_valid !== 1'b1 || DUT_out_result_d !== 64'h4000000000000000 ||
			DUT_out_dest_pr !== 7'h12 || DUT_out_rob_idx !== 7'h22) begin
			$display("TB ERROR: buffered transaction did not drain after backpressure");
			num_errors++;
		end
		@(posedge CLK); #1;
		if (DUT_out_valid !== 1'b0) begin
			$display("TB ERROR: output valid did not clear after drain");
			num_errors++;
		end

		// The pipeline has two-cycle latency but accepts and completes one
		// transaction every cycle when there is no backpressure.
		test_case = "pipeline throughput";
		$display("\ntest %0d: %s", test_num++, test_case);
		@(negedge CLK);
		tb_in_valid = 1'b1;
		tb_in_funct7 = 7'b0100001;
		tb_in_A_s_boxed = 32'h3f800000;
		tb_in_dest_pr = 7'h31;
		tb_in_rob_idx = 7'h41;
		tb_out_ready = 1'b1;
		@(posedge CLK); #1;
		if (DUT_in_ready !== 1'b1) begin
			$display("TB ERROR: first back-to-back input was stalled");
			num_errors++;
		end
		@(negedge CLK);
		tb_in_A_s_boxed = 32'h40000000;
		tb_in_dest_pr = 7'h32;
		tb_in_rob_idx = 7'h42;
		@(posedge CLK); #1;
		if (DUT_in_ready !== 1'b1 || DUT_out_valid !== 1'b1 ||
			DUT_out_result_d !== 64'h3ff0000000000000 ||
			DUT_out_dest_pr !== 7'h31 || DUT_out_rob_idx !== 7'h41) begin
			$display("TB ERROR: pipeline did not accept/complete one item per cycle");
			num_errors++;
		end
		@(negedge CLK);
		tb_in_valid = 1'b0;
		@(posedge CLK); #1;
		if (DUT_out_valid !== 1'b1 || DUT_out_result_d !== 64'h4000000000000000 ||
			DUT_out_dest_pr !== 7'h32 || DUT_out_rob_idx !== 7'h42) begin
			$display("TB ERROR: second back-to-back result was not delivered next cycle");
			num_errors++;
		end
		@(posedge CLK); #1;

		test_case = "FCVT.D.S";
		$display("\ntest %0d: %s", test_num++, test_case);
		sub_test_case = "positive one";
		tb_in_funct7 = 7'b0100001;
		tb_in_A_s_boxed = 32'h3f800000;
		expected_out_result_d = 64'h3ff0000000000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "negative two";
		tb_in_funct7 = 7'b0100001;
		tb_in_A_s_boxed = 32'hc0000000;
		expected_out_result_d = 64'hc000000000000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "smallest subnormal";
		tb_in_funct7 = 7'b0100001;
		tb_in_A_s_boxed = 32'h00000001;
		expected_out_result_d = 64'h36a0000000000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "subnormal with two set bits";
		tb_in_funct7 = 7'b0100001;
		tb_in_A_s_boxed = 32'h00400001;
		expected_out_result_d = 64'h3800000040000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "signaling NaN";
		tb_in_funct7 = 7'b0100001;
		tb_in_A_s_boxed = 32'h7f800001;
		expected_out_result_d = 64'h7ff8000000000000;
		expected_out_except = 5'b10000;
		run_case();

		test_case = "FCVT.S.D";
		$display("\ntest %0d: %s", test_num++, test_case);
		sub_test_case = "positive one";
		tb_in_funct7 = 7'b0100000;
		tb_in_A_d = 64'h3ff0000000000000;
		expected_out_result_d = 64'hffffffff3f800000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "negative two";
		tb_in_funct7 = 7'b0100000;
		tb_in_A_d = 64'hc000000000000000;
		expected_out_result_d = 64'hffffffffc0000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "positive infinity";
		tb_in_funct7 = 7'b0100000;
		tb_in_A_d = 64'h7ff0000000000000;
		expected_out_result_d = 64'hffffffff7f800000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "tiny rounds to zero with NX UF";
		tb_in_funct7 = 7'b0100000;
		tb_in_A_d = 64'h3690000000000000;
		expected_out_result_d = 64'hffffffff00000000;
		expected_out_except = 5'b00011;
		run_case();

		// Halfway between 1.0 and the next larger single precision value.
		sub_test_case = "positive halfway RNE ties even down";
		tb_in_funct7 = 7'b0100000;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h3ff0000010000000;
		expected_out_result_d = 64'hffffffff3f800000;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "positive halfway RTZ down";
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_result_d = 64'hffffffff3f800000;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "positive halfway RDN down";
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_result_d = 64'hffffffff3f800000;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "positive halfway RUP up";
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_result_d = 64'hffffffff3f800001;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "positive halfway RMM away";
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_result_d = 64'hffffffff3f800001;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "negative halfway RDN away";
		tb_in_instr_rm = fpp::RM_RDN;
		tb_in_A_d = 64'hbff0000010000000;
		expected_out_result_d = 64'hffffffffbf800001;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "dynamic RM uses FCSR RUP";
		tb_in_instr_rm = fpp::RM_DYN;
		tb_in_fcsr_rm = fpp::RM_RUP;
		tb_in_A_d = 64'h3ff0000010000000;
		expected_out_result_d = 64'hffffffff3f800001;
		expected_out_except = 5'b00001;
		run_case();

		test_case = "FCVT integer to FP";
		$display("\ntest %0d: %s", test_num++, test_case);
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_fcsr_rm = fpp::RM_RNE;
		sub_test_case = "W 1 to single";
		tb_in_funct7 = 7'b1101000;
		tb_in_funct5 = 5'b00000;
		tb_in_A_d = 64'h1;
		expected_out_result_d = 64'hffffffff3f800000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "W -2 to single";
		tb_in_funct7 = 7'b1101000;
		tb_in_funct5 = 5'b00000;
		tb_in_A_d = 64'hfffffffe;
		expected_out_result_d = 64'hffffffffc0000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "WU 2 to double";
		tb_in_funct7 = 7'b1101001;
		tb_in_funct5 = 5'b00001;
		tb_in_A_d = 64'h2;
		expected_out_result_d = 64'h4000000000000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "L -1 to double";
		tb_in_funct7 = 7'b1101001;
		tb_in_funct5 = 5'b00010;
		tb_in_A_d = 64'hffffffffffffffff;
		expected_out_result_d = 64'hbff0000000000000;
		expected_out_except = 0;
		run_case();

		sub_test_case = "rounding sets NX";
		tb_in_funct7 = 7'b1101001;
		tb_in_funct5 = 5'b00010;
		tb_in_A_d = 64'h0020000000000001;
		expected_out_result_d = 64'h4340000000000000;
		expected_out_except = 5'b00001;
		run_case();

		// 2^24+1 is exactly halfway between adjacent single precision values.
		sub_test_case = "W halfway RNE ties even down";
		tb_in_funct7 = 7'b1101000;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h01000001;
		expected_out_result_d = 64'hffffffff4b800000;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W halfway RTZ down";
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_result_d = 64'hffffffff4b800000;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W halfway RDN down";
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_result_d = 64'hffffffff4b800000;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W halfway RUP up";
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_result_d = 64'hffffffff4b800001;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W halfway RMM away";
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_result_d = 64'hffffffff4b800001;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W negative halfway RDN away";
		tb_in_instr_rm = fpp::RM_RDN;
		tb_in_A_d = 64'hfeffffff;
		expected_out_result_d = 64'hffffffffcb800001;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W negative halfway RUP toward zero";
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_result_d = 64'hffffffffcb800000;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "L halfway RMM away";
		tb_in_funct7 = 7'b1101001;
		tb_in_funct5 = 5'b00010;
		tb_in_instr_rm = fpp::RM_RMM;
		tb_in_A_d = 64'h0020000000000001;
		expected_out_result_d = 64'h4340000000000001;
		expected_out_except = 5'b00001;
		run_case();

		test_case = "FCVT FP to integer";
		$display("\ntest %0d: %s", test_num++, test_case);
		sub_test_case = "W 1.5 RNE";
		tb_in_funct7 = 7'b1100001;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h3ff8000000000000;
		expected_out_result_d = 64'h2;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W 1.5 RTZ";
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_result_d = 64'h1;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W 1.5 RDN";
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_result_d = 64'h1;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W 1.5 RUP";
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_result_d = 64'h2;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W 1.5 RMM";
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_result_d = 64'h2;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W 1.5 dynamic RM uses FCSR RUP";
		tb_in_instr_rm = fpp::RM_DYN;
		tb_in_fcsr_rm = fpp::RM_RUP;
		expected_out_result_d = 64'h2;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W -1.5 RNE";
		tb_in_funct7 = 7'b1100001;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_fcsr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'hbff8000000000000;
		expected_out_result_d = 64'hfffffffffffffffe;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W -1.5 RTZ";
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_result_d = 64'hffffffffffffffff;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W -1.5 RDN";
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_result_d = 64'hfffffffffffffffe;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W -1.5 RUP";
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_result_d = 64'hffffffffffffffff;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "W -1.5 RMM";
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_result_d = 64'hfffffffffffffffe;
		expected_out_except = 5'b00001;
		run_case();

		sub_test_case = "WU negative invalid";
		tb_in_funct7 = 7'b1100001;
		tb_in_funct5 = 5'b00001;
		tb_in_instr_rm = fpp::RM_RTZ;
		tb_in_A_d = 64'hbff0000000000000;
		expected_out_result_d = 64'h0;
		expected_out_except = 5'b10000;
		run_case();

		sub_test_case = "W positive overflow saturates";
		tb_in_funct7 = 7'b1100001;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_RTZ;
		tb_in_A_d = 64'h41e0000000000000;
		expected_out_result_d = 64'h7fffffff;
		expected_out_except = 5'b10000;
		run_case();

		sub_test_case = "L positive infinity invalid";
		tb_in_funct7 = 7'b1100001;
		tb_in_funct5 = 5'b00010;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h7ff0000000000000;
		expected_out_result_d = 64'h7fffffffffffffff;
		expected_out_except = 5'b10000;
		run_case();

		sub_test_case = "S 1.5 rounds up";
		tb_in_funct7 = 7'b1100000;
		tb_in_funct5 = 5'b00000;
		tb_in_instr_rm = fpp::RM_RUP;
		tb_in_A_s_boxed = 32'h3fc00000;
		expected_out_result_d = 64'h2;
		expected_out_except = 5'b00001;
		run_case();

		test_case = "finish";
		$display("\ntest %0d: %s", test_num++, test_case);
		@(posedge CLK); #1;
		$display();
		if (num_errors) $display("FAIL: %0d errors", num_errors);
		else $display("SUCCESS: all tests pass");
		$finish;
	end

endmodule
