/*
	Filename: fpu_fuse_tb.sv
	Author: zlagpacan
	Description: Testbench for fpu_fuse module.
	Spec: LOROF/spec/design/fpu_fuse.md
*/

`timescale 1ns/100ps

`include "fpp.vh"

module fpu_fuse_tb #(
) ();

	parameter int unsigned PERIOD = 10;
	localparam int unsigned PIPE_LATENCY = 12;

	logic CLK = 1'b1, nRST;
	string test_case;
	string sub_test_case;
	int test_num = 0;
	int num_errors = 0;
	logic tb_error = 1'b0;

	always begin #(PERIOD/2); CLK = ~CLK; end

	logic tb_in_valid;
	fpp::fp_tag_t tb_in_fp_tag;
	logic DUT_in_ready, expected_in_ready;
	logic [6:0] tb_in_opcode7;
	logic [1:0] tb_in_funct2;
	logic [2:0] tb_in_instr_rm, tb_in_fcsr_rm;
	fpp::double_t tb_in_A_d, tb_in_B_d, tb_in_C_d;
	fpp::single_t tb_in_A_s_boxed, tb_in_B_s_boxed, tb_in_C_s_boxed;
	logic DUT_out_valid, expected_out_valid;
	fpp::fp_tag_t DUT_out_fp_tag, expected_out_fp_tag;
	logic tb_out_ready;
	fpp::double_t DUT_out_result_d, expected_out_result_d;
	fpp::fpu_except_t DUT_out_except, expected_out_except;

	typedef struct packed {
		logic valid;
		fpp::fp_tag_t fp_tag;
		fpp::double_t result_d;
		fpp::fpu_except_t except;
	} expected_packet_t;
	expected_packet_t expected_packet_now;
	expected_packet_t expected_pipe [0:PIPE_LATENCY];

	fpu_fuse DUT (
		.CLK(CLK), .nRST(nRST),
		.in_valid(tb_in_valid), .in_fp_tag(tb_in_fp_tag),
		.in_ready(DUT_in_ready),
		.in_opcode7(tb_in_opcode7), .in_funct2(tb_in_funct2),
		.in_instr_rm(tb_in_instr_rm), .in_fcsr_rm(tb_in_fcsr_rm),
		.in_A_d(tb_in_A_d), .in_A_s_boxed(tb_in_A_s_boxed),
		.in_B_d(tb_in_B_d), .in_B_s_boxed(tb_in_B_s_boxed),
		.in_C_d(tb_in_C_d), .in_C_s_boxed(tb_in_C_s_boxed),
		.out_valid(DUT_out_valid), .out_fp_tag(DUT_out_fp_tag),
		.out_ready(tb_out_ready), .out_result_d(DUT_out_result_d), .out_except(DUT_out_except)
	);

	function automatic fpp::double_t box_single(input logic [31:0] bits);
		return {32'hffffffff, bits};
	endfunction

	task check_outputs();
		integer i;
	begin
		expected_packet_now = {expected_out_valid, expected_out_fp_tag,
			expected_out_result_d, expected_out_except};
		if (expected_in_ready !== DUT_in_ready) begin
			$display("TB ERROR: expected_in_ready (%b) != DUT_in_ready (%b)", expected_in_ready, DUT_in_ready);
			num_errors++; tb_error = 1'b1;
		end
		if (expected_pipe[PIPE_LATENCY].valid !== DUT_out_valid) begin
			$display("TB ERROR: expected_out_valid (%b) != DUT_out_valid (%b)", expected_pipe[PIPE_LATENCY].valid, DUT_out_valid);
			num_errors++; tb_error = 1'b1;
		end
		if (expected_pipe[PIPE_LATENCY].valid) begin
			if (expected_pipe[PIPE_LATENCY].fp_tag !== DUT_out_fp_tag) begin
				$display("TB ERROR: expected_out_fp_tag (%h) != DUT_out_fp_tag (%h)", expected_pipe[PIPE_LATENCY].fp_tag, DUT_out_fp_tag);
				num_errors++; tb_error = 1'b1;
			end
			if (expected_pipe[PIPE_LATENCY].result_d !== DUT_out_result_d) begin
				$display("TB ERROR: expected_out_result_d (%h) != DUT_out_result_d (%h)", expected_pipe[PIPE_LATENCY].result_d, DUT_out_result_d);
				num_errors++; tb_error = 1'b1;
			end
			if (expected_pipe[PIPE_LATENCY].except !== DUT_out_except) begin
				$display("TB ERROR: expected_out_except (%b) != DUT_out_except (%b)", expected_pipe[PIPE_LATENCY].except, DUT_out_except);
				num_errors++; tb_error = 1'b1;
			end
		end
		for (i = PIPE_LATENCY; i > 0; i = i - 1)
			expected_pipe[i] = expected_pipe[i-1];
		expected_pipe[0] = expected_packet_now;
		#(PERIOD / 10);
		tb_error = 1'b0;
	end
	endtask

	initial begin
		nRST = 1'b0;
		tb_in_valid = 1'b0;
		tb_in_fp_tag = '0;
		tb_in_opcode7 = 7'b1000011;
		tb_in_funct2 = 2'b00;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_fcsr_rm = fpp::RM_RNE;
		tb_in_A_d = '0; tb_in_B_d = '0; tb_in_C_d = '0;
		tb_in_A_s_boxed = '0; tb_in_B_s_boxed = '0; tb_in_C_s_boxed = '0;
		tb_out_ready = 1'b1;
		expected_in_ready = 1'b1;
		expected_out_valid = 1'b0;
		expected_out_fp_tag = '0;
		expected_out_result_d = '0;
		expected_out_except = '0;
		expected_pipe = '{default:'0};

		test_case = "reset";
		$display("\ntest %0d: %s", test_num, test_case);
		test_num++;
		@(posedge CLK); #(PERIOD/10);
		check_outputs();
		nRST = 1'b1;

		test_case = "pipelined fused operation stream";
		$display("\ntest %0d: %s", test_num, test_case);
		test_num++;

		@(negedge CLK);
		sub_test_case = "FMADD.S: 1 * 2 + 3 = 5";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h10, rob_idx: 7'h20};
		tb_in_opcode7 = 7'b1000011; tb_in_funct2 = 2'b00;
		tb_in_instr_rm = fpp::RM_RNE; tb_in_fcsr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h40000000; tb_in_C_s_boxed = 32'h40400000;
		expected_in_ready = 1'b1; expected_out_valid = 1'b1; expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h10, rob_idx: 7'h20};
		expected_out_result_d = box_single(32'h40a00000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.S: 1 * 2 - 3 = -1";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h11, rob_idx: 7'h21};
		tb_in_opcode7 = 7'b1000111; tb_in_funct2 = 2'b00;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h40000000; tb_in_C_s_boxed = 32'h40400000;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h11, rob_idx: 7'h21};
		expected_out_result_d = box_single(32'hbf800000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMSUB.S: -(1 * 2) + 3 = 1";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h12, rob_idx: 7'h22};
		tb_in_opcode7 = 7'b1001011; tb_in_funct2 = 2'b00;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h40000000; tb_in_C_s_boxed = 32'h40400000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h12, rob_idx: 7'h22};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.S: -(1 * 2) - 3 = -5";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h13, rob_idx: 7'h23};
		tb_in_opcode7 = 7'b1001111; tb_in_funct2 = 2'b00;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h40000000; tb_in_C_s_boxed = 32'h40400000;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h13, rob_idx: 7'h23};
		expected_out_result_d = box_single(32'hc0a00000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S product with a zero addend";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h35, rob_idx: 7'h45};
		tb_in_opcode7 = 7'b1000011; tb_in_funct2 = 2'b00;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h00000000;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h35, rob_idx: 7'h45};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.S tie under RNE rounds to even one";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h3d, rob_idx: 7'h4d};
		tb_in_opcode7 = 7'b1000111; tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h33000000;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h3d, rob_idx: 7'h4d};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.S tie under RTZ rounds to predecessor";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h3e, rob_idx: 7'h4e};
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h3e, rob_idx: 7'h4e};
		expected_out_result_d = box_single(32'h3f7fffff); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.S tie under RDN rounds to the predecessor";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h36, rob_idx: 7'h46};
		tb_in_opcode7 = 7'b1000111; tb_in_funct2 = 2'b00;
		tb_in_instr_rm = fpp::RM_RDN;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h33000000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h36, rob_idx: 7'h46};
		expected_out_result_d = box_single(32'h3f7fffff); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.S tie under RUP rounds to one";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h37, rob_idx: 7'h47};
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h37, rob_idx: 7'h47};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.S tie under RMM rounds away from zero";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h38, rob_idx: 7'h48};
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h38, rob_idx: 7'h48};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMSUB.S exact cancellation is positive zero under RNE";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h39, rob_idx: 7'h49};
		tb_in_opcode7 = 7'b1001011; tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h3f800000;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h39, rob_idx: 7'h49};
		expected_out_result_d = box_single(32'h00000000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMSUB.S exact cancellation is negative zero under RDN";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h3a, rob_idx: 7'h4a};
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h3a, rob_idx: 7'h4a};
		expected_out_result_d = box_single(32'h80000000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.S negative tie rounds away under RDN";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h3b, rob_idx: 7'h4b};
		tb_in_opcode7 = 7'b1001111; tb_in_instr_rm = fpp::RM_RDN;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h33800000;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h3b, rob_idx: 7'h4b};
		expected_out_result_d = box_single(32'hbf800001); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.S negative tie rounds toward zero under RUP";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h3c, rob_idx: 7'h4c};
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h3c, rob_idx: 7'h4c};
		expected_out_result_d = box_single(32'hbf800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.S negative tie rounds to even under RNE";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h3f, rob_idx: 7'h4f};
		tb_in_opcode7 = 7'b1001111; tb_in_instr_rm = fpp::RM_RNE;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h3f, rob_idx: 7'h4f};
		expected_out_result_d = box_single(32'hbf800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.S negative tie rounds toward zero under RTZ";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h40, rob_idx: 7'h50};
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h40, rob_idx: 7'h50};
		expected_out_result_d = box_single(32'hbf800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.S negative tie rounds away under RMM";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h41, rob_idx: 7'h51};
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h41, rob_idx: 7'h51};
		expected_out_result_d = box_single(32'hbf800001); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S tie: RNE even rounds down";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h14, rob_idx: 7'h24};
		tb_in_opcode7 = 7'b1000011; tb_in_funct2 = 2'b00;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h33800000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h14, rob_idx: 7'h24};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S tie: RTZ rounds down";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h15, rob_idx: 7'h25};
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h15, rob_idx: 7'h25};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S tie: RDN rounds down";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h16, rob_idx: 7'h26};
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h16, rob_idx: 7'h26};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S tie: RUP rounds up";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h17, rob_idx: 7'h27};
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h17, rob_idx: 7'h27};
		expected_out_result_d = box_single(32'h3f800001); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S tie: RMM rounds away";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h18, rob_idx: 7'h28};
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h18, rob_idx: 7'h28};
		expected_out_result_d = box_single(32'h3f800001); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S dynamic rounding selects FCSR RUP";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h19, rob_idx: 7'h29};
		tb_in_instr_rm = fpp::RM_DYN; tb_in_fcsr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h19, rob_idx: 7'h29};
		expected_out_result_d = box_single(32'h3f800001); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S minimum subnormal times one";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h1a, rob_idx: 7'h2a};
		tb_in_instr_rm = fpp::RM_RNE; tb_in_fcsr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h00000001; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h00000000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h1a, rob_idx: 7'h2a};
		expected_out_result_d = box_single(32'h00000001); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S half minimum subnormal rounds to zero";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h1b, rob_idx: 7'h2b};
		tb_in_A_s_boxed = 32'h00000001; tb_in_B_s_boxed = 32'h3f000000;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h1b, rob_idx: 7'h2b};
		expected_out_result_d = box_single(32'h00000000); expected_out_except = 5'b00011;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S qNaN propagates canonically without NV";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h1c, rob_idx: 7'h2c};
		tb_in_A_s_boxed = 32'h7fc00000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h00000000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h1c, rob_idx: 7'h2c};
		expected_out_result_d = box_single(32'h7fc00000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S sNaN raises NV";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h1d, rob_idx: 7'h2d};
		tb_in_A_s_boxed = 32'h7f800001;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h1d, rob_idx: 7'h2d};
		expected_out_result_d = box_single(32'h7fc00000); expected_out_except = 5'b10000;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S zero times infinity raises NV";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h1e, rob_idx: 7'h2e};
		tb_in_A_s_boxed = 32'h00000000; tb_in_B_s_boxed = 32'h7f800000; tb_in_C_s_boxed = 32'h3f800000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h1e, rob_idx: 7'h2e};
		expected_out_result_d = box_single(32'h7fc00000); expected_out_except = 5'b10000;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S opposite-signed infinities raise NV";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h1f, rob_idx: 7'h2f};
		tb_in_A_s_boxed = 32'h7f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'hff800000;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h1f, rob_idx: 7'h2f};
		expected_out_result_d = box_single(32'h7fc00000); expected_out_except = 5'b10000;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S infinity plus finite remains infinity";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h20, rob_idx: 7'h30};
		tb_in_A_s_boxed = 32'h7f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h40400000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h20, rob_idx: 7'h30};
		expected_out_result_d = box_single(32'h7f800000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S 1.5 * 1.5 + 0.25 retains fused result";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h30, rob_idx: 7'h40};
		tb_in_A_s_boxed = 32'h3fc00000; tb_in_B_s_boxed = 32'h3fc00000; tb_in_C_s_boxed = 32'h3e800000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h30, rob_idx: 7'h40};
		expected_out_result_d = box_single(32'h40200000); expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S distant addend contributes sticky and NX";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h31, rob_idx: 7'h41};
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h00000001;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h31, rob_idx: 7'h41};
		expected_out_result_d = box_single(32'h3f800000); expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S overflow to infinity";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h32, rob_idx: 7'h42};
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h7f000000; tb_in_B_s_boxed = 32'h40000000; tb_in_C_s_boxed = 32'h00000000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h32, rob_idx: 7'h42};
		expected_out_result_d = box_single(32'h7f800000); expected_out_except = 5'b00101;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S overflow saturates under RTZ";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h33, rob_idx: 7'h43};
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h33, rob_idx: 7'h43};
		expected_out_result_d = box_single(32'h7f7fffff); expected_out_except = 5'b00101;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.S underflow rounds up to minimum subnormal";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h34, rob_idx: 7'h44};
		tb_in_instr_rm = fpp::RM_RUP;
		tb_in_A_s_boxed = 32'h00000001; tb_in_B_s_boxed = 32'h3f000000; tb_in_C_s_boxed = 32'h00000000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h34, rob_idx: 7'h44};
		expected_out_result_d = box_single(32'h00000001); expected_out_except = 5'b00011;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D exact";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h21, rob_idx: 7'h31};
		tb_in_opcode7 = 7'b1000011; tb_in_funct2 = 2'b01;
		tb_in_A_d = 64'h3ff0000000000000; tb_in_B_d = 64'h4000000000000000; tb_in_C_d = 64'h4008000000000000;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h21, rob_idx: 7'h31};
		expected_out_result_d = 64'h4014000000000000; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.D exact";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h22, rob_idx: 7'h32};
		tb_in_opcode7 = 7'b1000111; tb_in_funct2 = 2'b01;
		tb_in_A_d = 64'h3ff0000000000000; tb_in_B_d = 64'h4000000000000000; tb_in_C_d = 64'h4008000000000000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h22, rob_idx: 7'h32};
		expected_out_result_d = 64'hbff0000000000000; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMSUB.D: -(2 * 2) + 5 = 1";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h2c, rob_idx: 7'h3c};
		tb_in_opcode7 = 7'b1001011; tb_in_funct2 = 2'b01;
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h4000000000000000; tb_in_B_d = 64'h4000000000000000; tb_in_C_d = 64'h4014000000000000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h2c, rob_idx: 7'h3c};
		expected_out_result_d = 64'h3ff0000000000000; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.D: -(2 * 2) - 1 = -5";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h2d, rob_idx: 7'h3d};
		tb_in_opcode7 = 7'b1001111;
		tb_in_A_d = 64'h4000000000000000; tb_in_B_d = 64'h4000000000000000; tb_in_C_d = 64'h3ff0000000000000;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h2d, rob_idx: 7'h3d};
		expected_out_result_d = 64'hc014000000000000; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMSUB.D exact cancellation is negative zero under RDN";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h2e, rob_idx: 7'h3e};
		tb_in_opcode7 = 7'b1001011; tb_in_instr_rm = fpp::RM_RDN;
		tb_in_A_d = 64'h3ff0000000000000; tb_in_B_d = 64'h3ff0000000000000; tb_in_C_d = 64'h3ff0000000000000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h2e, rob_idx: 7'h3e};
		expected_out_result_d = 64'h8000000000000000; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.D tie RNE rounds to even one";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h2f, rob_idx: 7'h3f};
		tb_in_opcode7 = 7'b1000111; tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h3ff0000000000000; tb_in_B_d = 64'h3ff0000000000000; tb_in_C_d = 64'h3c90000000000000;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h2f, rob_idx: 7'h3f};
		expected_out_result_d = 64'h3ff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.D tie RTZ rounds to predecessor";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h30, rob_idx: 7'h40};
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h30, rob_idx: 7'h40};
		expected_out_result_d = 64'h3fefffffffffffff; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.D tie RDN rounds to predecessor";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h31, rob_idx: 7'h41};
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h31, rob_idx: 7'h41};
		expected_out_result_d = 64'h3fefffffffffffff; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.D tie RUP rounds to one";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h32, rob_idx: 7'h42};
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h32, rob_idx: 7'h42};
		expected_out_result_d = 64'h3ff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMSUB.D tie RMM rounds away from zero";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h33, rob_idx: 7'h43};
		tb_in_instr_rm = fpp::RM_RMM;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h33, rob_idx: 7'h43};
		expected_out_result_d = 64'h3ff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.D negative tie RNE rounds to even";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h34, rob_idx: 7'h44};
		tb_in_opcode7 = 7'b1001111; tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h3ff0000000000000; tb_in_B_d = 64'h3ff0000000000000; tb_in_C_d = 64'h3ca0000000000000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h34, rob_idx: 7'h44};
		expected_out_result_d = 64'hbff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.D negative tie RTZ rounds toward zero";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h35, rob_idx: 7'h45};
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h35, rob_idx: 7'h45};
		expected_out_result_d = 64'hbff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.D negative tie RDN rounds away";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h36, rob_idx: 7'h46};
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h36, rob_idx: 7'h46};
		expected_out_result_d = 64'hbff0000000000001; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FNMADD.D negative tie RUP rounds toward zero";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h37, rob_idx: 7'h47};
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h37, rob_idx: 7'h47};
		expected_out_result_d = 64'hbff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D tie RMM rounds away";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h23, rob_idx: 7'h33};
		tb_in_opcode7 = 7'b1000011; tb_in_funct2 = 2'b01;
		tb_in_instr_rm = fpp::RM_RMM;
		tb_in_A_d = 64'h3ff0000000000000; tb_in_B_d = 64'h3ff0000000000000; tb_in_C_d = 64'h3ca0000000000000;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h23, rob_idx: 7'h33};
		expected_out_result_d = 64'h3ff0000000000001; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D tie RNE rounds to even";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h25, rob_idx: 7'h35};
		tb_in_instr_rm = fpp::RM_RNE;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h25, rob_idx: 7'h35};
		expected_out_result_d = 64'h3ff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D tie RTZ rounds down";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h26, rob_idx: 7'h36};
		tb_in_instr_rm = fpp::RM_RTZ;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h26, rob_idx: 7'h36};
		expected_out_result_d = 64'h3ff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D tie RDN rounds down";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h27, rob_idx: 7'h37};
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h27, rob_idx: 7'h37};
		expected_out_result_d = 64'h3ff0000000000000; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D tie RUP rounds up";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h28, rob_idx: 7'h38};
		tb_in_instr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h28, rob_idx: 7'h38};
		expected_out_result_d = 64'h3ff0000000000001; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D tie dynamic rounding selects FCSR RUP";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h29, rob_idx: 7'h39};
		tb_in_instr_rm = fpp::RM_DYN; tb_in_fcsr_rm = fpp::RM_RUP;
		expected_out_fp_tag = '{hart_id: 2'd1, dest_pr: 7'h29, rob_idx: 7'h39};
		expected_out_result_d = 64'h3ff0000000000001; expected_out_except = 5'b00001;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D minimum subnormal times one";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h24, rob_idx: 7'h34};
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h0000000000000001; tb_in_B_d = 64'h3ff0000000000000; tb_in_C_d = 64'h0000000000000000;
		expected_out_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h24, rob_idx: 7'h34};
		expected_out_result_d = 64'h0000000000000001; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D exact cancellation produces positive zero";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h2a, rob_idx: 7'h3a};
		tb_in_instr_rm = fpp::RM_RNE;
		tb_in_A_d = 64'h3ff0000000000000; tb_in_B_d = 64'h3ff0000000000000; tb_in_C_d = 64'hbff0000000000000;
		expected_out_fp_tag = '{hart_id: 2'd2, dest_pr: 7'h2a, rob_idx: 7'h3a};
		expected_out_result_d = 64'h0000000000000000; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "FMADD.D exact cancellation is negative zero under RDN";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h2b, rob_idx: 7'h3b};
		tb_in_instr_rm = fpp::RM_RDN;
		expected_out_fp_tag = '{hart_id: 2'd3, dest_pr: 7'h2b, rob_idx: 7'h3b};
		expected_out_result_d = 64'h8000000000000000; expected_out_except = '0;
		@(posedge CLK); #(PERIOD/10); check_outputs();

		@(negedge CLK);
		sub_test_case = "bubble and pipeline drain";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b0; expected_out_valid = 1'b0;
		expected_in_ready = 1'b1;
		@(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();
		@(negedge CLK); @(posedge CLK); #(PERIOD/10); check_outputs();

		test_case = "output backpressure holds the completed transaction";
		$display("\ntest %0d: %s", test_num, test_case);
		test_num++;
		@(negedge CLK);
		sub_test_case = "issue FMADD.S and block output";
		$display("\t- sub_test: %s", sub_test_case);
		tb_in_valid = 1'b1; tb_in_fp_tag = '{hart_id: 2'd0, dest_pr: 7'h50, rob_idx: 7'h60};
		tb_in_opcode7 = 7'b1000011; tb_in_funct2 = 2'b00;
		tb_in_instr_rm = fpp::RM_RNE; tb_in_fcsr_rm = fpp::RM_RNE;
		tb_in_A_s_boxed = 32'h3f800000; tb_in_B_s_boxed = 32'h3f800000; tb_in_C_s_boxed = 32'h00000000;
		tb_out_ready = 1'b0;
		@(posedge CLK); #(PERIOD/10);
		@(negedge CLK); tb_in_valid = 1'b0;
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		@(posedge CLK); #(PERIOD/10);
		if (DUT_out_valid !== 1'b1 || DUT_out_fp_tag !== fpp::fp_tag_t'('{hart_id: 2'd0, dest_pr: 7'h50, rob_idx: 7'h60}) ||
			DUT_out_result_d !== box_single(32'h3f800000) || DUT_out_except !== '0) begin
			$display("TB ERROR: stalled output transaction mismatch: valid=%b dest=%h rob=%h result=%h except=%b",
				DUT_out_valid,DUT_out_fp_tag.dest_pr,DUT_out_fp_tag.rob_idx,DUT_out_result_d,DUT_out_except);
			num_errors++; tb_error = 1'b1;
		end
		@(posedge CLK); #(PERIOD/10);
		if (DUT_out_valid !== 1'b1 || DUT_out_fp_tag !== fpp::fp_tag_t'('{hart_id: 2'd0, dest_pr: 7'h50, rob_idx: 7'h60}) ||
			DUT_out_result_d !== box_single(32'h3f800000) || DUT_out_except !== '0) begin
			$display("TB ERROR: output changed while out_ready was low: valid=%b dest=%h rob=%h result=%h except=%b",
				DUT_out_valid,DUT_out_fp_tag.dest_pr,DUT_out_fp_tag.rob_idx,DUT_out_result_d,DUT_out_except);
			num_errors++; tb_error = 1'b1;
		end
		@(negedge CLK); tb_out_ready = 1'b1;
		@(posedge CLK); #(PERIOD/10);
		if (DUT_out_valid !== 1'b0) begin
			$display("TB ERROR: output valid did not clear after handshake");
			num_errors++; tb_error = 1'b1;
		end

		test_case = "finish";
		$display("\ntest %0d: %s", test_num, test_case);
		test_num++;
		if (num_errors) $display("FAIL: %0d errors", num_errors);
		else $display("SUCCESS: all tests pass");
		$display();
		$finish();
	end

endmodule
