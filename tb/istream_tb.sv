/*
    Filename: istream_tb.sv
    Author: zlagpacan
    Description: Testbench for istream module. 
    Spec: LOROF/spec/design/istream.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module istream_tb ();

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


    // SENQ stage
	logic tb_valid_SENQ;
	logic [FETCH_WIDTH_2B-1:0] tb_valid_by_fetch_2B_SENQ;
	logic [FETCH_WIDTH_2B-1:0][15:0] tb_instr_2B_by_fetch_2B_SENQ;
	logic [FETCH_WIDTH_2B-1:0][BTB_PRED_INFO_WIDTH-1:0] tb_pred_info_by_fetch_2B_SENQ;
	logic [FETCH_WIDTH_2B-1:0] tb_dep_pred_by_fetch_2B_SENQ;
	logic [31:0] tb_after_PC_SENQ;
	logic [LH_LENGTH-1:0] tb_LH_SENQ;
	logic [GH_LENGTH-1:0] tb_GH_SENQ;
	logic [RAS_INDEX_WIDTH-1:0] tb_ras_index_SENQ;

    // SENQ feedback
	logic DUT_stall_SENQ, expected_stall_SENQ;

    // SDEQ stage
	logic DUT_valid_SDEQ, expected_valid_SDEQ;
	logic [3:0] DUT_valid_by_way_SDEQ, expected_valid_by_way_SDEQ;
	logic [3:0] DUT_uncompressed_by_way_SDEQ, expected_uncompressed_by_way_SDEQ;
	logic [3:0][1:0][15:0] DUT_instr_2B_by_way_by_chunk_SDEQ, expected_instr_2B_by_way_by_chunk_SDEQ;
	logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0] DUT_pred_info_by_way_by_chunk_SDEQ, expected_pred_info_by_way_by_chunk_SDEQ;
	logic [3:0] DUT_dep_pred_by_way_SDEQ, expected_dep_pred_by_way_SDEQ;
	logic [3:0][31:0] DUT_PC_by_way_SDEQ, expected_PC_by_way_SDEQ;
	logic [3:0][LH_LENGTH-1:0] DUT_LH_by_way_SDEQ, expected_LH_by_way_SDEQ;
	logic [3:0][GH_LENGTH-1:0] DUT_GH_by_way_SDEQ, expected_GH_by_way_SDEQ;
	logic [3:0][RAS_INDEX_WIDTH-1:0] DUT_ras_index_by_way_SDEQ, expected_ras_index_by_way_SDEQ;

    // SDEQ feedback
	logic tb_stall_SDEQ;

    // control
	logic tb_restart;
	logic [31:0] tb_restart_PC;

    // ----------------------------------------------------------------
    // DUT instantiation:

	istream #(
		.ISTREAM_SETS(8),
		.INIT_PC(32'h80000000)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // SENQ stage
		.valid_SENQ(tb_valid_SENQ),
		.valid_by_fetch_2B_SENQ(tb_valid_by_fetch_2B_SENQ),
		.instr_2B_by_fetch_2B_SENQ(tb_instr_2B_by_fetch_2B_SENQ),
		.pred_info_by_fetch_2B_SENQ(tb_pred_info_by_fetch_2B_SENQ),
		.dep_pred_by_fetch_2B_SENQ(tb_dep_pred_by_fetch_2B_SENQ),
		.after_PC_SENQ(tb_after_PC_SENQ),
		.LH_SENQ(tb_LH_SENQ),
		.GH_SENQ(tb_GH_SENQ),
		.ras_index_SENQ(tb_ras_index_SENQ),

	    // SENQ feedback
		.stall_SENQ(DUT_stall_SENQ),

	    // SDEQ stage
		.valid_SDEQ(DUT_valid_SDEQ),
		.valid_by_way_SDEQ(DUT_valid_by_way_SDEQ),
		.uncompressed_by_way_SDEQ(DUT_uncompressed_by_way_SDEQ),
		.instr_2B_by_way_by_chunk_SDEQ(DUT_instr_2B_by_way_by_chunk_SDEQ),
		.pred_info_by_way_by_chunk_SDEQ(DUT_pred_info_by_way_by_chunk_SDEQ),
		.dep_pred_by_way_SDEQ(DUT_dep_pred_by_way_SDEQ),
		.PC_by_way_SDEQ(DUT_PC_by_way_SDEQ),
		.LH_by_way_SDEQ(DUT_LH_by_way_SDEQ),
		.GH_by_way_SDEQ(DUT_GH_by_way_SDEQ),
		.ras_index_by_way_SDEQ(DUT_ras_index_by_way_SDEQ),

	    // SDEQ feedback
		.stall_SDEQ(tb_stall_SDEQ),

	    // control
		.restart(tb_restart),
		.restart_PC(tb_restart_PC)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_stall_SENQ !== DUT_stall_SENQ) begin
			$display("TB ERROR: expected_stall_SENQ (%h) != DUT_stall_SENQ (%h)",
				expected_stall_SENQ, DUT_stall_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_valid_SDEQ !== DUT_valid_SDEQ) begin
			$display("TB ERROR: expected_valid_SDEQ (%h) != DUT_valid_SDEQ (%h)",
				expected_valid_SDEQ, DUT_valid_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_valid_by_way_SDEQ !== DUT_valid_by_way_SDEQ) begin
			$display("TB ERROR: expected_valid_by_way_SDEQ (%h) != DUT_valid_by_way_SDEQ (%h)",
				expected_valid_by_way_SDEQ, DUT_valid_by_way_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_uncompressed_by_way_SDEQ !== DUT_uncompressed_by_way_SDEQ) begin
			$display("TB ERROR: expected_uncompressed_by_way_SDEQ (%h) != DUT_uncompressed_by_way_SDEQ (%h)",
				expected_uncompressed_by_way_SDEQ, DUT_uncompressed_by_way_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_instr_2B_by_way_by_chunk_SDEQ !== DUT_instr_2B_by_way_by_chunk_SDEQ) begin
			$display("TB ERROR: expected_instr_2B_by_way_by_chunk_SDEQ (%h) != DUT_instr_2B_by_way_by_chunk_SDEQ (%h)",
				expected_instr_2B_by_way_by_chunk_SDEQ, DUT_instr_2B_by_way_by_chunk_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pred_info_by_way_by_chunk_SDEQ !== DUT_pred_info_by_way_by_chunk_SDEQ) begin
			$display("TB ERROR: expected_pred_info_by_way_by_chunk_SDEQ (%h) != DUT_pred_info_by_way_by_chunk_SDEQ (%h)",
				expected_pred_info_by_way_by_chunk_SDEQ, DUT_pred_info_by_way_by_chunk_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dep_pred_by_way_SDEQ !== DUT_dep_pred_by_way_SDEQ) begin
			$display("TB ERROR: expected_dep_pred_by_way_SDEQ (%h) != DUT_dep_pred_by_way_SDEQ (%h)",
				expected_dep_pred_by_way_SDEQ, DUT_dep_pred_by_way_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PC_by_way_SDEQ !== DUT_PC_by_way_SDEQ) begin
			$display("TB ERROR: expected_PC_by_way_SDEQ (%h) != DUT_PC_by_way_SDEQ (%h)",
				expected_PC_by_way_SDEQ, DUT_PC_by_way_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_LH_by_way_SDEQ !== DUT_LH_by_way_SDEQ) begin
			$display("TB ERROR: expected_LH_by_way_SDEQ (%h) != DUT_LH_by_way_SDEQ (%h)",
				expected_LH_by_way_SDEQ, DUT_LH_by_way_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_GH_by_way_SDEQ !== DUT_GH_by_way_SDEQ) begin
			$display("TB ERROR: expected_GH_by_way_SDEQ (%h) != DUT_GH_by_way_SDEQ (%h)",
				expected_GH_by_way_SDEQ, DUT_GH_by_way_SDEQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ras_index_by_way_SDEQ !== DUT_ras_index_by_way_SDEQ) begin
			$display("TB ERROR: expected_ras_index_by_way_SDEQ (%h) != DUT_ras_index_by_way_SDEQ (%h)",
				expected_ras_index_by_way_SDEQ, DUT_ras_index_by_way_SDEQ);
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
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'b00000000;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b00000000;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b0;
		expected_valid_by_way_SDEQ = 4'b0000;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h0, 8'h0,
			8'h0, 8'h0,
			8'h0, 8'h0,
			8'h0, 8'h0
		};
		expected_dep_pred_by_way_SDEQ = 4'b0000;
		expected_PC_by_way_SDEQ = {
			32'h80000000,
			32'h80000000,
			32'h80000000,
			32'h80000000
		};
		expected_LH_by_way_SDEQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_GH_by_way_SDEQ = {
			12'h0,
			12'h0,
			12'h0,
			12'h0
		};
		expected_ras_index_by_way_SDEQ = {
			3'h0,
			3'h0,
			3'h0,
			3'h0
		};
	    // SDEQ feedback
	    // control

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'b00000000;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b00000000;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b0;
		expected_valid_by_way_SDEQ = 4'b0000;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h0, 8'h0,
			8'h0, 8'h0,
			8'h0, 8'h0,
			8'h0, 8'h0
		};
		expected_dep_pred_by_way_SDEQ = 4'b0000;
		expected_PC_by_way_SDEQ = {
			32'h80000000,
			32'h80000000,
			32'h80000000,
			32'h80000000
		};
		expected_LH_by_way_SDEQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_GH_by_way_SDEQ = {
			12'h0,
			12'h0,
			12'h0,
			12'h0
		};
		expected_ras_index_by_way_SDEQ = {
			3'h0,
			3'h0,
			3'h0,
			3'h0
		};
	    // SDEQ feedback
	    // control

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ unC 0x80000000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h087, 2'b11,
			14'h096, 2'b11,
			14'h0a5, 2'b11,
			14'h0b4, 2'b11,
			14'h0c3, 2'b11,
			14'h0d2, 2'b11,
			14'h0e1, 2'b11,
			14'h0f0, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b10101010;
		tb_after_PC_SENQ = 32'h80000010;
		tb_LH_SENQ = 8'b10101010;
		tb_GH_SENQ = 12'b101010101010;
		tb_ras_index_SENQ = 3'b010;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b0;
		expected_valid_by_way_SDEQ = 4'b0000;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00,
			14'h0, 2'b00, 14'h0, 2'b00
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h0, 8'h0,
			8'h0, 8'h0,
			8'h0, 8'h0,
			8'h0, 8'h0
		};
		expected_dep_pred_by_way_SDEQ = 4'b0000;
		expected_PC_by_way_SDEQ = {
			32'h80000000,
			32'h80000000,
			32'h80000000,
			32'h80000000
		};
		expected_LH_by_way_SDEQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_GH_by_way_SDEQ = {
			12'h0,
			12'h0,
			12'h0,
			12'h0
		};
		expected_ras_index_by_way_SDEQ = {
			3'h0,
			3'h0,
			3'h0,
			3'h0
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ C 0x80000010, deQ unC 0x80000000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h00f, 2'b00,
			14'h01e, 2'b10,
			14'h02d, 2'b01,
			14'h03c, 2'b00,
			14'h04b, 2'b00,
			14'h05a, 2'b10,
			14'h069, 2'b01,
			14'h078, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0f,
			8'h1e,
			8'h2d,
			8'h3c,
			8'h4b,
			8'h5a,
			8'h69,
			8'h78
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b01010101;
		tb_after_PC_SENQ = 32'h80000020;
		tb_LH_SENQ = 8'b01010101;
		tb_GH_SENQ = 12'b010101010101;
		tb_ras_index_SENQ = 3'b101;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h087, 2'b11,
			14'h096, 2'b11,
			14'h0a5, 2'b11,
			14'h0b4, 2'b11,
			14'h0c3, 2'b11,
			14'h0d2, 2'b11,
			14'h0e1, 2'b11,
			14'h0f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b0000;
		expected_PC_by_way_SDEQ = {
			32'h8000000C,
			32'h80000008,
			32'h80000004,
			32'h80000000
		};
		expected_LH_by_way_SDEQ = {
			8'b10101010,
			8'b10101010,
			8'b10101010,
			8'b10101010
		};
		expected_GH_by_way_SDEQ = {
			12'b101010101010,
			12'b101010101010,
			12'b101010101010,
			12'b101010101010
		};
		expected_ras_index_by_way_SDEQ = {
			3'b010,
			3'b010,
			3'b010,
			3'b010
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ unC 0x80000020, deQ C 0x80000010 first half";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b01100110;
		tb_after_PC_SENQ = 32'h80000030;
		tb_LH_SENQ = 8'b01100110;
		tb_GH_SENQ = 12'b011001100110;
		tb_ras_index_SENQ = 3'b110;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h03c, 2'b00,
			14'h04b, 2'b00,
			14'h04b, 2'b00,
			14'h05a, 2'b10,
			14'h05a, 2'b10,
			14'h069, 2'b01,
			14'h069, 2'b01,
			14'h078, 2'b00
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h3c,
			8'h4b,
			8'h4b,
			8'h5a,
			8'h5a,
			8'h69,
			8'h69,
			8'h78
		};
		expected_dep_pred_by_way_SDEQ = 4'b0101;
		expected_PC_by_way_SDEQ = {
			32'h80000016,
			32'h80000014,
			32'h80000012,
			32'h80000010
		};
		expected_LH_by_way_SDEQ = {
			8'b01010101,
			8'b01010101,
			8'b01010101,
			8'b01010101
		};
		expected_GH_by_way_SDEQ = {
			12'b010101010101,
			12'b010101010101,
			12'b010101010101,
			12'b010101010101
		};
		expected_ras_index_by_way_SDEQ = {
			3'b101,
			3'b101,
			3'b101,
			3'b101
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ C 0x80000030, deQ C 0x80000010 second half";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h10f, 2'b10,
			14'h11e, 2'b00,
			14'h12d, 2'b00,
			14'h13c, 2'b01,
			14'h14b, 2'b01,
			14'h15a, 2'b10,
			14'h169, 2'b10,
			14'h178, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0f,
			8'h1e,
			8'h2d,
			8'h3c,
			8'h4b,
			8'h5a,
			8'h69,
			8'h78
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b10011001;
		tb_after_PC_SENQ = 32'h80000040;
		tb_LH_SENQ = 8'b10011001;
		tb_GH_SENQ = 12'b100110011001;
		tb_ras_index_SENQ = 3'b001;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h1f0, 2'b11,
			14'h00f, 2'b00,
			14'h00f, 2'b00,
			14'h01e, 2'b10,
			14'h01e, 2'b10,
			14'h02d, 2'b01,
			14'h02d, 2'b01,
			14'h03c, 2'b00
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'hf0,
			8'h0f,
			8'h0f,
			8'h1e,
			8'h1e,
			8'h2d,
			8'h2d,
			8'h3c
		};
		expected_dep_pred_by_way_SDEQ = 4'b0101;
		expected_PC_by_way_SDEQ = {
			32'h8000001e,
			32'h8000001c,
			32'h8000001a,
			32'h80000018
		};
		expected_LH_by_way_SDEQ = {
			8'b01010101,
			8'b01010101,
			8'b01010101,
			8'b01010101
		};
		expected_GH_by_way_SDEQ = {
			12'b010101010101,
			12'b010101010101,
			12'b010101010101,
			12'b010101010101
		};
		expected_ras_index_by_way_SDEQ = {
			3'b101,
			3'b101,
			3'b101,
			3'b101
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ mixed 0:4 0x80000040, deQ stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b00111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h240, 2'b01,
			14'h231, 2'b11,
			14'h230, 2'b11,
			14'h220, 2'b10,
			14'h210, 2'b00,
			14'h200, 2'b01
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'hff,
			8'hff,
			8'h40,
			8'h31,
			8'h30,
			8'h20,
			8'h10,
			8'h00
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b00011111;
		tb_after_PC_SENQ = 32'h76543210;
		tb_LH_SENQ = 8'b11001100;
		tb_GH_SENQ = 12'b110011001100;
		tb_ras_index_SENQ = 3'b100;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b1;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ mixed 5:A0 0x76543210, deQ stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111110;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h2A0, 2'b11,
			14'h290, 2'b01,
			14'h280, 2'b01,
			14'h270, 2'b00,
			14'h261, 2'b10,
			14'h260, 2'b11,
			14'h250, 2'b10,
			14'h3ff, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'hA0,
			8'h90,
			8'h80,
			8'h70,
			8'h61,
			8'h60,
			8'h50,
			8'hff
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b11111111;
		tb_after_PC_SENQ = 32'h76543220;
		tb_LH_SENQ = 8'b00110011;
		tb_GH_SENQ = 12'b001100110011;
		tb_ras_index_SENQ = 3'b011;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b1;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ mixed A1:C 0x76543220, deQ stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b00011111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h2C1, 2'b00,
			14'h2C0, 2'b11,
			14'h2B1, 2'b00,
			14'h2B0, 2'b11,
			14'h2A1, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'hff,
			8'hff,
			8'hff,
			8'hC1,
			8'hC0,
			8'hB1,
			8'hB0,
			8'hA1
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b11100000;
		tb_after_PC_SENQ = 32'hfedcba90;
		tb_LH_SENQ = 8'b11110000;
		tb_GH_SENQ = 12'b000011110000;
		tb_ras_index_SENQ = 3'b000;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b1;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ mixed D0 0xfedcba90, deQ stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b10000000;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h2d0, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'hd0,
			8'hff,
			8'hff,
			8'hff,
			8'hff,
			8'hff,
			8'hff,
			8'hff
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b11111111;
		tb_after_PC_SENQ = 32'hfedcbaa0;
		tb_LH_SENQ = 8'b00001111;
		tb_GH_SENQ = 12'b111100001111;
		tb_ras_index_SENQ = 3'b111;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b1;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ mixed D1:F 0xfedcbaa0, deQ stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b00001111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h2f1, 2'b10,
			14'h2f0, 2'b11,
			14'h2e0, 2'b01,
			14'h2d1, 2'b01
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'hff,
			8'hff,
			8'hff,
			8'hff,
			8'hf1,
			8'hf0,
			8'he0,
			8'hd1
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b00000000;
		tb_after_PC_SENQ = 32'h90000000;
		tb_LH_SENQ = 8'b11011101;
		tb_GH_SENQ = 12'b110111011101;
		tb_ras_index_SENQ = 3'b101;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b1;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ mixed 10:14A 0x90000000, deQ stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h242, 2'b11,
			14'h232, 2'b00,
			14'h223, 2'b00,
			14'h222, 2'b11,
			14'h213, 2'b00,
			14'h212, 2'b11,
			14'h203, 2'b00,
			14'h202, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h42,
			8'h32,
			8'h23,
			8'h22,
			8'h13,
			8'h12,
			8'h03,
			8'h02
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b00010001;
		tb_after_PC_SENQ = 32'h90000010;
		tb_LH_SENQ = 8'b00010001;
		tb_GH_SENQ = 12'b000100010001;
		tb_ras_index_SENQ = 3'b001;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b1;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ stall (mixed 14B:19 0x90000010), deQ stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h292, 2'b01,
			14'h282, 2'b01,
			14'h273, 2'b11,
			14'h272, 2'b11,
			14'h262, 2'b00,
			14'h253, 2'b10,
			14'h252, 2'b11,
			14'h243, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h92,
			8'h82,
			8'h73,
			8'h72,
			8'h62,
			8'h53,
			8'h52,
			8'h43
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b01000100;
		tb_after_PC_SENQ = 32'h90000020;
		tb_LH_SENQ = 8'b01000100;
		tb_GH_SENQ = 12'b010001000100;
		tb_ras_index_SENQ = 3'b100;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b1;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b1;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ stall (mixed 14B:19 0x90000010), deQ unC 0x80000020";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h292, 2'b01,
			14'h282, 2'b01,
			14'h273, 2'b11,
			14'h272, 2'b11,
			14'h262, 2'b00,
			14'h253, 2'b10,
			14'h252, 2'b11,
			14'h243, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h92,
			8'h82,
			8'h73,
			8'h72,
			8'h62,
			8'h53,
			8'h52,
			8'h43
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b01000100;
		tb_after_PC_SENQ = 32'h90000020;
		tb_LH_SENQ = 8'b01000100;
		tb_GH_SENQ = 12'b010001000100;
		tb_ras_index_SENQ = 3'b100;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b1;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h187, 2'b11,
			14'h196, 2'b11,
			14'h1a5, 2'b11,
			14'h1b4, 2'b11,
			14'h1c3, 2'b11,
			14'h1d2, 2'b11,
			14'h1e1, 2'b11,
			14'h1f0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h87,
			8'h96,
			8'ha5,
			8'hb4,
			8'hc3,
			8'hd2,
			8'he1,
			8'hf0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1010;
		expected_PC_by_way_SDEQ = {
			32'h8000002c,
			32'h80000028,
			32'h80000024,
			32'h80000020
		};
		expected_LH_by_way_SDEQ = {
			8'b01100110,
			8'b01100110,
			8'b01100110,
			8'b01100110
		};
		expected_GH_by_way_SDEQ = {
			12'b011001100110,
			12'b011001100110,
			12'b011001100110,
			12'b011001100110
		};
		expected_ras_index_by_way_SDEQ = {
			3'b110,
			3'b110,
			3'b110,
			3'b110
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ mixed 14B:19 0x90000010, deQ C 0x80000030 first half";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b1;
		tb_valid_by_fetch_2B_SENQ = 8'b11111111;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h292, 2'b01,
			14'h282, 2'b01,
			14'h273, 2'b11,
			14'h272, 2'b11,
			14'h262, 2'b00,
			14'h253, 2'b10,
			14'h252, 2'b11,
			14'h243, 2'b11
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h92,
			8'h82,
			8'h73,
			8'h72,
			8'h62,
			8'h53,
			8'h52,
			8'h43
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'b01000100;
		tb_after_PC_SENQ = 32'h90000020;
		tb_LH_SENQ = 8'b01000100;
		tb_GH_SENQ = 12'b010001000100;
		tb_ras_index_SENQ = 3'b100;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h13c, 2'b01,
			14'h14b, 2'b01,
			14'h14b, 2'b01,
			14'h15a, 2'b10,
			14'h15a, 2'b10,
			14'h169, 2'b10,
			14'h169, 2'b10,
			14'h178, 2'b00
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h3c,
			8'h4b,
			8'h4b,
			8'h5a,
			8'h5a,
			8'h69,
			8'h69,
			8'h78
		};
		expected_dep_pred_by_way_SDEQ = 4'b1001;
		expected_PC_by_way_SDEQ = {
			32'h80000036,
			32'h80000034,
			32'h80000032,
			32'h80000030
		};
		expected_LH_by_way_SDEQ = {
			8'b10011001,
			8'b10011001,
			8'b10011001,
			8'b10011001
		};
		expected_GH_by_way_SDEQ = {
			12'b100110011001,
			12'b100110011001,
			12'b100110011001,
			12'b100110011001
		};
		expected_ras_index_by_way_SDEQ = {
			3'b001,
			3'b001,
			3'b001,
			3'b001
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ C 0x80000030 second half";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b1;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h200, 2'b01,
			14'h10f, 2'b10,
			14'h10f, 2'b10,
			14'h11e, 2'b00,
			14'h11e, 2'b00,
			14'h12d, 2'b00,
			14'h12d, 2'b00,
			14'h13c, 2'b01
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h00,
			8'h0f,
			8'h0f,
			8'h1e,
			8'h1e,
			8'h2d,
			8'h2d,
			8'h3c
		};
		expected_dep_pred_by_way_SDEQ = 4'b1001;
		expected_PC_by_way_SDEQ = {
			32'h8000003e,
			32'h8000003c,
			32'h8000003a,
			32'h80000038
		};
		expected_LH_by_way_SDEQ = {
			8'b10011001,
			8'b10011001,
			8'b10011001,
			8'b10011001
		};
		expected_GH_by_way_SDEQ = {
			12'b100110011001,
			12'b100110011001,
			12'b100110011001,
			12'b100110011001
		};
		expected_ras_index_by_way_SDEQ = {
			3'b001,
			3'b001,
			3'b001,
			3'b001
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ mixed 0:3 0x80000040";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h231, 2'b11,
			14'h230, 2'b11,
			14'h230, 2'b11,
			14'h220, 2'b10,
			14'h220, 2'b10,
			14'h210, 2'b00,
			14'h210, 2'b00,
			14'h200, 2'b01
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h31,
			8'h30,
			8'h30,
			8'h20,
			8'h20,
			8'h10,
			8'h10,
			8'h00
		};
		expected_dep_pred_by_way_SDEQ = 4'b1111;
		expected_PC_by_way_SDEQ = {
			32'h80000046,
			32'h80000044,
			32'h80000042,
			32'h80000040
		};
		expected_LH_by_way_SDEQ = {
			8'b11001100,
			8'b11001100,
			8'b11001100,
			8'b11001100
		};
		expected_GH_by_way_SDEQ = {
			12'b110011001100,
			12'b110011001100,
			12'b110011001100,
			12'b110011001100
		};
		expected_ras_index_by_way_SDEQ = {
			3'b100,
			3'b100,
			3'b100,
			3'b100
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ mixed 4:7 0x80000040, 0x76543210";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b0100;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h280, 2'b01,
			14'h270, 2'b00,
			14'h261, 2'b10,
			14'h260, 2'b11,
			14'h260, 2'b11,
			14'h250, 2'b10,
			14'h250, 2'b10,
			14'h240, 2'b01
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h80,
			8'h70,
			8'h61,
			8'h60,
			8'h60,
			8'h50,
			8'h50,
			8'h40
		};
		expected_dep_pred_by_way_SDEQ = 4'b1110;
		expected_PC_by_way_SDEQ = {
			32'h76543218,
			32'h76543214,
			32'h76543212,
			32'h8000004a
		};
		expected_LH_by_way_SDEQ = {
			8'b00110011,
			8'b00110011,
			8'b00110011,
			8'b11001100
		};
		expected_GH_by_way_SDEQ = {
			12'b001100110011,
			12'b001100110011,
			12'b001100110011,
			12'b110011001100
		};
		expected_ras_index_by_way_SDEQ = {
			3'b011,
			3'b011,
			3'b011,
			3'b100
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ mixed 8:B 0x76543210, 0x76543220";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1100;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h2B1, 2'b00,
			14'h2B0, 2'b11,
			14'h2A1, 2'b00,
			14'h2A0, 2'b11,
			14'h2A0, 2'b11,
			14'h290, 2'b01,
			14'h290, 2'b01,
			14'h280, 2'b01
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'hB1,
			8'hB0,
			8'hA1,
			8'hA0,
			8'hA0,
			8'h90,
			8'h90,
			8'h80
		};
		expected_dep_pred_by_way_SDEQ = 4'b0111;
		expected_PC_by_way_SDEQ = {
			32'h76543222,
			32'h7654321e,
			32'h7654321c,
			32'h7654321a
		};
		expected_LH_by_way_SDEQ = {
			8'b11110000,
			8'b11110000,
			8'b00110011,
			8'b00110011
		};
		expected_GH_by_way_SDEQ = {
			12'b000011110000,
			12'b000011110000,
			12'b001100110011,
			12'b001100110011
		};
		expected_ras_index_by_way_SDEQ = {
			3'b0000,
			3'b0000,
			3'b011,
			3'b011
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ mixed C 0x76543220";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b0001;
		expected_uncompressed_by_way_SDEQ = 4'b0001;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h2A1, 2'b00,
			14'h2A1, 2'b00,
			14'h2A1, 2'b00,
			14'h2A1, 2'b00,
			14'h2A1, 2'b00,
			14'h2A1, 2'b00,
			14'h2C1, 2'b00,
			14'h2C0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'hA1,
			8'hA1,
			8'hA1,
			8'hA1,
			8'hA1,
			8'hA1,
			8'hC1,
			8'hC0
		};
		expected_dep_pred_by_way_SDEQ = 4'b0000;
		expected_PC_by_way_SDEQ = {
			32'h76543220,
			32'h76543220,
			32'h76543220,
			32'h76543226
		};
		expected_LH_by_way_SDEQ = {
			8'b11110000,
			8'b11110000,
			8'b11110000,
			8'b11110000
		};
		expected_GH_by_way_SDEQ = {
			12'b000011110000,
			12'b000011110000,
			12'b000011110000,
			12'b000011110000
		};
		expected_ras_index_by_way_SDEQ = {
			3'b000,
			3'b000,
			3'b000,
			3'b000
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ mixed D:F 0xfedcba90, 0xfedcbaa0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b0111;
		expected_uncompressed_by_way_SDEQ = 4'b0101;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h3ff, 2'b11,
			14'h3ff, 2'b11,
			14'h2f1, 2'b10,
			14'h2f0, 2'b11,
			14'h2f0, 2'b11,
			14'h2e0, 2'b01,
			14'h2d1, 2'b01,
			14'h2d0, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'hff,
			8'hff,
			8'hf1,
			8'hf0,
			8'hf0,
			8'he0,
			8'hd1,
			8'hd0
		};
		expected_dep_pred_by_way_SDEQ = 4'b1001;
		expected_PC_by_way_SDEQ = {
			32'hfedcba90,
			32'hfedcbaa4,
			32'hfedcbaa2,
			32'hfedcba9e
		};
		expected_LH_by_way_SDEQ = {
			8'b00001111,
			8'b11011101,
			8'b11011101,
			8'b11011101
		};
		expected_GH_by_way_SDEQ = {
			12'b111100001111,
			12'b110111011101,
			12'b110111011101,
			12'b110111011101
		};
		expected_ras_index_by_way_SDEQ = {
			3'b111,
			3'b101,
			3'b101,
			3'b101
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ mixed 10:13 0x90000000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b0111;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h242, 2'b11,
			14'h232, 2'b00,
			14'h223, 2'b00,
			14'h222, 2'b11,
			14'h213, 2'b00,
			14'h212, 2'b11,
			14'h203, 2'b00,
			14'h202, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h42,
			8'h32,
			8'h23,
			8'h22,
			8'h13,
			8'h12,
			8'h03,
			8'h02
		};
		expected_dep_pred_by_way_SDEQ = 4'b0101;
		expected_PC_by_way_SDEQ = {
			32'h9000000c,
			32'h90000008,
			32'h90000004,
			32'h90000000
		};
		expected_LH_by_way_SDEQ = {
			8'b00010001,
			8'b00010001,
			8'b00010001,
			8'b00010001
		};
		expected_GH_by_way_SDEQ = {
			12'b000100010001,
			12'b000100010001,
			12'b000100010001,
			12'b000100010001
		};
		expected_ras_index_by_way_SDEQ = {
			3'b001,
			3'b001,
			3'b001,
			3'b001
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ mixed 14:17 0x90000000, 0x90000010";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b0;
		tb_restart_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b1111;
		expected_uncompressed_by_way_SDEQ = 4'b1011;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h273, 2'b11,
			14'h272, 2'b11,
			14'h272, 2'b11,
			14'h262, 2'b00,
			14'h253, 2'b10,
			14'h252, 2'b11,
			14'h243, 2'b11,
			14'h242, 2'b11
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h73,
			8'h72,
			8'h72,
			8'h62,
			8'h53,
			8'h52,
			8'h43,
			8'h42
		};
		expected_dep_pred_by_way_SDEQ = 4'b0000;
		expected_PC_by_way_SDEQ = {
			32'h90000018,
			32'h90000016,
			32'h90000012,
			32'h9000000e
		};
		expected_LH_by_way_SDEQ = {
			8'b01000100,
			8'b01000100,
			8'b01000100,
			8'b01000100
		};
		expected_GH_by_way_SDEQ = {
			12'b010001000100,
			12'b010001000100,
			12'b010001000100,
			12'b010001000100
		};
		expected_ras_index_by_way_SDEQ = {
			3'b100,
			3'b100,
			3'b100,
			3'b100
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "restart + enQ NOP, deQ mixed 18:19 0x90000010";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b1;
		tb_restart_PC = 32'ha0000000;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b1;
		expected_valid_by_way_SDEQ = 4'b0011;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h243, 2'b11,
			14'h243, 2'b11,
			14'h243, 2'b11,
			14'h243, 2'b11,
			14'h243, 2'b11,
			14'h292, 2'b01,
			14'h292, 2'b01,
			14'h282, 2'b01
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h43,
			8'h43,
			8'h43,
			8'h43,
			8'h43,
			8'h92,
			8'h92,
			8'h82
		};
		expected_dep_pred_by_way_SDEQ = 4'b0001;
		expected_PC_by_way_SDEQ = {
			32'h90000010,
			32'h90000010,
			32'h9000001e,
			32'h9000001c
		};
		expected_LH_by_way_SDEQ = {
			8'b01000100,
			8'b01000100,
			8'b01000100,
			8'b01000100
		};
		expected_GH_by_way_SDEQ = {
			12'b010001000100,
			12'b010001000100,
			12'b010001000100,
			12'b010001000100
		};
		expected_ras_index_by_way_SDEQ = {
			3'b100,
			3'b100,
			3'b100,
			3'b100
		};
	    // SDEQ feedback
	    // control

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "enQ NOP, deQ NOP";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // SENQ stage
		tb_valid_SENQ = 1'b0;
		tb_valid_by_fetch_2B_SENQ = 8'h0;
		tb_instr_2B_by_fetch_2B_SENQ = {
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00,
			14'h0, 2'b00
		};
		tb_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		tb_dep_pred_by_fetch_2B_SENQ = 8'h0;
		tb_after_PC_SENQ = 32'h0;
		tb_LH_SENQ = 8'h0;
		tb_GH_SENQ = 12'h0;
		tb_ras_index_SENQ = 3'h0;
	    // SENQ feedback
	    // SDEQ stage
	    // SDEQ feedback
		tb_stall_SDEQ = 1'b0;
	    // control
		tb_restart = 1'b1;
		tb_restart_PC = 32'ha0000000;

		@(negedge CLK);

		// outputs:

	    // SENQ stage
	    // SENQ feedback
		expected_stall_SENQ = 1'b0;
	    // SDEQ stage
		expected_valid_SDEQ = 1'b0;
		expected_valid_by_way_SDEQ = 4'b0000;
		expected_uncompressed_by_way_SDEQ = 4'b0000;
		expected_instr_2B_by_way_by_chunk_SDEQ = {
			14'h0, 2'b0,
			14'h0, 2'b0,
			14'h0, 2'b0,
			14'h0, 2'b0,
			14'h0, 2'b0,
			14'h0, 2'b0,
			14'h0, 2'b0,
			14'h0, 2'b0
		};
		expected_pred_info_by_way_by_chunk_SDEQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_dep_pred_by_way_SDEQ = 4'b0000;
		expected_PC_by_way_SDEQ = {
			32'ha0000000,
			32'ha0000000,
			32'ha0000000,
			32'ha0000000
		};
		expected_LH_by_way_SDEQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_GH_by_way_SDEQ = {
			12'h0,
			12'h0,
			12'h0,
			12'h0
		};
		expected_ras_index_by_way_SDEQ = {
			3'h0,
			3'h0,
			3'h0,
			3'h0
		};
	    // SDEQ feedback
	    // control

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
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule