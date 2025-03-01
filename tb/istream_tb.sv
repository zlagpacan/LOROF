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
	logic [3:0][1:0][31:0] DUT_instr_2B_by_way_by_chunk_SDEQ, expected_instr_2B_by_way_by_chunk_SDEQ;
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

	istream #(.INIT_PC(32'h80000000)) DUT (
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
		expected_dep_pred_by_way_SDEQ = 8'b00000000;
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
		expected_dep_pred_by_way_SDEQ = 8'b00000000;
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
		expected_dep_pred_by_way_SDEQ = 8'b00000000;
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