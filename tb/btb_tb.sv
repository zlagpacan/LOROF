/*
    Filename: btb_tb.sv
    Author: zlagpacan
    Description: Testbench for btb module. 
    Spec: LOROF/spec/design/btb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb_tb ();

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


    // REQ stage
	logic tb_valid_REQ;
	logic [31:0] tb_full_PC_REQ;
	logic [ASID_WIDTH-1:0] tb_ASID_REQ;

    // RESP stage
	logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0] DUT_hit_by_instr_RESP, expected_hit_by_instr_RESP;
	logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_PRED_INFO_WIDTH-1:0] DUT_pred_info_by_instr_RESP, expected_pred_info_by_instr_RESP;
	logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0] DUT_pred_lru_by_instr_RESP, expected_pred_lru_by_instr_RESP;
	logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_TARGET_WIDTH-1:0] DUT_target_by_instr_RESP, expected_target_by_instr_RESP;

    // Update 0
	logic tb_update0_valid;
	logic [31:0] tb_update0_start_full_PC;

    // Update 1
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_update1_pred_info;
	logic tb_update1_pred_lru;
	logic [31:0] tb_update1_target_full_PC;

    // ----------------------------------------------------------------
    // DUT instantiation:

	btb #(
		.BTB_NWAY_ENTRIES(1024)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // REQ stage
		.valid_REQ(tb_valid_REQ),
		.full_PC_REQ(tb_full_PC_REQ),
		.ASID_REQ(tb_ASID_REQ),

	    // RESP stage
		.hit_by_instr_RESP(DUT_hit_by_instr_RESP),
		.pred_info_by_instr_RESP(DUT_pred_info_by_instr_RESP),
		.pred_lru_by_instr_RESP(DUT_pred_lru_by_instr_RESP),
		.target_by_instr_RESP(DUT_target_by_instr_RESP),

	    // Update 0
		.update0_valid(tb_update0_valid),
		.update0_start_full_PC(tb_update0_start_full_PC),

	    // Update 1
		.update1_pred_info(tb_update1_pred_info),
		.update1_pred_lru(tb_update1_pred_lru),
		.update1_target_full_PC(tb_update1_target_full_PC)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_hit_by_instr_RESP !== DUT_hit_by_instr_RESP) begin
			$display("TB ERROR: expected_hit_by_instr_RESP (%h) != DUT_hit_by_instr_RESP (%h)",
				expected_hit_by_instr_RESP, DUT_hit_by_instr_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pred_info_by_instr_RESP !== DUT_pred_info_by_instr_RESP) begin
			$display("TB ERROR: expected_pred_info_by_instr_RESP (%h) != DUT_pred_info_by_instr_RESP (%h)",
				expected_pred_info_by_instr_RESP, DUT_pred_info_by_instr_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pred_lru_by_instr_RESP !== DUT_pred_lru_by_instr_RESP) begin
			$display("TB ERROR: expected_pred_lru_by_instr_RESP (%h) != DUT_pred_lru_by_instr_RESP (%h)",
				expected_pred_lru_by_instr_RESP, DUT_pred_lru_by_instr_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_target_by_instr_RESP !== DUT_target_by_instr_RESP) begin
			$display("TB ERROR: expected_target_by_instr_RESP (%h) != DUT_target_by_instr_RESP (%h)",
				expected_target_by_instr_RESP, DUT_target_by_instr_RESP);
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
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = 32'h0;
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
	    // Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_hit_by_instr_RESP = {16{1'b1}};
		expected_pred_info_by_instr_RESP = {16{8'h0}};
		expected_pred_lru_by_instr_RESP = {16{1'b0}};
		expected_target_by_instr_RESP = {16{14'h0}};
	    // Update 0
	    // Update 1

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = 32'h0;
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
	    // Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_hit_by_instr_RESP = {16{1'b1}};
		expected_pred_info_by_instr_RESP = {16{8'h0}};
		expected_pred_lru_by_instr_RESP = {16{1'b0}};
		expected_target_by_instr_RESP = {16{14'h0}};
	    // Update 0
	    // Update 1

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
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = 32'h0;
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
	    // Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = 32'h0;

		@(negedge CLK);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_hit_by_instr_RESP = {16{1'b1}};
		expected_pred_info_by_instr_RESP = {16{8'h0}};
		expected_pred_lru_by_instr_RESP = {16{1'b0}};
		expected_target_by_instr_RESP = {16{14'h0}};
	    // Update 0
	    // Update 1

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