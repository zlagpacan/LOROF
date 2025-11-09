/*
    Filename: sysu_dq_tb.sv
    Author: zlagpacan
    Description: Testbench for sysu_dq module. 
    Spec: LOROF/spec/design/sysu_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module sysu_dq_tb #(
	parameter STAMOFU_DQ_ENTRIES = 4
) ();

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

    // op dispatch by way
	logic [3:0] tb_dispatch_attempt_by_way;
	logic [3:0] tb_dispatch_valid_by_way;
	logic [3:0][3:0] tb_dispatch_op_by_way;
	logic [3:0][11:0] tb_dispatch_imm12_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0] tb_dispatch_A_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_way;
	logic [3:0] tb_dispatch_B_ready_by_way;
	logic [3:0] tb_dispatch_B_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // op launch to sysu
	logic DUT_sysu_launch_valid, expected_sysu_launch_valid;
	logic DUT_sysu_launch_killed, expected_sysu_launch_killed;
	logic [3:0] DUT_sysu_launch_op, expected_sysu_launch_op;
	logic [11:0] DUT_sysu_launch_imm12, expected_sysu_launch_imm12;
	logic [LOG_PR_COUNT-1:0] DUT_sysu_launch_A_PR, expected_sysu_launch_A_PR;
	logic DUT_sysu_launch_A_is_zero, expected_sysu_launch_A_is_zero;
	logic [LOG_PR_COUNT-1:0] DUT_sysu_launch_B_PR, expected_sysu_launch_B_PR;
	logic DUT_sysu_launch_B_is_zero, expected_sysu_launch_B_is_zero;
	logic [LOG_PR_COUNT-1:0] DUT_sysu_launch_dest_PR, expected_sysu_launch_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_sysu_launch_ROB_index, expected_sysu_launch_ROB_index;

    // sysu launch feedback
	logic tb_sysu_launch_ready;

    // ROB kill
	logic tb_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	sysu_dq #(
		.SYSU_DQ_ENTRIES(SYSU_DQ_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op dispatch by way
		.dispatch_attempt_by_way(tb_dispatch_attempt_by_way),
		.dispatch_valid_by_way(tb_dispatch_valid_by_way),
		.dispatch_op_by_way(tb_dispatch_op_by_way),
		.dispatch_imm12_by_way(tb_dispatch_imm12_by_way),
		.dispatch_A_PR_by_way(tb_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_A_is_zero_by_way(tb_dispatch_A_is_zero_by_way),
		.dispatch_B_PR_by_way(tb_dispatch_B_PR_by_way),
		.dispatch_B_ready_by_way(tb_dispatch_B_ready_by_way),
		.dispatch_B_is_zero_by_way(tb_dispatch_B_is_zero_by_way),
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // op dispatch feedback
		.dispatch_ack_by_way(DUT_dispatch_ack_by_way),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // op launch to sysu
		.sysu_launch_valid(DUT_sysu_launch_valid),
		.sysu_launch_killed(DUT_sysu_launch_killed),
		.sysu_launch_op(DUT_sysu_launch_op),
		.sysu_launch_imm12(DUT_sysu_launch_imm12),
		.sysu_launch_A_PR(DUT_sysu_launch_A_PR),
		.sysu_launch_A_is_zero(DUT_sysu_launch_A_is_zero),
		.sysu_launch_B_PR(DUT_sysu_launch_B_PR),
		.sysu_launch_B_is_zero(DUT_sysu_launch_B_is_zero),
		.sysu_launch_dest_PR(DUT_sysu_launch_dest_PR),
		.sysu_launch_ROB_index(DUT_sysu_launch_ROB_index),

	    // sysu launch feedback
		.sysu_launch_ready(tb_sysu_launch_ready),

	    // ROB kill
		.rob_kill_valid(tb_rob_kill_valid),
		.rob_kill_abs_head_index(tb_rob_kill_abs_head_index),
		.rob_kill_rel_kill_younger_index(tb_rob_kill_rel_kill_younger_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_dispatch_ack_by_way !== DUT_dispatch_ack_by_way) begin
			$display("TB ERROR: expected_dispatch_ack_by_way (%h) != DUT_dispatch_ack_by_way (%h)",
				expected_dispatch_ack_by_way, DUT_dispatch_ack_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_valid !== DUT_sysu_launch_valid) begin
			$display("TB ERROR: expected_sysu_launch_valid (%h) != DUT_sysu_launch_valid (%h)",
				expected_sysu_launch_valid, DUT_sysu_launch_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_killed !== DUT_sysu_launch_killed) begin
			$display("TB ERROR: expected_sysu_launch_killed (%h) != DUT_sysu_launch_killed (%h)",
				expected_sysu_launch_killed, DUT_sysu_launch_killed);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_op !== DUT_sysu_launch_op) begin
			$display("TB ERROR: expected_sysu_launch_op (%h) != DUT_sysu_launch_op (%h)",
				expected_sysu_launch_op, DUT_sysu_launch_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_imm12 !== DUT_sysu_launch_imm12) begin
			$display("TB ERROR: expected_sysu_launch_imm12 (%h) != DUT_sysu_launch_imm12 (%h)",
				expected_sysu_launch_imm12, DUT_sysu_launch_imm12);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_A_PR !== DUT_sysu_launch_A_PR) begin
			$display("TB ERROR: expected_sysu_launch_A_PR (%h) != DUT_sysu_launch_A_PR (%h)",
				expected_sysu_launch_A_PR, DUT_sysu_launch_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_A_is_zero !== DUT_sysu_launch_A_is_zero) begin
			$display("TB ERROR: expected_sysu_launch_A_is_zero (%h) != DUT_sysu_launch_A_is_zero (%h)",
				expected_sysu_launch_A_is_zero, DUT_sysu_launch_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_B_PR !== DUT_sysu_launch_B_PR) begin
			$display("TB ERROR: expected_sysu_launch_B_PR (%h) != DUT_sysu_launch_B_PR (%h)",
				expected_sysu_launch_B_PR, DUT_sysu_launch_B_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_B_is_zero !== DUT_sysu_launch_B_is_zero) begin
			$display("TB ERROR: expected_sysu_launch_B_is_zero (%h) != DUT_sysu_launch_B_is_zero (%h)",
				expected_sysu_launch_B_is_zero, DUT_sysu_launch_B_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_dest_PR !== DUT_sysu_launch_dest_PR) begin
			$display("TB ERROR: expected_sysu_launch_dest_PR (%h) != DUT_sysu_launch_dest_PR (%h)",
				expected_sysu_launch_dest_PR, DUT_sysu_launch_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sysu_launch_ROB_index !== DUT_sysu_launch_ROB_index) begin
			$display("TB ERROR: expected_sysu_launch_ROB_index (%h) != DUT_sysu_launch_ROB_index (%h)",
				expected_sysu_launch_ROB_index, DUT_sysu_launch_ROB_index);
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
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h000, 12'h000, 12'h000};
		tb_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h00, 5'h00, 5'h00, 5'h00};
	    // op launch to sysu
	    // sysu launch feedback
		tb_sysu_launch_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op launch to sysu
		expected_sysu_launch_valid = 1'b0;
		expected_sysu_launch_killed = 1'b0;
		expected_sysu_launch_op = 4'b0000;
		expected_sysu_launch_imm12 = 12'h000;
		expected_sysu_launch_A_PR = 7'h00;
		expected_sysu_launch_A_is_zero = 1'b0;
		expected_sysu_launch_B_PR = 7'h00;
		expected_sysu_launch_B_is_zero = 1'b0;
		expected_sysu_launch_dest_PR = 7'h00;
		expected_sysu_launch_ROB_index = 7'h00;
	    // sysu launch feedback
	    // ROB kill

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h000, 12'h000, 12'h000};
		tb_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h00, 5'h00, 5'h00, 5'h00};
	    // op launch to sysu
	    // sysu launch feedback
		tb_sysu_launch_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op launch to sysu
		expected_sysu_launch_valid = 1'b0;
		expected_sysu_launch_killed = 1'b0;
		expected_sysu_launch_op = 4'b0000;
		expected_sysu_launch_imm12 = 12'h000;
		expected_sysu_launch_A_PR = 7'h00;
		expected_sysu_launch_A_is_zero = 1'b0;
		expected_sysu_launch_B_PR = 7'h00;
		expected_sysu_launch_B_is_zero = 1'b0;
		expected_sysu_launch_dest_PR = 7'h00;
		expected_sysu_launch_ROB_index = 7'h00;
	    // sysu launch feedback
	    // ROB kill

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
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h000, 12'h000, 12'h000};
		tb_dispatch_A_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h00, 7'h00, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h00, 5'h00, 5'h00, 5'h00};
	    // op launch to sysu
	    // sysu launch feedback
		tb_sysu_launch_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h00;
		tb_rob_kill_rel_kill_younger_index = 7'h00;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op launch to sysu
		expected_sysu_launch_valid = 1'b0;
		expected_sysu_launch_killed = 1'b0;
		expected_sysu_launch_op = 4'b0000;
		expected_sysu_launch_imm12 = 12'h000;
		expected_sysu_launch_A_PR = 7'h00;
		expected_sysu_launch_A_is_zero = 1'b0;
		expected_sysu_launch_B_PR = 7'h00;
		expected_sysu_launch_B_is_zero = 1'b0;
		expected_sysu_launch_dest_PR = 7'h00;
		expected_sysu_launch_ROB_index = 7'h00;
	    // sysu launch feedback
	    // ROB kill

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