/*
    Filename: alu_imm_ldu_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_imm_ldu_iq module. 
    Spec: LOROF/spec/design/alu_imm_ldu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_ldu_iq_tb ();

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
	logic [3:0] tb_dispatch_valid_alu_imm_by_way;
	logic [3:0] tb_dispatch_valid_ldu_by_way;
	logic [3:0][3:0] tb_dispatch_op_by_way;
	logic [3:0][11:0] tb_dispatch_imm12_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0] tb_dispatch_A_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // pipeline feedback
	logic tb_alu_imm_pipeline_ready;
	logic tb_ldu_pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // op issue to ALU Reg-Imm Pipeline
	logic DUT_issue_alu_imm_valid, expected_issue_alu_imm_valid;
	logic [3:0] DUT_issue_alu_imm_op, expected_issue_alu_imm_op;
	logic [11:0] DUT_issue_alu_imm_imm12, expected_issue_alu_imm_imm12;
	logic DUT_issue_alu_imm_A_forward, expected_issue_alu_imm_A_forward;
	logic DUT_issue_alu_imm_A_is_zero, expected_issue_alu_imm_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_alu_imm_A_bank, expected_issue_alu_imm_A_bank;
	logic [LOG_PR_COUNT-1:0] DUT_issue_alu_imm_dest_PR, expected_issue_alu_imm_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_alu_imm_ROB_index, expected_issue_alu_imm_ROB_index;

    // ALU Reg-Imm Pipeline reg read req to PRF
	logic DUT_PRF_alu_imm_req_A_valid, expected_PRF_alu_imm_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_alu_imm_req_A_PR, expected_PRF_alu_imm_req_A_PR;

    // op issue to LDU Pipeline
	logic DUT_issue_ldu_valid, expected_issue_ldu_valid;
	logic [3:0] DUT_issue_ldu_op, expected_issue_ldu_op;
	logic [11:0] DUT_issue_ldu_imm12, expected_issue_ldu_imm12;
	logic DUT_issue_ldu_A_forward, expected_issue_ldu_A_forward;
	logic DUT_issue_ldu_A_is_zero, expected_issue_ldu_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_ldu_A_bank, expected_issue_ldu_A_bank;
	logic [LOG_PR_COUNT-1:0] DUT_issue_ldu_dest_PR, expected_issue_ldu_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_ldu_ROB_index, expected_issue_ldu_ROB_index;

    // LDU Pipeline reg read req to PRF
	logic DUT_PRF_ldu_req_A_valid, expected_PRF_ldu_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_ldu_req_A_PR, expected_PRF_ldu_req_A_PR;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_imm_ldu_iq #(
		.ALU_IMM_LDU_IQ_ENTRIES(8)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op dispatch by way
		.dispatch_attempt_by_way(tb_dispatch_attempt_by_way),
		.dispatch_valid_alu_imm_by_way(tb_dispatch_valid_alu_imm_by_way),
		.dispatch_valid_ldu_by_way(tb_dispatch_valid_ldu_by_way),
		.dispatch_op_by_way(tb_dispatch_op_by_way),
		.dispatch_imm12_by_way(tb_dispatch_imm12_by_way),
		.dispatch_A_PR_by_way(tb_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_A_is_zero_by_way(tb_dispatch_A_is_zero_by_way),
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // op dispatch feedback
		.dispatch_ack_by_way(DUT_dispatch_ack_by_way),

	    // pipeline feedback
		.alu_imm_pipeline_ready(tb_alu_imm_pipeline_ready),
		.ldu_pipeline_ready(tb_ldu_pipeline_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // op issue to ALU Reg-Imm Pipeline
		.issue_alu_imm_valid(DUT_issue_alu_imm_valid),
		.issue_alu_imm_op(DUT_issue_alu_imm_op),
		.issue_alu_imm_imm12(DUT_issue_alu_imm_imm12),
		.issue_alu_imm_A_forward(DUT_issue_alu_imm_A_forward),
		.issue_alu_imm_A_is_zero(DUT_issue_alu_imm_A_is_zero),
		.issue_alu_imm_A_bank(DUT_issue_alu_imm_A_bank),
		.issue_alu_imm_dest_PR(DUT_issue_alu_imm_dest_PR),
		.issue_alu_imm_ROB_index(DUT_issue_alu_imm_ROB_index),

	    // ALU Reg-Imm Pipeline reg read req to PRF
		.PRF_alu_imm_req_A_valid(DUT_PRF_alu_imm_req_A_valid),
		.PRF_alu_imm_req_A_PR(DUT_PRF_alu_imm_req_A_PR),

	    // op issue to LDU Pipeline
		.issue_ldu_valid(DUT_issue_ldu_valid),
		.issue_ldu_op(DUT_issue_ldu_op),
		.issue_ldu_imm12(DUT_issue_ldu_imm12),
		.issue_ldu_A_forward(DUT_issue_ldu_A_forward),
		.issue_ldu_A_is_zero(DUT_issue_ldu_A_is_zero),
		.issue_ldu_A_bank(DUT_issue_ldu_A_bank),
		.issue_ldu_dest_PR(DUT_issue_ldu_dest_PR),
		.issue_ldu_ROB_index(DUT_issue_ldu_ROB_index),

	    // LDU Pipeline reg read req to PRF
		.PRF_ldu_req_A_valid(DUT_PRF_ldu_req_A_valid),
		.PRF_ldu_req_A_PR(DUT_PRF_ldu_req_A_PR)
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

		if (expected_issue_alu_imm_valid !== DUT_issue_alu_imm_valid) begin
			$display("TB ERROR: expected_issue_alu_imm_valid (%h) != DUT_issue_alu_imm_valid (%h)",
				expected_issue_alu_imm_valid, DUT_issue_alu_imm_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_imm_op !== DUT_issue_alu_imm_op) begin
			$display("TB ERROR: expected_issue_alu_imm_op (%h) != DUT_issue_alu_imm_op (%h)",
				expected_issue_alu_imm_op, DUT_issue_alu_imm_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_imm_imm12 !== DUT_issue_alu_imm_imm12) begin
			$display("TB ERROR: expected_issue_alu_imm_imm12 (%h) != DUT_issue_alu_imm_imm12 (%h)",
				expected_issue_alu_imm_imm12, DUT_issue_alu_imm_imm12);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_imm_A_forward !== DUT_issue_alu_imm_A_forward) begin
			$display("TB ERROR: expected_issue_alu_imm_A_forward (%h) != DUT_issue_alu_imm_A_forward (%h)",
				expected_issue_alu_imm_A_forward, DUT_issue_alu_imm_A_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_imm_A_is_zero !== DUT_issue_alu_imm_A_is_zero) begin
			$display("TB ERROR: expected_issue_alu_imm_A_is_zero (%h) != DUT_issue_alu_imm_A_is_zero (%h)",
				expected_issue_alu_imm_A_is_zero, DUT_issue_alu_imm_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_imm_A_bank !== DUT_issue_alu_imm_A_bank) begin
			$display("TB ERROR: expected_issue_alu_imm_A_bank (%h) != DUT_issue_alu_imm_A_bank (%h)",
				expected_issue_alu_imm_A_bank, DUT_issue_alu_imm_A_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_imm_dest_PR !== DUT_issue_alu_imm_dest_PR) begin
			$display("TB ERROR: expected_issue_alu_imm_dest_PR (%h) != DUT_issue_alu_imm_dest_PR (%h)",
				expected_issue_alu_imm_dest_PR, DUT_issue_alu_imm_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_alu_imm_ROB_index !== DUT_issue_alu_imm_ROB_index) begin
			$display("TB ERROR: expected_issue_alu_imm_ROB_index (%h) != DUT_issue_alu_imm_ROB_index (%h)",
				expected_issue_alu_imm_ROB_index, DUT_issue_alu_imm_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_alu_imm_req_A_valid !== DUT_PRF_alu_imm_req_A_valid) begin
			$display("TB ERROR: expected_PRF_alu_imm_req_A_valid (%h) != DUT_PRF_alu_imm_req_A_valid (%h)",
				expected_PRF_alu_imm_req_A_valid, DUT_PRF_alu_imm_req_A_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_alu_imm_req_A_PR !== DUT_PRF_alu_imm_req_A_PR) begin
			$display("TB ERROR: expected_PRF_alu_imm_req_A_PR (%h) != DUT_PRF_alu_imm_req_A_PR (%h)",
				expected_PRF_alu_imm_req_A_PR, DUT_PRF_alu_imm_req_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_valid !== DUT_issue_ldu_valid) begin
			$display("TB ERROR: expected_issue_ldu_valid (%h) != DUT_issue_ldu_valid (%h)",
				expected_issue_ldu_valid, DUT_issue_ldu_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_op !== DUT_issue_ldu_op) begin
			$display("TB ERROR: expected_issue_ldu_op (%h) != DUT_issue_ldu_op (%h)",
				expected_issue_ldu_op, DUT_issue_ldu_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_imm12 !== DUT_issue_ldu_imm12) begin
			$display("TB ERROR: expected_issue_ldu_imm12 (%h) != DUT_issue_ldu_imm12 (%h)",
				expected_issue_ldu_imm12, DUT_issue_ldu_imm12);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_A_forward !== DUT_issue_ldu_A_forward) begin
			$display("TB ERROR: expected_issue_ldu_A_forward (%h) != DUT_issue_ldu_A_forward (%h)",
				expected_issue_ldu_A_forward, DUT_issue_ldu_A_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_A_is_zero !== DUT_issue_ldu_A_is_zero) begin
			$display("TB ERROR: expected_issue_ldu_A_is_zero (%h) != DUT_issue_ldu_A_is_zero (%h)",
				expected_issue_ldu_A_is_zero, DUT_issue_ldu_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_A_bank !== DUT_issue_ldu_A_bank) begin
			$display("TB ERROR: expected_issue_ldu_A_bank (%h) != DUT_issue_ldu_A_bank (%h)",
				expected_issue_ldu_A_bank, DUT_issue_ldu_A_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_dest_PR !== DUT_issue_ldu_dest_PR) begin
			$display("TB ERROR: expected_issue_ldu_dest_PR (%h) != DUT_issue_ldu_dest_PR (%h)",
				expected_issue_ldu_dest_PR, DUT_issue_ldu_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ldu_ROB_index !== DUT_issue_ldu_ROB_index) begin
			$display("TB ERROR: expected_issue_ldu_ROB_index (%h) != DUT_issue_ldu_ROB_index (%h)",
				expected_issue_ldu_ROB_index, DUT_issue_ldu_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_ldu_req_A_valid !== DUT_PRF_ldu_req_A_valid) begin
			$display("TB ERROR: expected_PRF_ldu_req_A_valid (%h) != DUT_PRF_ldu_req_A_valid (%h)",
				expected_PRF_ldu_req_A_valid, DUT_PRF_ldu_req_A_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_ldu_req_A_PR !== DUT_PRF_ldu_req_A_PR) begin
			$display("TB ERROR: expected_PRF_ldu_req_A_PR (%h) != DUT_PRF_ldu_req_A_PR (%h)",
				expected_PRF_ldu_req_A_PR, DUT_PRF_ldu_req_A_PR);
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
		tb_dispatch_attempt_by_way = '0;
		tb_dispatch_valid_alu_imm_by_way = '0;
		tb_dispatch_valid_ldu_by_way = '0;
		tb_dispatch_op_by_way = '0;
		tb_dispatch_imm12_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_is_zero_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // pipeline feedback
		tb_alu_imm_pipeline_ready = 1'b1;
		tb_ldu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // op issue to ALU Reg-Imm Pipeline
	    // ALU Reg-Imm Pipeline reg read req to PRF
	    // op issue to LDU Pipeline
	    // LDU Pipeline reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = '0;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Imm Pipeline
		expected_issue_alu_imm_valid = '0;
		expected_issue_alu_imm_op = '0;
		expected_issue_alu_imm_imm12 = '0;
		expected_issue_alu_imm_A_forward = '0;
		expected_issue_alu_imm_A_is_zero = '0;
		expected_issue_alu_imm_A_bank = '0;
		expected_issue_alu_imm_dest_PR = '0;
		expected_issue_alu_imm_ROB_index = '0;
	    // ALU Reg-Imm Pipeline reg read req to PRF
		expected_PRF_alu_imm_req_A_valid = '0;
		expected_PRF_alu_imm_req_A_PR = '0;
	    // op issue to LDU Pipeline
		expected_issue_ldu_valid = '0;
		expected_issue_ldu_op = '0;
		expected_issue_ldu_imm12 = '0;
		expected_issue_ldu_A_forward = '0;
		expected_issue_ldu_A_is_zero = '0;
		expected_issue_ldu_A_bank = '0;
		expected_issue_ldu_dest_PR = '0;
		expected_issue_ldu_ROB_index = '0;
	    // LDU Pipeline reg read req to PRF
		expected_PRF_ldu_req_A_valid = '0;
		expected_PRF_ldu_req_A_PR = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = '0;
		tb_dispatch_valid_alu_imm_by_way = '0;
		tb_dispatch_valid_ldu_by_way = '0;
		tb_dispatch_op_by_way = '0;
		tb_dispatch_imm12_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_is_zero_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // pipeline feedback
		tb_alu_imm_pipeline_ready = 1'b1;
		tb_ldu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // op issue to ALU Reg-Imm Pipeline
	    // ALU Reg-Imm Pipeline reg read req to PRF
	    // op issue to LDU Pipeline
	    // LDU Pipeline reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = '0;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Imm Pipeline
		expected_issue_alu_imm_valid = '0;
		expected_issue_alu_imm_op = '0;
		expected_issue_alu_imm_imm12 = '0;
		expected_issue_alu_imm_A_forward = '0;
		expected_issue_alu_imm_A_is_zero = '0;
		expected_issue_alu_imm_A_bank = '0;
		expected_issue_alu_imm_dest_PR = '0;
		expected_issue_alu_imm_ROB_index = '0;
	    // ALU Reg-Imm Pipeline reg read req to PRF
		expected_PRF_alu_imm_req_A_valid = '0;
		expected_PRF_alu_imm_req_A_PR = '0;
	    // op issue to LDU Pipeline
		expected_issue_ldu_valid = '0;
		expected_issue_ldu_op = '0;
		expected_issue_ldu_imm12 = '0;
		expected_issue_ldu_A_forward = '0;
		expected_issue_ldu_A_is_zero = '0;
		expected_issue_ldu_A_bank = '0;
		expected_issue_ldu_dest_PR = '0;
		expected_issue_ldu_ROB_index = '0;
	    // LDU Pipeline reg read req to PRF
		expected_PRF_ldu_req_A_valid = '0;
		expected_PRF_ldu_req_A_PR = '0;

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
		tb_dispatch_attempt_by_way = '0;
		tb_dispatch_valid_alu_imm_by_way = '0;
		tb_dispatch_valid_ldu_by_way = '0;
		tb_dispatch_op_by_way = '0;
		tb_dispatch_imm12_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_is_zero_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // pipeline feedback
		tb_alu_imm_pipeline_ready = 1'b1;
		tb_ldu_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // op issue to ALU Reg-Imm Pipeline
	    // ALU Reg-Imm Pipeline reg read req to PRF
	    // op issue to LDU Pipeline
	    // LDU Pipeline reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = '0;
	    // pipeline feedback
	    // writeback bus by bank
	    // op issue to ALU Reg-Imm Pipeline
		expected_issue_alu_imm_valid = '0;
		expected_issue_alu_imm_op = '0;
		expected_issue_alu_imm_imm12 = '0;
		expected_issue_alu_imm_A_forward = '0;
		expected_issue_alu_imm_A_is_zero = '0;
		expected_issue_alu_imm_A_bank = '0;
		expected_issue_alu_imm_dest_PR = '0;
		expected_issue_alu_imm_ROB_index = '0;
	    // ALU Reg-Imm Pipeline reg read req to PRF
		expected_PRF_alu_imm_req_A_valid = '0;
		expected_PRF_alu_imm_req_A_PR = '0;
	    // op issue to LDU Pipeline
		expected_issue_ldu_valid = '0;
		expected_issue_ldu_op = '0;
		expected_issue_ldu_imm12 = '0;
		expected_issue_ldu_A_forward = '0;
		expected_issue_ldu_A_is_zero = '0;
		expected_issue_ldu_A_bank = '0;
		expected_issue_ldu_dest_PR = '0;
		expected_issue_ldu_ROB_index = '0;
	    // LDU Pipeline reg read req to PRF
		expected_PRF_ldu_req_A_valid = '0;
		expected_PRF_ldu_req_A_PR = '0;

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