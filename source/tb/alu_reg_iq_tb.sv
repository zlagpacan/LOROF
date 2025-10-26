/*
    Filename: alu_reg_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_reg_iq module. 
    Spec: LOROF/spec/design/alu_reg_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_iq_tb ();

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


    // ALU op dispatch by way
	logic [3:0] tb_dispatch_attempt_by_way;
	logic [3:0] tb_dispatch_valid_by_way;
	logic [3:0][3:0] tb_dispatch_op_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_way;
	logic [3:0] tb_dispatch_B_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // ALU op dispatch feedback by way
	logic [3:0] DUT_dispatch_ready_advertisement, expected_dispatch_ready_advertisement;

    // ALU pipeline feedback
	logic tb_pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // ALU op issue to ALU pipeline
	logic DUT_issue_valid, expected_issue_valid;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic DUT_issue_A_forward, expected_issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_A_bank, expected_issue_A_bank;
	logic DUT_issue_B_forward, expected_issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_B_bank, expected_issue_B_bank;
	logic [LOG_PR_COUNT-1:0] DUT_issue_dest_PR, expected_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_issue_ROB_index, expected_issue_ROB_index;

    // reg read req to PRF
	logic DUT_PRF_req_A_valid, expected_PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_A_PR, expected_PRF_req_A_PR;
	logic DUT_PRF_req_B_valid, expected_PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_B_PR, expected_PRF_req_B_PR;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_reg_iq DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // ALU op dispatch by way
		.dispatch_attempt_by_way(tb_dispatch_attempt_by_way),
		.dispatch_valid_by_way(tb_dispatch_valid_by_way),
		.dispatch_op_by_way(tb_dispatch_op_by_way),
		.dispatch_A_PR_by_way(tb_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_B_PR_by_way(tb_dispatch_B_PR_by_way),
		.dispatch_B_ready_by_way(tb_dispatch_B_ready_by_way),
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // ALU op dispatch feedback by way
		.dispatch_ready_advertisement(DUT_dispatch_ready_advertisement),

	    // ALU pipeline feedback
		.pipeline_ready(tb_pipeline_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // ALU op issue to ALU pipeline
		.issue_valid(DUT_issue_valid),
		.issue_op(DUT_issue_op),
		.issue_A_forward(DUT_issue_A_forward),
		.issue_A_bank(DUT_issue_A_bank),
		.issue_B_forward(DUT_issue_B_forward),
		.issue_B_bank(DUT_issue_B_bank),
		.issue_dest_PR(DUT_issue_dest_PR),
		.issue_ROB_index(DUT_issue_ROB_index),

	    // reg read req to PRF
		.PRF_req_A_valid(DUT_PRF_req_A_valid),
		.PRF_req_A_PR(DUT_PRF_req_A_PR),
		.PRF_req_B_valid(DUT_PRF_req_B_valid),
		.PRF_req_B_PR(DUT_PRF_req_B_PR)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_dispatch_ready_advertisement !== DUT_dispatch_ready_advertisement) begin
			$display("TB ERROR: expected_dispatch_ready_advertisement (%h) != DUT_dispatch_ready_advertisement (%h)",
				expected_dispatch_ready_advertisement, DUT_dispatch_ready_advertisement);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_valid !== DUT_issue_valid) begin
			$display("TB ERROR: expected_issue_valid (%h) != DUT_issue_valid (%h)",
				expected_issue_valid, DUT_issue_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_op !== DUT_issue_op) begin
			$display("TB ERROR: expected_issue_op (%h) != DUT_issue_op (%h)",
				expected_issue_op, DUT_issue_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_forward !== DUT_issue_A_forward) begin
			$display("TB ERROR: expected_issue_A_forward (%h) != DUT_issue_A_forward (%h)",
				expected_issue_A_forward, DUT_issue_A_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_bank !== DUT_issue_A_bank) begin
			$display("TB ERROR: expected_issue_A_bank (%h) != DUT_issue_A_bank (%h)",
				expected_issue_A_bank, DUT_issue_A_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_forward !== DUT_issue_B_forward) begin
			$display("TB ERROR: expected_issue_B_forward (%h) != DUT_issue_B_forward (%h)",
				expected_issue_B_forward, DUT_issue_B_forward);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_B_bank !== DUT_issue_B_bank) begin
			$display("TB ERROR: expected_issue_B_bank (%h) != DUT_issue_B_bank (%h)",
				expected_issue_B_bank, DUT_issue_B_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_dest_PR !== DUT_issue_dest_PR) begin
			$display("TB ERROR: expected_issue_dest_PR (%h) != DUT_issue_dest_PR (%h)",
				expected_issue_dest_PR, DUT_issue_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_ROB_index !== DUT_issue_ROB_index) begin
			$display("TB ERROR: expected_issue_ROB_index (%h) != DUT_issue_ROB_index (%h)",
				expected_issue_ROB_index, DUT_issue_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_req_A_valid !== DUT_PRF_req_A_valid) begin
			$display("TB ERROR: expected_PRF_req_A_valid (%h) != DUT_PRF_req_A_valid (%h)",
				expected_PRF_req_A_valid, DUT_PRF_req_A_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_req_A_PR !== DUT_PRF_req_A_PR) begin
			$display("TB ERROR: expected_PRF_req_A_PR (%h) != DUT_PRF_req_A_PR (%h)",
				expected_PRF_req_A_PR, DUT_PRF_req_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_req_B_valid !== DUT_PRF_req_B_valid) begin
			$display("TB ERROR: expected_PRF_req_B_valid (%h) != DUT_PRF_req_B_valid (%h)",
				expected_PRF_req_B_valid, DUT_PRF_req_B_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_PRF_req_B_PR !== DUT_PRF_req_B_PR) begin
			$display("TB ERROR: expected_PRF_req_B_PR (%h) != DUT_PRF_req_B_PR (%h)",
				expected_PRF_req_B_PR, DUT_PRF_req_B_PR);
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
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b1111;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b1111;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 2: SLL p8, p6:r, p7:f", "\n\t\t",
            "dispatch2: v 1: SUB p5, p2:f, p3:r", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: v 0: ADD p2, p0:r, p1:r", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: i NOP", "\n\t\t",
            "issue: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1101;
		tb_dispatch_valid_by_way = 4'b1101;
		tb_dispatch_op_by_way = {4'b0001, 4'b1000, 4'b0000, 4'b0000};
		tb_dispatch_A_PR_by_way = {7'h6, 7'h2, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1001;
		tb_dispatch_B_PR_by_way = {7'h7, 7'h3, 7'h0, 7'h1};
		tb_dispatch_B_ready_by_way = 4'b0101;
		tb_dispatch_dest_PR_by_way = {7'h8, 7'h5, 7'h0, 7'h2};
		tb_dispatch_ROB_index_by_way = {7'h2, 7'h1, 7'h0, 7'h0};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b1111;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: v 4: SLTU pC, p9:f, pB:f", "\n\t\t",
            "dispatch1: v 3: SLT pB, p9:f, pA:f", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v 2: SLL p8, p6:r, p7:Fr", "\n\t\t",
            "IQ1: v 1: SUB p5, p2:f, p3:r", "\n\t\t",
            "IQ0: v 0: ADD p2, p0:r, p1:r", "\n\t\t",
            "issue: v 0: ADD p2, p0:r, p1:r", "\n\t\t",
			"activity: forward p7", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0110;
		tb_dispatch_valid_by_way = 4'b0110;
		tb_dispatch_op_by_way = {4'b0000, 4'b0010, 4'b0011, 4'b0000};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h9, 7'h9, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'hB, 7'hA, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'hC, 7'hB, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h4, 7'h3, 7'h0};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1000;
		tb_WB_bus_upper_PR_by_bank = {5'h1, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b1111;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h1;
		expected_issue_dest_PR = 7'h2;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 6: SRL pF, p0:r, pE:f", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: v 5: XOR pD, p0:r, p4:f", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: i NOP", "\n\t\t",
            "IQ3: v 4: SLTU pC, p9:f, pB:f", "\n\t\t",
            "IQ2: v 3: SLT pB, p9:f, pA:f", "\n\t\t",
            "IQ1: v 2: SLL p8, p6:r, p7:r", "\n\t\t",
            "IQ0: v 1: SUB p5, p2:F, p3:r", "\n\t\t",
            "issue: v 1: SUB p5, p2:F, p3:r", "\n\t\t",
			"activity: forward p2", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1001;
		tb_dispatch_valid_by_way = 4'b1001;
		tb_dispatch_op_by_way = {4'b0101, 4'b0000, 4'b0000, 4'b0100};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1001;
		tb_dispatch_B_PR_by_way = {7'hE, 7'h0, 7'h0, 7'h4};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'hF, 7'h0, 7'h0, 7'hD};
		tb_dispatch_ROB_index_by_way = {7'h6, 7'h0, 7'h0, 7'h5};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0100;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b1111;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1000;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h2;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h3;
		expected_issue_dest_PR = 7'h5;
		expected_issue_ROB_index = 7'h1;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h2;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: vi A: ADD p13, p0:r, p3A:f", "\n\t\t",
            "dispatch2: vi 9: AND p12, p0:r, p39:f", "\n\t\t",
            "dispatch1: v 8: OR p11, p0:r, p38:f", "\n\t\t",
            "dispatch0: v 7: SRA p10, p0:r, p37:f", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i NOP", "\n\t\t",
            "IQ5: i NOP", "\n\t\t",
            "IQ4: v 6: SRL pF, p0:r, pE:f", "\n\t\t",
            "IQ3: v 5: XOR pD, p0:r, p4:f", "\n\t\t",
            "IQ2: v 4: SLTU pC, p9:f, pB:f", "\n\t\t",
            "IQ1: v 3: SLT pB, p9:f, pA:f", "\n\t\t",
            "IQ0: v 2: SLL p8, p6:r, p7:r", "\n\t\t",
            "issue: i NOP", "\n\t\t",
			"activity: pipeline stall", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1111;
		tb_dispatch_valid_by_way = 4'b0011;
		tb_dispatch_op_by_way = {4'b0000, 4'b0111, 4'b0110, 4'b1101};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1111;
		tb_dispatch_B_PR_by_way = {7'h3A, 7'h39, 7'h38, 7'h37};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h13, 7'h12, 7'h11, 7'h10};
		tb_dispatch_ROB_index_by_way = {7'hA, 7'h9, 7'h8, 7'h7};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b0;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b0111;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: vi A: ADD p13, p0:r, p3A:f", "\n\t\t",
            "dispatch2: v 9: AND p12, p0:r, p39:f", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: v 8: OR p11, p0:r, p38:f", "\n\t\t",
            "IQ5: v 7: SRA p10, p0:r, p37:f", "\n\t\t",
            "IQ4: v 6: SRL pF, p0:r, pE:f", "\n\t\t",
            "IQ3: v 5: XOR pD, p0:r, p4:f", "\n\t\t",
            "IQ2: v 4: SLTU pC, p9:f, pB:f", "\n\t\t",
            "IQ1: v 3: SLT pB, p9:f, pA:f", "\n\t\t",
            "IQ0: v 2: SLL p8, p6:r, p7:r", "\n\t\t",
            "issue: v 2: SLL p8, p6:r, p7:r", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1100;
		tb_dispatch_valid_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b0111, 4'b0000, 4'b0000};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1100;
		tb_dispatch_B_PR_by_way = {7'h3A, 7'h39, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h13, 7'h12, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'hA, 7'h9, 7'h0, 7'h0};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b0001;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0001;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h2;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h3;
		expected_issue_dest_PR = 7'h8;
		expected_issue_ROB_index = 7'h2;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h6;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: vi A: ADD p13, p0:r, p3A:f", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: v 9: AND p12, p0:r, p39:f", "\n\t\t",
            "IQ5: v 8: OR p11, p0:r, p38:f", "\n\t\t",
            "IQ4: v 7: SRA p10, p0:r, p37:F", "\n\t\t",
            "IQ3: v 6: SRL pF, p0:r, pE:f", "\n\t\t",
            "IQ2: v 5: XOR pD, p0:r, p4:f", "\n\t\t",
            "IQ1: v 4: SLTU pC, p9:f, pB:f", "\n\t\t",
            "IQ0: v 3: SLT pB, p9:f, pA:f", "\n\t\t",
            "issue: v 7: SRA p10, p0:r, p37:F", "\n\t\t",
			"activity: forward p37", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0001;
		tb_dispatch_valid_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0001;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h3A};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h13};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'hA};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1000;
		tb_WB_bus_upper_PR_by_bank = {5'hD, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b0001;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1101;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b1;
		expected_issue_B_bank = 2'h3;
		expected_issue_dest_PR = 7'h10;
		expected_issue_ROB_index = 7'h7;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h37;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: vi C: SUB p14, p0:r, p3C:f", "\n\t\t",
            "dispatch1: v B: ADD p13, p3B:f, p0:r", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ7: i NOP", "\n\t\t",
            "IQ6: i A: ADD p13, p0:r, p3A:f", "\n\t\t",
            "IQ5: v 9: AND p12, p0:r, p39:f", "\n\t\t",
            "IQ4: v 8: OR p11, p0:r, p38:f", "\n\t\t",
            "IQ3: v 6: SRL pF, p0:r, pE:f", "\n\t\t",
            "IQ2: v 5: XOR pD, p0:r, p4:f", "\n\t\t",
            "IQ1: v 4: SLTU pC, p9:f, pB:f", "\n\t\t",
            "IQ0: v 3: SLT pB, p9:f, pA:f", "\n\t\t",
            "issue: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0110;
		tb_dispatch_valid_by_way = 4'b0010;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b1000, 4'b0000};
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h3B, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0100;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h3C, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0010;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h14, 7'h13, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'hC, 7'hB, 7'h0};
	    // ALU op dispatch feedback by way
	    // ALU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by way
	    // ALU op dispatch feedback by way
		expected_dispatch_ready_advertisement = 4'b0011;
	    // ALU pipeline feedback
	    // writeback bus by bank
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

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