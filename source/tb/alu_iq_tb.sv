/*
    Filename: alu_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_iq module. 
    Spec: LOROF/spec/design/alu_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_iq_tb ();

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
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

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // DUT signals:


    // ALU op dispatch by entry
	logic [3:0] tb_dispatch_valid_by_entry;
	logic [3:0][3:0] tb_dispatch_op_by_entry;
	logic [3:0][31:0] tb_dispatch_imm_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_entry;
	logic [3:0] tb_dispatch_A_unneeded_by_entry;
	logic [3:0] tb_dispatch_A_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_entry;
	logic [3:0] tb_dispatch_is_imm_by_entry;
	logic [3:0] tb_dispatch_B_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_entry;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_entry;

    // ALU op dispatch feedback by entry
    logic [3:0] DUT_dispatch_open_by_entry, expected_dispatch_open_by_entry;

    // ALU pipeline feedback
    logic tb_pipeline_ready;

    // writeback bus
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // ALU op issue to ALU pipeline
	logic DUT_issue_valid, expected_issue_valid;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic DUT_issue_is_imm, expected_issue_is_imm;
	logic [31:0] DUT_issue_imm, expected_issue_imm;
	logic DUT_issue_A_unneeded, expected_issue_A_unneeded;
	logic DUT_issue_A_forward, expected_issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_A_bank, expected_issue_A_bank;
	logic DUT_issue_B_forward, expected_issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_B_bank, expected_issue_B_bank;
	logic [LOG_PR_COUNT-1:0] DUT_issue_dest_PR, expected_issue_dest_PR;
	logic [3:0][LOG_ROB_ENTRIES-1:0] DUT_issue_ROB_index, expected_issue_ROB_index;

    // reg read req to PRF
	logic DUT_PRF_req_A_valid, expected_PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_A_PR, expected_PRF_req_A_PR;
	logic DUT_PRF_req_B_valid, expected_PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] DUT_PRF_req_B_PR, expected_PRF_req_B_PR;

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // DUT instantiation:

	alu_iq DUT (

		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // ALU op dispatch by entry
		.dispatch_valid_by_entry(tb_dispatch_valid_by_entry),
		.dispatch_op_by_entry(tb_dispatch_op_by_entry),
		.dispatch_imm_by_entry(tb_dispatch_imm_by_entry),
		.dispatch_A_PR_by_entry(tb_dispatch_A_PR_by_entry),
		.dispatch_A_unneeded_by_entry(tb_dispatch_A_unneeded_by_entry),
		.dispatch_A_ready_by_entry(tb_dispatch_A_ready_by_entry),
		.dispatch_B_PR_by_entry(tb_dispatch_B_PR_by_entry),
		.dispatch_is_imm_by_entry(tb_dispatch_is_imm_by_entry),
		.dispatch_B_ready_by_entry(tb_dispatch_B_ready_by_entry),
		.dispatch_dest_PR_by_entry(tb_dispatch_dest_PR_by_entry),
		.dispatch_ROB_index_by_entry(tb_dispatch_ROB_index_by_entry),

        // ALU op dispatch feedback by entry
        .dispatch_open_by_entry(DUT_dispatch_open_by_entry),

        // ALU pipeline feedback
        .pipeline_ready(tb_pipeline_ready),

	    // writeback bus
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // ALU op issue to ALU pipeline
		.issue_valid(DUT_issue_valid),
		.issue_op(DUT_issue_op),
		.issue_is_imm(DUT_issue_is_imm),
		.issue_imm(DUT_issue_imm),
		.issue_A_unneeded(DUT_issue_A_unneeded),
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

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // tasks:

    task check_outputs();
    begin
		if (expected_dispatch_open_by_entry !== DUT_dispatch_open_by_entry) begin
			$display("TB ERROR: expected_dispatch_open_by_entry (%h) != DUT_dispatch_open_by_entry (%h)",
				expected_dispatch_open_by_entry, DUT_dispatch_open_by_entry);
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

		if (expected_issue_is_imm !== DUT_issue_is_imm) begin
			$display("TB ERROR: expected_issue_is_imm (%h) != DUT_issue_is_imm (%h)",
				expected_issue_is_imm, DUT_issue_is_imm);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_imm !== DUT_issue_imm) begin
			$display("TB ERROR: expected_issue_imm (%h) != DUT_issue_imm (%h)",
				expected_issue_imm, DUT_issue_imm);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_unneeded !== DUT_issue_A_unneeded) begin
			$display("TB ERROR: expected_issue_A_unneeded (%h) != DUT_issue_A_unneeded (%h)",
				expected_issue_A_unneeded, DUT_issue_A_unneeded);
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

    ///////////////////////////////////////////////////////////////////////////////////////////////////////
    // initial block:

    initial begin

        ///////////////////////////////////////////////////////////////////////////////////////////////////
        // reset:
        test_case = "reset";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        // inputs:
        sub_test_case = "assert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b0;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
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
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
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

        ///////////////////////////////////////////////////////////////////////////////////////////////////
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: NOP", "\n\t\t",
            "dispatch2: NOP", "\n\t\t",
            "dispatch1: NOP", "\n\t\t",
            "dispatch0: 0: ADD p3, p1:r, p2:r", "\n\t\t",
            "IQ3: NOP", "\n\t\t",
            "IQ2: NOP", "\n\t\t",
            "IQ1: NOP", "\n\t\t",
            "IQ0: NOP", "\n\t\t",
            "issue: NOP", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0001;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h1};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0001;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h2};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0001;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h3};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
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
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: v 1: SLL p6, p4:f, p5:r", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v 0: ADD p3, p1:r, p2:r", "\n\t\t",
            "issue: v 0: ADD p3, p1:r, p2:r", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0001;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0001};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h4};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h5};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0001;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h6};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h1};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h1;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h2;
		expected_issue_dest_PR = 7'h3;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h1;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 5: OR p12, p11:r, p8:f", "\n\t\t",
            "dispatch2: v 4: XORI p10, p8:f, 0xFFFFFFFF", "\n\t\t",
            "dispatch1: v 3: SLTI p9, p8:f, 0x678", "\n\t\t",
            "dispatch0: v 2: LUI p7, 0x12345000", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v 1: SLL p6, p4:F, p5:r", "\n\t\t",
            "issue: v 1: SLL p6, p4:F, p5:r", "\n\t\t",
			"activity: WB p4", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b1111;
		tb_dispatch_op_by_entry = {4'b0110, 4'b0100, 4'b0010, 4'b1111};
		tb_dispatch_imm_by_entry = {32'h0, 32'hFFFFFFFF, 32'h678, 32'h12345000};
		tb_dispatch_A_PR_by_entry = {7'hB, 7'h8, 7'h8, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0001;
		tb_dispatch_A_ready_by_entry = 4'b1000;
		tb_dispatch_B_PR_by_entry = {7'h8, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0111;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'hC, 7'hA, 7'h9, 7'h7};
		tb_dispatch_ROB_index_by_entry = {7'h5, 7'h4, 7'h3, 7'h2};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0001;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h1};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0001;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h1;
		expected_issue_dest_PR = 7'h6;
		expected_issue_ROB_index = 7'h1;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h4;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: v 5: OR p12, p11:r, p8:f", "\n\t\t",
            "IQ2: v 4: XORI p10, p8:f, 0xFFFFFFFF", "\n\t\t",
            "IQ1: v 3: SLTI p9, p8:f, 0x678", "\n\t\t",
            "IQ0: v 2: LUI p7, 0x12345000", "\n\t\t",
            "issue: i 2: LUI p7, 0x12345000", "\n\t\t",
			"activity: pipeline not ready", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b0;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b0000;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b1111;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'h12345000;
		expected_issue_A_unneeded = 1'b1;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h7;
		expected_issue_ROB_index = 7'h2;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h0;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 6: SRAI p14, p13:r, 0x123", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: v 5: OR p12, p11:r, p8:f", "\n\t\t",
            "IQ2: v 4: XORI p10, p8:f, 0xFFFFFFFF", "\n\t\t",
            "IQ1: v 3: SLTI p9, p8:f, 0x678", "\n\t\t",
            "IQ0: v 2: LUI p7, 0x12345000", "\n\t\t",
            "issue: v 2: LUI p7, 0x12345000", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b1000;
		tb_dispatch_op_by_entry = {4'b1101, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h123, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'hD, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b1000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b1000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'hE, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h6, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1000;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1111;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'h12345000;
		expected_issue_A_unneeded = 1'b1;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h7;
		expected_issue_ROB_index = 7'h2;
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
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: v 6: SRAI p14, p13:r, 0x123", "\n\t\t",
            "IQ2: v 5: OR p12, p11:r, p8:f", "\n\t\t",
            "IQ1: v 4: XORI p10, p8:f, 0xFFFFFFFF", "\n\t\t",
            "IQ0: v 3: SLTI p9, p8:f, 0x678", "\n\t\t",
            "issue: v 6: SRAI p14, p13:r, 0x123", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1000;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1101;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'h123;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h1;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'hE;
		expected_issue_ROB_index = 7'h6;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'hD;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v 5: OR p12, p11:r, p8:Fr", "\n\t\t",
            "IQ1: v 4: XORI p10, p8:Fr, 0xFFFFFFFF", "\n\t\t",
            "IQ0: v 3: SLTI p9, p8:F, 0x678", "\n\t\t",
            "issue: v 3: SLTI p9, p8:F, 0x678", "\n\t\t",
			"activity: WB p8", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0001;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h2};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1100;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0010;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'h678;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h9;
		expected_issue_ROB_index = 7'h3;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h8;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 8: SLTIU p19, p18:f, 0x543", "\n\t\t",
            "dispatch2: v 7: OR p17, p15:f, p16:f", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: v 5: OR p12, p11:r, p8:r", "\n\t\t",
            "IQ0: v 4: XORI p10, p8:r, 0xFFFFFFFF", "\n\t\t",
            "issue: i 4: XORI p10, p8:r, 0xFFFFFFFF", "\n\t\t",
			"activity: pipeline not ready", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b1100;
		tb_dispatch_op_by_entry = {4'b0011, 4'b0110, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h543, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h12, 7'hF, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h10, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b1000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h13, 7'h11, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h8, 7'h7, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b0;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1100;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0100;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'hFFFFFFFF;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'hA;
		expected_issue_ROB_index = 7'h4;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h8;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: v 8: SLTIU p19, p18:f, 0x543", "\n\t\t",
            "IQ2: v 7: OR p17, p15:f, p16:f", "\n\t\t",
            "IQ1: v 5: OR p12, p11:r, p8:r", "\n\t\t",
            "IQ0: v 4: XORI p10, p8:r, 0xFFFFFFFF", "\n\t\t",
            "issue: v 4: XORI p10, p8:r, 0xFFFFFFFF", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0110, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1000;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0100;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'hFFFFFFFF;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'hA;
		expected_issue_ROB_index = 7'h4;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h8;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v 8: SLTIU p19, p18:f, 0x543", "\n\t\t",
            "IQ1: v 7: OR p17, p15:f, p16:f", "\n\t\t",
            "IQ0: v 5: OR p12, p11:r, p8:r", "\n\t\t",
            "issue: v 5: OR p12, p11:r, p8:r", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0110, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1100;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0110;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h3;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'hC;
		expected_issue_ROB_index = 7'h5;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'hB;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h8;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: v 8: SLTIU p19, p18:Fr, 0x543", "\n\t\t",
            "IQ0: v 7: OR p17, p15:F, p16:F", "\n\t\t",
            "issue: v 7: OR p17, p15:F, p16:F", "\n\t\t",
			"activity: WB p15, p16, p18", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0110, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b1101;
		tb_WB_bus_upper_PR_by_bank = {5'h3, 5'h4, 5'h0, 5'h4};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1110;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0110;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h3;
		expected_issue_B_forward = 1'b1;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h11;
		expected_issue_ROB_index = 7'h7;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'hF;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h10;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: v B: ADD p27, p26:f, p26:f", "\n\t\t",
            "dispatch1: v A: SRL p25, p23:f, p24:f", "\n\t\t",
            "dispatch0: v 9: SUB p22, p20:f, p21:f", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v 8: SLTIU p19, p18:r, 0x543", "\n\t\t",
            "issue: v 8: SLTIU p19, p18:r, 0x543", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0111;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0101, 4'b1000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h1A, 7'h17, 7'h14};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h1A, 7'h18, 7'h15};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h1B, 7'h19, 7'h16};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'hB, 7'hA, 7'h9};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0011;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'h543;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h2;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h13;
		expected_issue_ROB_index = 7'h8;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h12;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v B: ADD p27, p26:f, p26:f", "\n\t\t",
            "IQ1: v A: SRL p25, p23:f, p24:f", "\n\t\t",
            "IQ0: v 9: SUB p22, p20:F, p21:F", "\n\t\t",
            "issue: v 9: SUB p22, p20:F, p21:F", "\n\t\t",
			"activity: WB p20, p21", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0011;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h5, 5'h5};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1100;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b1;
		expected_issue_B_bank = 2'h1;
		expected_issue_dest_PR = 7'h16;
		expected_issue_ROB_index = 7'h9;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h14;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h15;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: v B: ADD p27, p26:f, p26:f", "\n\t\t",
            "IQ0: v A: SRL p25, p23:f, p24:Fr", "\n\t\t",
            "issue: i A: SRL p25, p23:f, p24:Fr", "\n\t\t",
			"activity: WB p24", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0001;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h6};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1100;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0101;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h3;
		expected_issue_B_forward = 1'b1;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h19;
		expected_issue_ROB_index = 7'hA;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h17;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h18;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: v B: ADD p27, p26:f, p26:f", "\n\t\t",
            "IQ0: v A: SRL p25, p23:F, p24:r", "\n\t\t",
            "issue: v A: SRL p25, p23:F, p24:r", "\n\t\t",
			"activity: WB p23", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b1000;
		tb_WB_bus_upper_PR_by_bank = {5'h5, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1110;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0101;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h3;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h19;
		expected_issue_ROB_index = 7'hA;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h17;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h18;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v B: ADD p27, p26:f, p26:f", "\n\t\t",
            "issue: i B: ADD p27, p26:f, p26:f", "\n\t\t",
			"activity: inv WB p26", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b1011;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h6, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1110;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h2;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h2;
		expected_issue_dest_PR = 7'h1B;
		expected_issue_ROB_index = 7'hB;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h1A;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h1A;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: v C: SLLI p29, p28:f, 0x3", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v B: ADD p27, p26:f, p26:f", "\n\t\t",
            "issue: v B: ADD p27, p26:f, p26:f", "\n\t\t",
			"activity: WB p26", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0001;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0001};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h3};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h1C};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0001;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h1D};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'hC};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0100;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h6, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h2;
		expected_issue_B_forward = 1'b1;
		expected_issue_B_bank = 2'h2;
		expected_issue_dest_PR = 7'h1B;
		expected_issue_ROB_index = 7'hB;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h1A;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h1A;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v C: SLLI p29, p28:Fr, 0x3", "\n\t\t",
            "issue: i C: SLLI p29, p28:Fr, 0x3", "\n\t\t",
			"activity: WB p28, pipeline not ready", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b0;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0001;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h7};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1110;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0001;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'h3;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h1D;
		expected_issue_ROB_index = 7'hC;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h1C;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v C: SLLI p29, p28:r, 0x3", "\n\t\t",
            "issue: v C: SLLI p29, p28:r, 0x3", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0001;
		expected_issue_is_imm = 1'b1;
		expected_issue_imm = 32'h3;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h1D;
		expected_issue_ROB_index = 7'hC;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h1C;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
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
	    // ALU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_is_imm_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
        // ALU op dispatch feedback by entry
        // ALU pipeline feedback
        tb_pipeline_ready = 1'b1;
	    // writeback bus
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // ALU op issue to ALU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // ALU op dispatch by entry
        // ALU op dispatch feedback by entry
        expected_dispatch_open_by_entry = 4'b1111;
        // ALU pipeline feedback
	    // writeback bus
	    // ALU op issue to ALU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_is_imm = 1'b0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
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

        ///////////////////////////////////////////////////////////////////////////////////////////////////
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

