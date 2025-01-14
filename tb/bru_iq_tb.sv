/*
    Filename: bru_iq_tb.sv
    Author: zlagpacan
    Description: Testbench for bru_iq module. 
    Spec: LOROF/spec/design/bru_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_iq_tb ();

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


    // BRU op dispatch by entry
	logic [3:0] tb_dispatch_valid_by_entry;
	logic [3:0][3:0] tb_dispatch_op_by_entry;
	logic [3:0][31:0] tb_dispatch_PC_by_entry;
	logic [3:0][31:0] tb_dispatch_speculated_next_PC_by_entry;
	logic [3:0][31:0] tb_dispatch_imm_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_entry;
	logic [3:0] tb_dispatch_A_unneeded_by_entry;
	logic [3:0] tb_dispatch_A_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_entry;
	logic [3:0] tb_dispatch_B_unneeded_by_entry;
	logic [3:0] tb_dispatch_B_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_entry;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_entry;

    // BRU op dispatch feedback by entry
	logic [3:0] DUT_dispatch_open_by_entry, expected_dispatch_open_by_entry;

    // BRU pipeline feedback
	logic tb_pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // BRU op issue to BRU pipeline
	logic DUT_issue_valid, expected_issue_valid;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic [31:0] DUT_issue_PC, expected_issue_PC;
	logic [31:0] DUT_issue_speculated_next_PC, expected_issue_speculated_next_PC;
	logic [31:0] DUT_issue_imm, expected_issue_imm;
	logic DUT_issue_A_unneeded, expected_issue_A_unneeded;
	logic DUT_issue_A_forward, expected_issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_A_bank, expected_issue_A_bank;
	logic DUT_issue_B_unneeded, expected_issue_B_unneeded;
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

	bru_iq DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // BRU op dispatch by entry
		.dispatch_valid_by_entry(tb_dispatch_valid_by_entry),
		.dispatch_op_by_entry(tb_dispatch_op_by_entry),
		.dispatch_PC_by_entry(tb_dispatch_PC_by_entry),
		.dispatch_speculated_next_PC_by_entry(tb_dispatch_speculated_next_PC_by_entry),
		.dispatch_imm_by_entry(tb_dispatch_imm_by_entry),
		.dispatch_A_PR_by_entry(tb_dispatch_A_PR_by_entry),
		.dispatch_A_unneeded_by_entry(tb_dispatch_A_unneeded_by_entry),
		.dispatch_A_ready_by_entry(tb_dispatch_A_ready_by_entry),
		.dispatch_B_PR_by_entry(tb_dispatch_B_PR_by_entry),
		.dispatch_B_unneeded_by_entry(tb_dispatch_B_unneeded_by_entry),
		.dispatch_B_ready_by_entry(tb_dispatch_B_ready_by_entry),
		.dispatch_dest_PR_by_entry(tb_dispatch_dest_PR_by_entry),
		.dispatch_ROB_index_by_entry(tb_dispatch_ROB_index_by_entry),

	    // BRU op dispatch feedback by entry
		.dispatch_open_by_entry(DUT_dispatch_open_by_entry),

	    // BRU pipeline feedback
		.pipeline_ready(tb_pipeline_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // BRU op issue to BRU pipeline
		.issue_valid(DUT_issue_valid),
		.issue_op(DUT_issue_op),
		.issue_PC(DUT_issue_PC),
		.issue_speculated_next_PC(DUT_issue_speculated_next_PC),
		.issue_imm(DUT_issue_imm),
		.issue_A_unneeded(DUT_issue_A_unneeded),
		.issue_A_forward(DUT_issue_A_forward),
		.issue_A_bank(DUT_issue_A_bank),
		.issue_B_unneeded(DUT_issue_B_unneeded),
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

		if (expected_issue_PC !== DUT_issue_PC) begin
			$display("TB ERROR: expected_issue_PC (%h) != DUT_issue_PC (%h)",
				expected_issue_PC, DUT_issue_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_speculated_next_PC !== DUT_issue_speculated_next_PC) begin
			$display("TB ERROR: expected_issue_speculated_next_PC (%h) != DUT_issue_speculated_next_PC (%h)",
				expected_issue_speculated_next_PC, DUT_issue_speculated_next_PC);
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

		if (expected_issue_B_unneeded !== DUT_issue_B_unneeded) begin
			$display("TB ERROR: expected_issue_B_unneeded (%h) != DUT_issue_B_unneeded (%h)",
				expected_issue_B_unneeded, DUT_issue_B_unneeded);
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
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1111;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_PC = 32'h0;
		expected_issue_speculated_next_PC = 32'h0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b0;
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
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1111;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_PC = 32'h0;
		expected_issue_speculated_next_PC = 32'h0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b0;
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
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: v 0: JALR p2, 0x1C(p1:r); 0x0->0xABC", "\n\t\t",
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
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0001;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'hABC};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h1C};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h1};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0001;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0001;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h2};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1111;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b0000;
		expected_issue_PC = 32'h0;
		expected_issue_speculated_next_PC = 32'h0;
		expected_issue_imm = 32'h0;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b0;
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
            "dispatch0: v 1: JAL p3, 0x1234; 0xABC->0x1CF0", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v 0: JALR p2, 0x1C(p1:r); 0x0->0xABC", "\n\t\t",
            "issue: v 0: JALR p2, 0x1C(p1:r); 0x0->0xABC", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0001;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0001};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'hABC};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h1CF0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h1234};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0001;
		tb_dispatch_A_ready_by_entry = 4'b0001;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0001;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h3};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h1};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1111;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0000;
		expected_issue_PC = 32'h0;
		expected_issue_speculated_next_PC = 32'hABC;
		expected_issue_imm = 32'h1C;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h1;
		expected_issue_B_unneeded = 1'b1;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h2;
		expected_issue_ROB_index = 7'h0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h1;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: v 3: AUIPC p6, 0x5678; 0x1CF4->0x1CF8", "\n\t\t",
            "dispatch0: v 2: BEQ p4:f, p5:f, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: i NOP", "\n\t\t",
            "IQ0: v 1: JAL p3, 0x1234; 0xABC->0x1CF0", "\n\t\t",
            "issue: v 1: JAL p3, 0x1234; 0xABC->0x1CF0", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0011;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0100, 4'b1000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h1CF4, 32'h1CF0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h1CF8, 32'h1CF4};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h5678, 32'h210};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h4};
		tb_dispatch_A_unneeded_by_entry = 4'b0010;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h5};
		tb_dispatch_B_unneeded_by_entry = 4'b0010;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h6, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h3, 7'h2};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1111;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0001;
		expected_issue_PC = 32'hABC;
		expected_issue_speculated_next_PC = 32'h1CF0;
		expected_issue_imm = 32'h1234;
		expected_issue_A_unneeded = 1'b1;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b1;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h3;
		expected_issue_ROB_index = 7'h1;
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
            "dispatch2: v 5: BLT p9:f, pA:r, 0x234; 0x1C40->0x1E74", "\n\t\t",
            "dispatch1: v 4: BNE p7:r, p8:f, 0xFFFFFF48; 0x1CF8->0x1C40", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: i NOP", "\n\t\t",
            "IQ1: v 3: AUIPC p6, 0x5678; 0x1CF4->0x1CF8", "\n\t\t",
            "IQ0: v 2: BEQ p4:f, p5:Fr, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "issue: v 3: AUIPC p6, 0x5678; 0x1CF4->0x1CF8", "\n\t\t",
			"activity: WB p5", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0110;
		tb_dispatch_op_by_entry = {4'b0000, 4'b1100, 4'b1001, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h1C40, 32'h1CF8, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h1E74, 32'h1C40, 32'h0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h234, 32'hFFFFFF48, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h9, 7'h7, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0010;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'hA, 7'h8, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0100;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h5, 7'h4, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0010;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h1, 5'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1110;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b0100;
		expected_issue_PC = 32'h1CF4;
		expected_issue_speculated_next_PC = 32'h1CF8;
		expected_issue_imm = 32'h5678;
		expected_issue_A_unneeded = 1'b1;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b1;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h6;
		expected_issue_ROB_index = 7'h3;
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
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v 5: BLT p9:f, pA:r, 0x234; 0x1C40->0x1E74", "\n\t\t",
            "IQ1: v 4: BNE p7:r, p8:Fr, 0xFFFFFF48; 0x1CF8->0x1C40", "\n\t\t",
            "IQ0: v 2: BEQ p4:f, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "issue: i 2: BEQ p4:f, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
			"activity: pipeline not ready, WB p8", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b0;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0001;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h2};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1000;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b1000;
		expected_issue_PC = 32'h1CF0;
		expected_issue_speculated_next_PC = 32'h1CF4;
		expected_issue_imm = 32'h210;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h1;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h2;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h4;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 7: BLTU pD:r, pE:f, 0x8; 0x1E78->0x1E80", "\n\t\t",
            "dispatch2: v 6: BGE pB:r, pC:r, 0xFFFFFFFC; 0x1E74->0x1E78", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v 5: BLT p9:f, pA:r, 0x234; 0x1C40->0x1E74", "\n\t\t",
            "IQ1: v 4: BNE p7:r, p8:r, 0xFFFFFF48; 0x1CF8->0x1C40", "\n\t\t",
            "IQ0: v 2: BEQ p4:f, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "issue: v 4: BNE p7:r, p8:r, 0xFFFFFF48; 0x1CF8->0x1C40", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b1100;
		tb_dispatch_op_by_entry = {4'b1110, 4'b1101, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h1E78, 32'h1E74, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h1E80, 32'h1E78, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h8, 32'hFFFFFFFC, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'hD, 7'hB, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b1100;
		tb_dispatch_B_PR_by_entry = {7'hE, 7'hC, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0100;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h7, 7'h6, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1100;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1001;
		expected_issue_PC = 32'h1CF8;
		expected_issue_speculated_next_PC = 32'h1C40;
		expected_issue_imm = 32'hFFFFFF48;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h3;
		expected_issue_B_unneeded = 1'b0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h4;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'h7;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h8;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: v 8: BGEU pF:f, p0:r, 0x128CC; 0x1E80->0x1474C", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: v 7: BLTU pD:r, pE:f, 0x8; 0x1E78->0x1E80", "\n\t\t",
            "IQ2: v 6: BGE pB:r, pC:r, 0xFFFFFFFC; 0x1E74->0x1E78", "\n\t\t",
            "IQ1: v 5: BLT p9:F, pA:r, 0x234; 0x1C40->0x1E74", "\n\t\t",
            "IQ0: v 2: BEQ p4:f, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "issue: v 5: BLT p9:F, pA:r, 0x234; 0x1C40->0x1E74", "\n\t\t",
			"activity: WB p9", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b1000;
		tb_dispatch_op_by_entry = {4'b1111, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h1E80, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h1474C, 32'h0, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h128CC, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'hF, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b1000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h8, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0010;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h2, 5'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1000;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1100;
		expected_issue_PC = 32'h1C40;
		expected_issue_speculated_next_PC = 32'h1E74;
		expected_issue_imm = 32'h234;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h1;
		expected_issue_B_unneeded = 1'b0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h2;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h5;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h9;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'hA;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: v 8: BGEU pF:f, p0:r, 0x128CC; 0x1E80->0x1474C", "\n\t\t",
            "IQ2: v 7: BLTU pD:r, pE:f, 0x8; 0x1E78->0x1E80", "\n\t\t",
            "IQ1: v 6: BGE pB:r, pC:r, 0xFFFFFFFC; 0x1E74->0x1E78", "\n\t\t",
            "IQ0: v 2: BEQ p4:f, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "issue: v 6: BGE pB:r, pC:r, 0xFFFFFFFC; 0x1E74->0x1E78", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1000;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1101;
		expected_issue_PC = 32'h1E74;
		expected_issue_speculated_next_PC = 32'h1E78;
		expected_issue_imm = 32'hFFFFFFFC;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h3;
		expected_issue_B_unneeded = 1'b0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h0;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h6;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b1;
		expected_PRF_req_A_PR = 7'hB;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'hC;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v 8: BGEU pF:f, p0:r, 0x128CC; 0x1E80->0x1474C", "\n\t\t",
            "IQ1: v 7: BLTU pD:r, pE:f, 0x8; 0x1E78->0x1E80", "\n\t\t",
            "IQ0: v 2: BEQ p4:F, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "issue: i 2: BEQ p4:F, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1000;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b0;
		expected_issue_op = 4'b1000;
		expected_issue_PC = 32'h1CF0;
		expected_issue_speculated_next_PC = 32'h1CF4;
		expected_issue_imm = 32'h210;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b0;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h1;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h2;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h4;
		expected_PRF_req_B_valid = 1'b0;
		expected_PRF_req_B_PR = 7'h5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"\n\t\t", 
            "dispatch3: i NOP", "\n\t\t",
            "dispatch2: i NOP", "\n\t\t",
            "dispatch1: i NOP", "\n\t\t",
            "dispatch0: i NOP", "\n\t\t",
            "IQ3: i NOP", "\n\t\t",
            "IQ2: v 8: BGEU pF:Fr, p0:r, 0x128CC; 0x1E80->0x1474C", "\n\t\t",
            "IQ1: v 7: BLTU pD:r, pE:f, 0x8; 0x1E78->0x1E80", "\n\t\t",
            "IQ0: v 2: BEQ p4:F, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
            "issue: v 2: BEQ p4:F, p5:r, 0x210; 0x1CF0->0x1CF4", "\n\t\t",
			"activity: WB p4, pF", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op dispatch by entry
		tb_dispatch_valid_by_entry = 4'b0000;
		tb_dispatch_op_by_entry = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_speculated_next_PC_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_imm_by_entry = {32'h0, 32'h0, 32'h0, 32'h0};
		tb_dispatch_A_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_unneeded_by_entry = 4'b0000;
		tb_dispatch_A_ready_by_entry = 4'b0000;
		tb_dispatch_B_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_unneeded_by_entry = 4'b0000;
		tb_dispatch_B_ready_by_entry = 4'b0000;
		tb_dispatch_dest_PR_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_entry = {7'h0, 7'h0, 7'h0, 7'h0};
	    // BRU op dispatch feedback by entry
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1001;
		tb_WB_bus_upper_PR_by_bank = {5'h3, 5'h0, 5'h0, 5'h1};
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // BRU op dispatch by entry
	    // BRU op dispatch feedback by entry
		expected_dispatch_open_by_entry = 4'b1100;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = 1'b1;
		expected_issue_op = 4'b1000;
		expected_issue_PC = 32'h1CF0;
		expected_issue_speculated_next_PC = 32'h1CF4;
		expected_issue_imm = 32'h210;
		expected_issue_A_unneeded = 1'b0;
		expected_issue_A_forward = 1'b1;
		expected_issue_A_bank = 2'h0;
		expected_issue_B_unneeded = 1'b0;
		expected_issue_B_forward = 1'b0;
		expected_issue_B_bank = 2'h1;
		expected_issue_dest_PR = 7'h0;
		expected_issue_ROB_index = 7'h2;
	    // reg read req to PRF
		expected_PRF_req_A_valid = 1'b0;
		expected_PRF_req_A_PR = 7'h4;
		expected_PRF_req_B_valid = 1'b1;
		expected_PRF_req_B_PR = 7'h5;

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