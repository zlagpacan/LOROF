/*
    Filename: bru_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for bru_pipeline module. 
    Spec: LOROF/spec/design/bru_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pipeline_tb ();

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


    // BRU op issue to BRU IQ
	logic tb_issue_valid;
	logic [3:0] tb_issue_op;
	logic [31:0] tb_issue_PC;
	logic [31:0] tb_issue_speculated_next_PC;
	logic [31:0] tb_issue_imm;
	logic tb_issue_A_unneeded;
	logic tb_issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_A_bank;
	logic tb_issue_B_unneeded;
	logic tb_issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_B_bank;
	logic [LOG_PR_COUNT-1:0] tb_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_issue_ROB_index;

    // output feedback to BRU IQ
	logic DUT_issue_ready, expected_issue_ready;

    // reg read info and data from PRF
	logic tb_A_reg_read_ack;
	logic tb_A_reg_read_port;
	logic tb_B_reg_read_ack;
	logic tb_B_reg_read_port;
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] tb_reg_read_data_by_bank_by_port;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_forward_data_by_bank;

    // writeback data to PRF
	logic DUT_WB_valid, expected_WB_valid;
	logic [31:0] DUT_WB_data, expected_WB_data;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR, expected_WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_WB_ROB_index, expected_WB_ROB_index;

    // writeback backpressure from PRF
	logic tb_WB_ready;

    // restart req to ROB
        // no backpressure, ROB's job to deal with multiple identical req's
	logic DUT_restart_req_valid, expected_restart_req_valid;
	logic DUT_restart_req_mispredict, expected_restart_req_mispredict;
	logic [LOG_ROB_ENTRIES-1:0] DUT_restart_req_ROB_index, expected_restart_req_ROB_index;
	logic [31:0] DUT_restart_req_PC, expected_restart_req_PC;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bru_pipeline DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // BRU op issue to BRU IQ
		.issue_valid(tb_issue_valid),
		.issue_op(tb_issue_op),
		.issue_PC(tb_issue_PC),
		.issue_speculated_next_PC(tb_issue_speculated_next_PC),
		.issue_imm(tb_issue_imm),
		.issue_A_unneeded(tb_issue_A_unneeded),
		.issue_A_forward(tb_issue_A_forward),
		.issue_A_bank(tb_issue_A_bank),
		.issue_B_unneeded(tb_issue_B_unneeded),
		.issue_B_forward(tb_issue_B_forward),
		.issue_B_bank(tb_issue_B_bank),
		.issue_dest_PR(tb_issue_dest_PR),
		.issue_ROB_index(tb_issue_ROB_index),

	    // output feedback to BRU IQ
		.issue_ready(DUT_issue_ready),

	    // reg read info and data from PRF
		.A_reg_read_ack(tb_A_reg_read_ack),
		.A_reg_read_port(tb_A_reg_read_port),
		.B_reg_read_ack(tb_B_reg_read_ack),
		.B_reg_read_port(tb_B_reg_read_port),
		.reg_read_data_by_bank_by_port(tb_reg_read_data_by_bank_by_port),

	    // forward data from PRF
		.forward_data_by_bank(tb_forward_data_by_bank),

	    // writeback data to PRF
		.WB_valid(DUT_WB_valid),
		.WB_data(DUT_WB_data),
		.WB_PR(DUT_WB_PR),
		.WB_ROB_index(DUT_WB_ROB_index),

	    // writeback backpressure from PRF
		.WB_ready(tb_WB_ready),

	    // restart req to ROB
	        // no backpressure, ROB's job to deal with multiple identical req's
		.restart_req_valid(DUT_restart_req_valid),
		.restart_req_mispredict(DUT_restart_req_mispredict),
		.restart_req_ROB_index(DUT_restart_req_ROB_index),
		.restart_req_PC(DUT_restart_req_PC)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_issue_ready !== DUT_issue_ready) begin
			$display("TB ERROR: expected_issue_ready (%h) != DUT_issue_ready (%h)",
				expected_issue_ready, DUT_issue_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_valid !== DUT_WB_valid) begin
			$display("TB ERROR: expected_WB_valid (%h) != DUT_WB_valid (%h)",
				expected_WB_valid, DUT_WB_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_data !== DUT_WB_data) begin
			$display("TB ERROR: expected_WB_data (%h) != DUT_WB_data (%h)",
				expected_WB_data, DUT_WB_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_PR !== DUT_WB_PR) begin
			$display("TB ERROR: expected_WB_PR (%h) != DUT_WB_PR (%h)",
				expected_WB_PR, DUT_WB_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_ROB_index !== DUT_WB_ROB_index) begin
			$display("TB ERROR: expected_WB_ROB_index (%h) != DUT_WB_ROB_index (%h)",
				expected_WB_ROB_index, DUT_WB_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_req_valid !== DUT_restart_req_valid) begin
			$display("TB ERROR: expected_restart_req_valid (%h) != DUT_restart_req_valid (%h)",
				expected_restart_req_valid, DUT_restart_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_req_mispredict !== DUT_restart_req_mispredict) begin
			$display("TB ERROR: expected_restart_req_mispredict (%h) != DUT_restart_req_mispredict (%h)",
				expected_restart_req_mispredict, DUT_restart_req_mispredict);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_req_ROB_index !== DUT_restart_req_ROB_index) begin
			$display("TB ERROR: expected_restart_req_ROB_index (%h) != DUT_restart_req_ROB_index (%h)",
				expected_restart_req_ROB_index, DUT_restart_req_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_req_PC !== DUT_restart_req_PC) begin
			$display("TB ERROR: expected_restart_req_PC (%h) != DUT_restart_req_PC (%h)",
				expected_restart_req_PC, DUT_restart_req_PC);
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
	    // BRU op issue to BRU IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_PC = 32'h0;
		tb_issue_speculated_next_PC = 32'h0; 
		tb_issue_imm = 32'h0;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_unneeded = 1'b0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 7'h0;
		tb_issue_ROB_index = 7'h0;
	    // output feedback to BRU IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // restart req to ROB

		@(posedge CLK);

		// outputs:

	    // BRU op issue to BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h4;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // restart req to ROB
		expected_restart_req_valid = 1'b0;
		expected_restart_req_mispredict = 1'b0;
		expected_restart_req_ROB_index = 7'h0;
		expected_restart_req_PC = 32'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op issue to BRU IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_PC = 32'h0;
		tb_issue_speculated_next_PC = 32'h0; 
		tb_issue_imm = 32'h0;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_unneeded = 1'b0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 7'h0;
		tb_issue_ROB_index = 7'h0;
	    // output feedback to BRU IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // restart req to ROB

		@(posedge CLK);

		// outputs:

	    // BRU op issue to BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h4;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // restart req to ROB
		expected_restart_req_valid = 1'b0;
		expected_restart_req_mispredict = 1'b0;
		expected_restart_req_ROB_index = 7'h0;
		expected_restart_req_PC = 32'h0;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK);

		// inputs
		sub_test_case = {"\n\t\t",
            "issue: v 0: JALR p2, 0x1C(p1:r); 0x0->0xABC, mispred 0xAB8", "\n\t\t",
            "OC: i NOP", "\n\t\t",
            "EX: i NOP", "\n\t\t",
            "WB: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op issue to BRU IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0000;
		tb_issue_PC = 32'h0;
		tb_issue_speculated_next_PC = 32'hAB8;
		tb_issue_imm = 32'h1C;
		tb_issue_A_unneeded = 1'b0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h1;
		tb_issue_B_unneeded = 1'b1;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 7'h2;
		tb_issue_ROB_index = 7'h0;
	    // output feedback to BRU IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // restart req to ROB

		@(negedge CLK);

		// outputs:

	    // BRU op issue to BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h4;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // restart req to ROB
		expected_restart_req_valid = 1'b0;
		expected_restart_req_mispredict = 1'b0;
		expected_restart_req_ROB_index = 7'h0;
		expected_restart_req_PC = 32'h0;

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = {"\n\t\t",
            "issue: i 1: JAL p3, 0x1234; 0xABC->0x1CF0", "\n\t\t",
            "OC: v 0: JALR p2, 0x1C(p1:r); 0x0->0xABC, mispred 0xAB8", "\n\t\t",
            "EX: i NOP", "\n\t\t",
            "WB: i NOP", "\n\t\t",
			"activity: ", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op issue to BRU IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0001;
		tb_issue_PC = 32'hABC;
		tb_issue_speculated_next_PC = 32'h1CF0;
		tb_issue_imm = 32'h1234;
		tb_issue_A_unneeded = 1'b1;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_unneeded = 1'b1;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 7'h3;
		tb_issue_ROB_index = 7'h1;
	    // output feedback to BRU IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // restart req to ROB

		@(negedge CLK);

		// outputs:

	    // BRU op issue to BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b0;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h4;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // restart req to ROB
		expected_restart_req_valid = 1'b0;
		expected_restart_req_mispredict = 1'b0;
		expected_restart_req_ROB_index = 7'h0;
		expected_restart_req_PC = 32'h0;

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = {"\n\t\t",
            "issue: v 1: JAL p3, 0x1234; 0xABC->0x1CF0", "\n\t\t",
            "OC: v 0: JALR p2, 0x1C(p1:r); 0x0->0xABC, mispred 0xAB8", "\n\t\t",
            "EX: i NOP", "\n\t\t",
            "WB: i NOP", "\n\t\t",
			"activity: p1 read ack", "\n\t\t"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op issue to BRU IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0001;
		tb_issue_PC = 32'hABC;
		tb_issue_speculated_next_PC = 32'h1CF0;
		tb_issue_imm = 32'h1234;
		tb_issue_A_unneeded = 1'b1;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_unneeded = 1'b1;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_dest_PR = 7'h3;
		tb_issue_ROB_index = 7'h1;
	    // output feedback to BRU IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b1;
		tb_A_reg_read_port = 1'b1;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
            32'h0,
            32'h0,
            32'h0,
            32'h0,
            32'hAA0,
            32'hdeadbeef,
            32'h0,
            32'h0
        };
	    // forward data from PRF
		tb_forward_data_by_bank = {
            32'h0,
            32'h0,
            32'h0,
            32'h0
        };
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // restart req to ROB

		@(negedge CLK);

		// outputs:

	    // BRU op issue to BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h4;
		expected_WB_PR = 7'h0;
		expected_WB_ROB_index = 7'h0;
	    // writeback backpressure from PRF
	    // restart req to ROB
		expected_restart_req_valid = 1'b0;
		expected_restart_req_mispredict = 1'b0;
		expected_restart_req_ROB_index = 7'h0;
		expected_restart_req_PC = 32'h0;

		check_outputs();

        // ------------------------------------------------------------
        // finish:
        @(posedge CLK);
        
        test_case = "finish";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK);

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