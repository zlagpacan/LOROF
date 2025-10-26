/*
    Filename: ldu_addr_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for ldu_addr_pipeline module. 
    Spec: LOROF/spec/design/ldu_addr_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module ldu_addr_pipeline_tb ();

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


    // op issue from IQ
	logic tb_issue_valid;
	logic [3:0] tb_issue_op;
	logic [11:0] tb_issue_imm12;
	logic tb_issue_A_forward;
	logic tb_issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_A_bank;
	logic [LOG_LDU_CQ_ENTRIES-1:0] tb_issue_cq_index;

    // output feedback to IQ
	logic DUT_issue_ready, expected_issue_ready;

    // reg read info and data from PRF
	logic tb_A_reg_read_ack;
	logic tb_A_reg_read_port;
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] tb_reg_read_data_by_bank_by_port;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_forward_data_by_bank;

    // REQ stage info
	logic DUT_REQ_bank0_valid, expected_REQ_bank0_valid;
	logic DUT_REQ_bank1_valid, expected_REQ_bank1_valid;
	logic DUT_REQ_is_mq, expected_REQ_is_mq;
	logic DUT_REQ_misaligned, expected_REQ_misaligned;
	logic [VPN_WIDTH-1:0] DUT_REQ_VPN, expected_REQ_VPN;
	logic [PO_WIDTH-3:0] DUT_REQ_PO_word, expected_REQ_PO_word;
	logic [3:0] DUT_REQ_byte_mask, expected_REQ_byte_mask;
	logic [LOG_LDU_CQ_ENTRIES-1:0] DUT_REQ_cq_index, expected_REQ_cq_index;

    // REQ stage feedback
	logic tb_REQ_bank0_early_ready;
	logic tb_REQ_bank1_early_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ldu_addr_pipeline DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // op issue from IQ
		.issue_valid(tb_issue_valid),
		.issue_op(tb_issue_op),
		.issue_imm12(tb_issue_imm12),
		.issue_A_forward(tb_issue_A_forward),
		.issue_A_is_zero(tb_issue_A_is_zero),
		.issue_A_bank(tb_issue_A_bank),
		.issue_cq_index(tb_issue_cq_index),

	    // output feedback to IQ
		.issue_ready(DUT_issue_ready),

	    // reg read info and data from PRF
		.A_reg_read_ack(tb_A_reg_read_ack),
		.A_reg_read_port(tb_A_reg_read_port),
		.reg_read_data_by_bank_by_port(tb_reg_read_data_by_bank_by_port),

	    // forward data from PRF
		.forward_data_by_bank(tb_forward_data_by_bank),

	    // REQ stage info
		.REQ_bank0_valid(DUT_REQ_bank0_valid),
		.REQ_bank1_valid(DUT_REQ_bank1_valid),
		.REQ_is_mq(DUT_REQ_is_mq),
		.REQ_misaligned(DUT_REQ_misaligned),
		.REQ_VPN(DUT_REQ_VPN),
		.REQ_PO_word(DUT_REQ_PO_word),
		.REQ_byte_mask(DUT_REQ_byte_mask),
		.REQ_cq_index(DUT_REQ_cq_index),

	    // REQ stage feedback
		.REQ_bank0_early_ready(tb_REQ_bank0_early_ready),
		.REQ_bank1_early_ready(tb_REQ_bank1_early_ready)
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

		if (expected_REQ_bank0_valid !== DUT_REQ_bank0_valid) begin
			$display("TB ERROR: expected_REQ_bank0_valid (%h) != DUT_REQ_bank0_valid (%h)",
				expected_REQ_bank0_valid, DUT_REQ_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_bank1_valid !== DUT_REQ_bank1_valid) begin
			$display("TB ERROR: expected_REQ_bank1_valid (%h) != DUT_REQ_bank1_valid (%h)",
				expected_REQ_bank1_valid, DUT_REQ_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_is_mq !== DUT_REQ_is_mq) begin
			$display("TB ERROR: expected_REQ_is_mq (%h) != DUT_REQ_is_mq (%h)",
				expected_REQ_is_mq, DUT_REQ_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_misaligned !== DUT_REQ_misaligned) begin
			$display("TB ERROR: expected_REQ_misaligned (%h) != DUT_REQ_misaligned (%h)",
				expected_REQ_misaligned, DUT_REQ_misaligned);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_VPN !== DUT_REQ_VPN) begin
			$display("TB ERROR: expected_REQ_VPN (%h) != DUT_REQ_VPN (%h)",
				expected_REQ_VPN, DUT_REQ_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_PO_word !== DUT_REQ_PO_word) begin
			$display("TB ERROR: expected_REQ_PO_word (%h) != DUT_REQ_PO_word (%h)",
				expected_REQ_PO_word, DUT_REQ_PO_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_byte_mask !== DUT_REQ_byte_mask) begin
			$display("TB ERROR: expected_REQ_byte_mask (%h) != DUT_REQ_byte_mask (%h)",
				expected_REQ_byte_mask, DUT_REQ_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_cq_index !== DUT_REQ_cq_index) begin
			$display("TB ERROR: expected_REQ_cq_index (%h) != DUT_REQ_cq_index (%h)",
				expected_REQ_cq_index, DUT_REQ_cq_index);
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
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_cq_index = 0;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 0;
	    // REQ stage feedback

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_cq_index = 0;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 0;
	    // REQ stage feedback

		check_outputs();

        // ------------------------------------------------------------
        // sequence:
        test_case = "sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: i",
			"\n\t\tREQ: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_cq_index = 0;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 0;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 0: LB 0(zero)",
			"\n\t\tOC: i",
			"\n\t\tREQ: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b1;
		tb_issue_A_bank = 2'h0;
		tb_issue_cq_index = 0;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 0;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 3: LH 0x12(p9:r=0x23456789)",
			"\n\t\tOC: v 0: LB 0(zero)",
			"\n\t\tREQ: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0001;
		tb_issue_imm12 = 12'h12;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h1;
		tb_issue_cq_index = 3;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 0;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 4: LW 0xFFE(p77:f=0x77777777)",
			"\n\t\tOC: v 3: LH 0x12(p9:R=0x12345678)",
			"\n\t\tREQ: v 0: LB 0(zero)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'hFFE;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 4;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b1;
		tb_A_reg_read_port = 1'b1;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h12345678, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 0;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i 13: LBU 0x7(p21:r=0x44)",
			"\n\t\tOC: v 4: LW 0xFFE(p77:fS=0x77777777)",
			"\n\t\tREQ: v 3: LH 0x12(p9:R=0x12345678) (no ack)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b1100;
		tb_issue_imm12 = 12'h7;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h1;
		tb_issue_cq_index = 13;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h77777777,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h12345;
		expected_REQ_PO_word = ('h678 + 'h12) >> 2;
		expected_REQ_byte_mask = 4'b1100;
		expected_REQ_cq_index = 3;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 13: LBU 0x7(p21:r=0x44)",
			"\n\t\tOC: v 4: LW 0xFFE(p77:S=0x77777777)",
			"\n\t\tREQ: v 3: LH 0x12(p9:R=0x12345678)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b1100;
		tb_issue_imm12 = 12'h7;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h1;
		tb_issue_cq_index = 13;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h12345;
		expected_REQ_PO_word = ('h678 + 'h12) >> 2;
		expected_REQ_byte_mask = 4'b1100;
		expected_REQ_cq_index = 3;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 20: LHU 0x151(p6:r=0xAAAA)",
			"\n\t\tOC: v 13: LBU 0x7(p21:r=0x44)",
			"\n\t\tREQ: v 4: LW 0xFFE(p77:S=0x77777777) (new misaligned)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b1101;
		tb_issue_imm12 = 12'h151;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h2;
		tb_issue_cq_index = 20;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b1;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h77777;
		expected_REQ_PO_word = ('h777 - 'h2) >> 2;
		expected_REQ_byte_mask = 4'b1110;
		expected_REQ_cq_index = 4;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 20: LHU 0x151(p6:r=0xAAAA)",
			"\n\t\tOC: v 13: LBU 0x7(p21:R=0x44)",
			"\n\t\tREQ: m 4: LW 0xFFE(p77:S=0x77777777)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b1101;
		tb_issue_imm12 = 12'h151;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h2;
		tb_issue_cq_index = 20;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b1;
		tb_A_reg_read_port = 1'b1;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h44, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b1;
		expected_REQ_is_mq = 1'b1;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h77777;
		expected_REQ_PO_word = ('h777 - 'h2 + 'h4) >> 2;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 4;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 25: LW 0x1(p50:r=0xFFFF)",
			"\n\t\tOC: v 20: LHU 0x151(p6:R=0xAAAA)",
			"\n\t\tREQ: v 13: LBU 0x7(p21:R=0x44)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b1010;
		tb_issue_imm12 = 12'h001;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_cq_index = 25;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b1;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'hAAAA,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h00000;
		expected_REQ_PO_word = ('h44 + 'h7) >> 2;
		expected_REQ_byte_mask = 4'b1000;
		expected_REQ_cq_index = 13;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 26: LW 0x2(p53:f=0x0F0F0F0F)",
			"\n\t\tOC: v 25: LW 0x1(p50:r=0xFFFF) (no ack)",
			"\n\t\tREQ: v 20: LHU 0x151(p6:R=0xAAAA) (new misaligned)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h002;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b1;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h0000A;
		expected_REQ_PO_word = ('hAAA + 'h151) >> 2;
		expected_REQ_byte_mask = 4'b1000;
		expected_REQ_cq_index = 20;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 26: LW 0x2(p53:f=0x0F0F0F0F)",
			"\n\t\tOC: v 25: LW 0x1(p50:r=0xFFFF) (no ack)",
			"\n\t\tREQ: m 20: LHU 0x151(p6:R=0xAAAA)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h002;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b1;
		expected_REQ_is_mq = 1'b1;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h0000A;
		expected_REQ_PO_word = ('hAAA + 'h151 + 'h4) >> 2;
		expected_REQ_byte_mask = 4'b0001;
		expected_REQ_cq_index = 20;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: v 26: LW 0x3(p53:f=0x0F0F0F0F)",
			"\n\t\tOC: v 25: LW 0x1(p50:R=0xFFFF)",
			"\n\t\tREQ: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b1;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b1;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'hFFFF
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h00000;
		expected_REQ_PO_word = 12'h000;
		expected_REQ_byte_mask = 4'b1110;
		expected_REQ_cq_index = 25;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: v 26: LW 0x3(p53:F=0x0F0F0F0F)",
			"\n\t\tREQ: v 25: LW 0x1(p50:R=0xFFFF) (no ack)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0F0F0F0F,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b0;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h00010;
		expected_REQ_PO_word = ('h000 + 'h000) >> 2;
		expected_REQ_byte_mask = 4'b1111;
		expected_REQ_cq_index = 25;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: v 26: LW 0x3(p53:F=0x0F0F0F0F)",
			"\n\t\tREQ: v 25: LW 0x1(p50:R=0xFFFF)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_VPN = 20'h00010;
		expected_REQ_PO_word = ('h000 + 'h000) >> 2;
		expected_REQ_byte_mask = 4'b1111;
		expected_REQ_cq_index = 25;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: i",
			"\n\t\tREQ: v 26: LW 0x3(p53:F=0x0F0F0F0F) (no ack)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h0F0F0;
		expected_REQ_PO_word = ('hF0F + 'h3) >> 2;
		expected_REQ_byte_mask = 4'b1100;
		expected_REQ_cq_index = 26;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: i",
			"\n\t\tAC: v 26: LW 0x3(p53:F=0x0F0F0F0F) (no ack)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h0F0F0;
		expected_REQ_PO_word = ('hF0F + 'h3) >> 2;
		expected_REQ_byte_mask = 4'b1100;
		expected_REQ_cq_index = 26;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: i",
			"\n\t\tREQ: v 26: LW 0x3(p53:F=0x0F0F0F0F) (new misaligned)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h0F0F0;
		expected_REQ_PO_word = ('hF0F + 'h3) >> 2;
		expected_REQ_byte_mask = 4'b1100;
		expected_REQ_cq_index = 26;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: i",
			"\n\t\tREQ: m 26: LW 0x3(p53:F=0x0F0F0F0F) (no ack)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b0;
		tb_REQ_bank1_early_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b1;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h0F0F0;
		expected_REQ_PO_word = ('hF0F + 'h3 + 'h4) >> 2;
		expected_REQ_byte_mask = 4'b0011;
		expected_REQ_cq_index = 26;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: i",
			"\n\t\tREQ: m 26: LW 0x3(p53:F=0x0F0F0F0F)"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b1;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b1;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h0F0F0;
		expected_REQ_PO_word = ('hF0F + 'h3 + 'h4) >> 2;
		expected_REQ_byte_mask = 4'b0011;
		expected_REQ_cq_index = 26;
	    // REQ stage feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tIS: i",
			"\n\t\tOC: i",
			"\n\t\tREQ: i"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_op = 4'b0010;
		tb_issue_imm12 = 12'h003;
		tb_issue_A_forward = 1'b1;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h3;
		tb_issue_cq_index = 26;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {
			32'h0,
			32'h0,
			32'h0,
			32'h0
		};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_bank0_early_ready = 1'b1;
		tb_REQ_bank1_early_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_bank0_valid = 1'b0;
		expected_REQ_bank1_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b1;
		expected_REQ_VPN = 20'h00000;
		expected_REQ_PO_word = ('h000 + 'h000) >> 2;
		expected_REQ_byte_mask = 4'b1000;
		expected_REQ_cq_index = 26;
	    // REQ stage feedback

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