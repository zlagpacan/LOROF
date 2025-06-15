/*
    Filename: stamofu_addr_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_addr_pipeline module. 
    Spec: LOROF/spec/design/stamofu_addr_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_addr_pipeline_tb ();

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
	logic tb_issue_is_store;
	logic tb_issue_is_amo;
	logic tb_issue_is_fence;
	logic [3:0] tb_issue_op;
	logic [11:0] tb_issue_imm12;
	logic tb_issue_A_forward;
	logic tb_issue_A_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_A_bank;
	logic tb_issue_B_forward;
	logic tb_issue_B_is_zero;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_B_bank;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_issue_cq_index;

    // output feedback to IQ
	logic DUT_issue_ready, expected_issue_ready;

    // reg read info and data from PRF
	logic tb_A_reg_read_ack;
	logic tb_A_reg_read_port;
	logic tb_B_reg_read_ack;
	logic tb_B_reg_read_port;
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] tb_reg_read_data_by_bank_by_port;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_forward_data_by_bank;

    // REQ stage info
	logic DUT_REQ_valid, expected_REQ_valid;
	logic DUT_REQ_is_mq, expected_REQ_is_mq;
	logic DUT_REQ_misaligned, expected_REQ_misaligned;
	logic DUT_REQ_misaligned_exception, expected_REQ_misaligned_exception;
	logic [VPN_WIDTH-1:0] DUT_REQ_VPN, expected_REQ_VPN;
	logic [PO_WIDTH-3:0] DUT_REQ_PO_word, expected_REQ_PO_word;
	logic [3:0] DUT_REQ_byte_mask, expected_REQ_byte_mask;
	logic [31:0] DUT_REQ_write_data, expected_REQ_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_REQ_cq_index, expected_REQ_cq_index;

    // REQ stage feedback
	logic tb_REQ_ack;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_addr_pipeline DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // op issue from IQ
		.issue_valid(tb_issue_valid),
		.issue_is_store(tb_issue_is_store),
		.issue_is_amo(tb_issue_is_amo),
		.issue_is_fence(tb_issue_is_fence),
		.issue_op(tb_issue_op),
		.issue_imm12(tb_issue_imm12),
		.issue_A_forward(tb_issue_A_forward),
		.issue_A_is_zero(tb_issue_A_is_zero),
		.issue_A_bank(tb_issue_A_bank),
		.issue_B_forward(tb_issue_B_forward),
		.issue_B_is_zero(tb_issue_B_is_zero),
		.issue_B_bank(tb_issue_B_bank),
		.issue_cq_index(tb_issue_cq_index),

	    // output feedback to IQ
		.issue_ready(DUT_issue_ready),

	    // reg read info and data from PRF
		.A_reg_read_ack(tb_A_reg_read_ack),
		.A_reg_read_port(tb_A_reg_read_port),
		.B_reg_read_ack(tb_B_reg_read_ack),
		.B_reg_read_port(tb_B_reg_read_port),
		.reg_read_data_by_bank_by_port(tb_reg_read_data_by_bank_by_port),

	    // forward data from PRF
		.forward_data_by_bank(tb_forward_data_by_bank),

	    // REQ stage info
		.REQ_valid(DUT_REQ_valid),
		.REQ_is_mq(DUT_REQ_is_mq),
		.REQ_misaligned(DUT_REQ_misaligned),
		.REQ_misaligned_exception(DUT_REQ_misaligned_exception),
		.REQ_VPN(DUT_REQ_VPN),
		.REQ_PO_word(DUT_REQ_PO_word),
		.REQ_byte_mask(DUT_REQ_byte_mask),
		.REQ_write_data(DUT_REQ_write_data),
		.REQ_cq_index(DUT_REQ_cq_index),

	    // REQ stage feedback
		.REQ_ack(tb_REQ_ack)
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

		if (expected_REQ_valid !== DUT_REQ_valid) begin
			$display("TB ERROR: expected_REQ_valid (%h) != DUT_REQ_valid (%h)",
				expected_REQ_valid, DUT_REQ_valid);
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

		if (expected_REQ_misaligned_exception !== DUT_REQ_misaligned_exception) begin
			$display("TB ERROR: expected_REQ_misaligned_exception (%h) != DUT_REQ_misaligned_exception (%h)",
				expected_REQ_misaligned_exception, DUT_REQ_misaligned_exception);
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

		if (expected_REQ_write_data !== DUT_REQ_write_data) begin
			$display("TB ERROR: expected_REQ_write_data (%h) != DUT_REQ_write_data (%h)",
				expected_REQ_write_data, DUT_REQ_write_data);
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
		tb_issue_is_store = 1'b0;
		tb_issue_is_amo = 1'b0;
		tb_issue_is_fence = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_cq_index = 0;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_ack = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_misaligned_exception = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b1111;
		expected_REQ_write_data = 32'h0;
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
		tb_issue_is_store = 1'b0;
		tb_issue_is_amo = 1'b0;
		tb_issue_is_fence = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_cq_index = 0;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_ack = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_misaligned_exception = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b1111;
		expected_REQ_write_data = 32'h0;
		expected_REQ_cq_index = 0;
	    // REQ stage feedback

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
	    // op issue from IQ
		tb_issue_valid = 1'b0;
		tb_issue_is_store = 1'b0;
		tb_issue_is_amo = 1'b0;
		tb_issue_is_fence = 1'b0;
		tb_issue_op = 4'b0000;
		tb_issue_imm12 = 12'h0;
		tb_issue_A_forward = 1'b0;
		tb_issue_A_is_zero = 1'b0;
		tb_issue_A_bank = 2'h0;
		tb_issue_B_forward = 1'b0;
		tb_issue_B_is_zero = 1'b0;
		tb_issue_B_bank = 2'h0;
		tb_issue_cq_index = 0;
	    // output feedback to IQ
	    // reg read info and data from PRF
		tb_A_reg_read_ack = 1'b0;
		tb_A_reg_read_port = 1'b0;
		tb_B_reg_read_ack = 1'b0;
		tb_B_reg_read_port = 1'b0;
		tb_reg_read_data_by_bank_by_port = {
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0,
			32'h0, 32'h0
		};
	    // forward data from PRF
		tb_forward_data_by_bank = {32'h0, 32'h0, 32'h0, 32'h0};
	    // REQ stage info
	    // REQ stage feedback
		tb_REQ_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // op issue from IQ
	    // output feedback to IQ
		expected_issue_ready = 1'b1;
	    // reg read info and data from PRF
	    // forward data from PRF
	    // REQ stage info
		expected_REQ_valid = 1'b0;
		expected_REQ_is_mq = 1'b0;
		expected_REQ_misaligned = 1'b0;
		expected_REQ_misaligned_exception = 1'b0;
		expected_REQ_VPN = 20'h0;
		expected_REQ_PO_word = 10'h0;
		expected_REQ_byte_mask = 4'b1111;
		expected_REQ_write_data = 32'h0;
		expected_REQ_cq_index = 0;
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