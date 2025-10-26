/*
    Filename: stamofu_lq_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_lq module. 
    Spec: LOROF/spec/design/stamofu_lq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter STAMOFU_LQ_ENTRIES_PER_BANK = 2;

module stamofu_lq_tb ();

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

    // REQ stage enq info
	logic tb_REQ_enq_valid;
	logic tb_REQ_enq_is_store;
	logic tb_REQ_enq_is_amo;
	logic tb_REQ_enq_is_fence;
	logic [3:0] tb_REQ_enq_op;
	logic tb_REQ_enq_is_mq;
	logic tb_REQ_enq_misaligned;
	logic tb_REQ_enq_misaligned_exception;
	logic [VPN_WIDTH-1:0] tb_REQ_enq_VPN;
	logic [PO_WIDTH-3:0] tb_REQ_enq_PO_word;
	logic [3:0] tb_REQ_enq_byte_mask;
	logic [31:0] tb_REQ_enq_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_REQ_enq_cq_index;

    // REQ stage enq feedback
	logic DUT_REQ_enq_ack, expected_REQ_enq_ack;

    // REQ stage deq info bank 0
	logic DUT_REQ_deq_bank0_valid, expected_REQ_deq_bank0_valid;

	logic DUT_REQ_deq_bank0_is_store, expected_REQ_deq_bank0_is_store;
	logic DUT_REQ_deq_bank0_is_amo, expected_REQ_deq_bank0_is_amo;
	logic DUT_REQ_deq_bank0_is_fence, expected_REQ_deq_bank0_is_fence;
	logic [3:0] DUT_REQ_deq_bank0_op, expected_REQ_deq_bank0_op;
	logic DUT_REQ_deq_bank0_is_mq, expected_REQ_deq_bank0_is_mq;
	logic DUT_REQ_deq_bank0_misaligned, expected_REQ_deq_bank0_misaligned;
	logic DUT_REQ_deq_bank0_misaligned_exception, expected_REQ_deq_bank0_misaligned_exception;
	logic [VPN_WIDTH-1:0] DUT_REQ_deq_bank0_VPN, expected_REQ_deq_bank0_VPN;
	logic [PO_WIDTH-3:0] DUT_REQ_deq_bank0_PO_word, expected_REQ_deq_bank0_PO_word;
	logic [3:0] DUT_REQ_deq_bank0_byte_mask, expected_REQ_deq_bank0_byte_mask;
	logic [31:0] DUT_REQ_deq_bank0_write_data, expected_REQ_deq_bank0_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_REQ_deq_bank0_cq_index, expected_REQ_deq_bank0_cq_index;

    // REQ stage deq feedback bank 0
	logic tb_REQ_deq_bank0_ack;

    // REQ stage deq info bank 1
	logic DUT_REQ_deq_bank1_valid, expected_REQ_deq_bank1_valid;

	logic DUT_REQ_deq_bank1_is_store, expected_REQ_deq_bank1_is_store;
	logic DUT_REQ_deq_bank1_is_amo, expected_REQ_deq_bank1_is_amo;
	logic DUT_REQ_deq_bank1_is_fence, expected_REQ_deq_bank1_is_fence;
	logic [3:0] DUT_REQ_deq_bank1_op, expected_REQ_deq_bank1_op;
	logic DUT_REQ_deq_bank1_is_mq, expected_REQ_deq_bank1_is_mq;
	logic DUT_REQ_deq_bank1_misaligned, expected_REQ_deq_bank1_misaligned;
	logic DUT_REQ_deq_bank1_misaligned_exception, expected_REQ_deq_bank1_misaligned_exception;
	logic [VPN_WIDTH-1:0] DUT_REQ_deq_bank1_VPN, expected_REQ_deq_bank1_VPN;
	logic [PO_WIDTH-3:0] DUT_REQ_deq_bank1_PO_word, expected_REQ_deq_bank1_PO_word;
	logic [3:0] DUT_REQ_deq_bank1_byte_mask, expected_REQ_deq_bank1_byte_mask;
	logic [31:0] DUT_REQ_deq_bank1_write_data, expected_REQ_deq_bank1_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_REQ_deq_bank1_cq_index, expected_REQ_deq_bank1_cq_index;

    // REQ stage deq feedback bank 1
	logic tb_REQ_deq_bank1_ack;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_lq #(
		.STAMOFU_LQ_ENTRIES_PER_BANK(STAMOFU_LQ_ENTRIES_PER_BANK)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // REQ stage enq info
		.REQ_enq_valid(tb_REQ_enq_valid),
		.REQ_enq_is_store(tb_REQ_enq_is_store),
		.REQ_enq_is_amo(tb_REQ_enq_is_amo),
		.REQ_enq_is_fence(tb_REQ_enq_is_fence),
		.REQ_enq_op(tb_REQ_enq_op),
		.REQ_enq_is_mq(tb_REQ_enq_is_mq),
		.REQ_enq_misaligned(tb_REQ_enq_misaligned),
		.REQ_enq_misaligned_exception(tb_REQ_enq_misaligned_exception),
		.REQ_enq_VPN(tb_REQ_enq_VPN),
		.REQ_enq_PO_word(tb_REQ_enq_PO_word),
		.REQ_enq_byte_mask(tb_REQ_enq_byte_mask),
		.REQ_enq_write_data(tb_REQ_enq_write_data),
		.REQ_enq_cq_index(tb_REQ_enq_cq_index),

	    // REQ stage enq feedback
		.REQ_enq_ack(DUT_REQ_enq_ack),

	    // REQ stage deq info bank 0
		.REQ_deq_bank0_valid(DUT_REQ_deq_bank0_valid),

		.REQ_deq_bank0_is_store(DUT_REQ_deq_bank0_is_store),
		.REQ_deq_bank0_is_amo(DUT_REQ_deq_bank0_is_amo),
		.REQ_deq_bank0_is_fence(DUT_REQ_deq_bank0_is_fence),
		.REQ_deq_bank0_op(DUT_REQ_deq_bank0_op),
		.REQ_deq_bank0_is_mq(DUT_REQ_deq_bank0_is_mq),
		.REQ_deq_bank0_misaligned(DUT_REQ_deq_bank0_misaligned),
		.REQ_deq_bank0_misaligned_exception(DUT_REQ_deq_bank0_misaligned_exception),
		.REQ_deq_bank0_VPN(DUT_REQ_deq_bank0_VPN),
		.REQ_deq_bank0_PO_word(DUT_REQ_deq_bank0_PO_word),
		.REQ_deq_bank0_byte_mask(DUT_REQ_deq_bank0_byte_mask),
		.REQ_deq_bank0_write_data(DUT_REQ_deq_bank0_write_data),
		.REQ_deq_bank0_cq_index(DUT_REQ_deq_bank0_cq_index),

	    // REQ stage deq feedback bank 0
		.REQ_deq_bank0_ack(tb_REQ_deq_bank0_ack),

	    // REQ stage deq info bank 1
		.REQ_deq_bank1_valid(DUT_REQ_deq_bank1_valid),

		.REQ_deq_bank1_is_store(DUT_REQ_deq_bank1_is_store),
		.REQ_deq_bank1_is_amo(DUT_REQ_deq_bank1_is_amo),
		.REQ_deq_bank1_is_fence(DUT_REQ_deq_bank1_is_fence),
		.REQ_deq_bank1_op(DUT_REQ_deq_bank1_op),
		.REQ_deq_bank1_is_mq(DUT_REQ_deq_bank1_is_mq),
		.REQ_deq_bank1_misaligned(DUT_REQ_deq_bank1_misaligned),
		.REQ_deq_bank1_misaligned_exception(DUT_REQ_deq_bank1_misaligned_exception),
		.REQ_deq_bank1_VPN(DUT_REQ_deq_bank1_VPN),
		.REQ_deq_bank1_PO_word(DUT_REQ_deq_bank1_PO_word),
		.REQ_deq_bank1_byte_mask(DUT_REQ_deq_bank1_byte_mask),
		.REQ_deq_bank1_write_data(DUT_REQ_deq_bank1_write_data),
		.REQ_deq_bank1_cq_index(DUT_REQ_deq_bank1_cq_index),

	    // REQ stage deq feedback bank 1
		.REQ_deq_bank1_ack(tb_REQ_deq_bank1_ack)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_REQ_enq_ack !== DUT_REQ_enq_ack) begin
			$display("TB ERROR: expected_REQ_enq_ack (%h) != DUT_REQ_enq_ack (%h)",
				expected_REQ_enq_ack, DUT_REQ_enq_ack);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_valid !== DUT_REQ_deq_bank0_valid) begin
			$display("TB ERROR: expected_REQ_deq_bank0_valid (%h) != DUT_REQ_deq_bank0_valid (%h)",
				expected_REQ_deq_bank0_valid, DUT_REQ_deq_bank0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_is_store !== DUT_REQ_deq_bank0_is_store) begin
			$display("TB ERROR: expected_REQ_deq_bank0_is_store (%h) != DUT_REQ_deq_bank0_is_store (%h)",
				expected_REQ_deq_bank0_is_store, DUT_REQ_deq_bank0_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_is_amo !== DUT_REQ_deq_bank0_is_amo) begin
			$display("TB ERROR: expected_REQ_deq_bank0_is_amo (%h) != DUT_REQ_deq_bank0_is_amo (%h)",
				expected_REQ_deq_bank0_is_amo, DUT_REQ_deq_bank0_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_is_fence !== DUT_REQ_deq_bank0_is_fence) begin
			$display("TB ERROR: expected_REQ_deq_bank0_is_fence (%h) != DUT_REQ_deq_bank0_is_fence (%h)",
				expected_REQ_deq_bank0_is_fence, DUT_REQ_deq_bank0_is_fence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_op !== DUT_REQ_deq_bank0_op) begin
			$display("TB ERROR: expected_REQ_deq_bank0_op (%h) != DUT_REQ_deq_bank0_op (%h)",
				expected_REQ_deq_bank0_op, DUT_REQ_deq_bank0_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_is_mq !== DUT_REQ_deq_bank0_is_mq) begin
			$display("TB ERROR: expected_REQ_deq_bank0_is_mq (%h) != DUT_REQ_deq_bank0_is_mq (%h)",
				expected_REQ_deq_bank0_is_mq, DUT_REQ_deq_bank0_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_misaligned !== DUT_REQ_deq_bank0_misaligned) begin
			$display("TB ERROR: expected_REQ_deq_bank0_misaligned (%h) != DUT_REQ_deq_bank0_misaligned (%h)",
				expected_REQ_deq_bank0_misaligned, DUT_REQ_deq_bank0_misaligned);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_misaligned_exception !== DUT_REQ_deq_bank0_misaligned_exception) begin
			$display("TB ERROR: expected_REQ_deq_bank0_misaligned_exception (%h) != DUT_REQ_deq_bank0_misaligned_exception (%h)",
				expected_REQ_deq_bank0_misaligned_exception, DUT_REQ_deq_bank0_misaligned_exception);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_VPN !== DUT_REQ_deq_bank0_VPN) begin
			$display("TB ERROR: expected_REQ_deq_bank0_VPN (%h) != DUT_REQ_deq_bank0_VPN (%h)",
				expected_REQ_deq_bank0_VPN, DUT_REQ_deq_bank0_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_PO_word !== DUT_REQ_deq_bank0_PO_word) begin
			$display("TB ERROR: expected_REQ_deq_bank0_PO_word (%h) != DUT_REQ_deq_bank0_PO_word (%h)",
				expected_REQ_deq_bank0_PO_word, DUT_REQ_deq_bank0_PO_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_byte_mask !== DUT_REQ_deq_bank0_byte_mask) begin
			$display("TB ERROR: expected_REQ_deq_bank0_byte_mask (%h) != DUT_REQ_deq_bank0_byte_mask (%h)",
				expected_REQ_deq_bank0_byte_mask, DUT_REQ_deq_bank0_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_write_data !== DUT_REQ_deq_bank0_write_data) begin
			$display("TB ERROR: expected_REQ_deq_bank0_write_data (%h) != DUT_REQ_deq_bank0_write_data (%h)",
				expected_REQ_deq_bank0_write_data, DUT_REQ_deq_bank0_write_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank0_cq_index !== DUT_REQ_deq_bank0_cq_index) begin
			$display("TB ERROR: expected_REQ_deq_bank0_cq_index (%h) != DUT_REQ_deq_bank0_cq_index (%h)",
				expected_REQ_deq_bank0_cq_index, DUT_REQ_deq_bank0_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_valid !== DUT_REQ_deq_bank1_valid) begin
			$display("TB ERROR: expected_REQ_deq_bank1_valid (%h) != DUT_REQ_deq_bank1_valid (%h)",
				expected_REQ_deq_bank1_valid, DUT_REQ_deq_bank1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_is_store !== DUT_REQ_deq_bank1_is_store) begin
			$display("TB ERROR: expected_REQ_deq_bank1_is_store (%h) != DUT_REQ_deq_bank1_is_store (%h)",
				expected_REQ_deq_bank1_is_store, DUT_REQ_deq_bank1_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_is_amo !== DUT_REQ_deq_bank1_is_amo) begin
			$display("TB ERROR: expected_REQ_deq_bank1_is_amo (%h) != DUT_REQ_deq_bank1_is_amo (%h)",
				expected_REQ_deq_bank1_is_amo, DUT_REQ_deq_bank1_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_is_fence !== DUT_REQ_deq_bank1_is_fence) begin
			$display("TB ERROR: expected_REQ_deq_bank1_is_fence (%h) != DUT_REQ_deq_bank1_is_fence (%h)",
				expected_REQ_deq_bank1_is_fence, DUT_REQ_deq_bank1_is_fence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_op !== DUT_REQ_deq_bank1_op) begin
			$display("TB ERROR: expected_REQ_deq_bank1_op (%h) != DUT_REQ_deq_bank1_op (%h)",
				expected_REQ_deq_bank1_op, DUT_REQ_deq_bank1_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_is_mq !== DUT_REQ_deq_bank1_is_mq) begin
			$display("TB ERROR: expected_REQ_deq_bank1_is_mq (%h) != DUT_REQ_deq_bank1_is_mq (%h)",
				expected_REQ_deq_bank1_is_mq, DUT_REQ_deq_bank1_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_misaligned !== DUT_REQ_deq_bank1_misaligned) begin
			$display("TB ERROR: expected_REQ_deq_bank1_misaligned (%h) != DUT_REQ_deq_bank1_misaligned (%h)",
				expected_REQ_deq_bank1_misaligned, DUT_REQ_deq_bank1_misaligned);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_misaligned_exception !== DUT_REQ_deq_bank1_misaligned_exception) begin
			$display("TB ERROR: expected_REQ_deq_bank1_misaligned_exception (%h) != DUT_REQ_deq_bank1_misaligned_exception (%h)",
				expected_REQ_deq_bank1_misaligned_exception, DUT_REQ_deq_bank1_misaligned_exception);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_VPN !== DUT_REQ_deq_bank1_VPN) begin
			$display("TB ERROR: expected_REQ_deq_bank1_VPN (%h) != DUT_REQ_deq_bank1_VPN (%h)",
				expected_REQ_deq_bank1_VPN, DUT_REQ_deq_bank1_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_PO_word !== DUT_REQ_deq_bank1_PO_word) begin
			$display("TB ERROR: expected_REQ_deq_bank1_PO_word (%h) != DUT_REQ_deq_bank1_PO_word (%h)",
				expected_REQ_deq_bank1_PO_word, DUT_REQ_deq_bank1_PO_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_byte_mask !== DUT_REQ_deq_bank1_byte_mask) begin
			$display("TB ERROR: expected_REQ_deq_bank1_byte_mask (%h) != DUT_REQ_deq_bank1_byte_mask (%h)",
				expected_REQ_deq_bank1_byte_mask, DUT_REQ_deq_bank1_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_write_data !== DUT_REQ_deq_bank1_write_data) begin
			$display("TB ERROR: expected_REQ_deq_bank1_write_data (%h) != DUT_REQ_deq_bank1_write_data (%h)",
				expected_REQ_deq_bank1_write_data, DUT_REQ_deq_bank1_write_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_bank1_cq_index !== DUT_REQ_deq_bank1_cq_index) begin
			$display("TB ERROR: expected_REQ_deq_bank1_cq_index (%h) != DUT_REQ_deq_bank1_cq_index (%h)",
				expected_REQ_deq_bank1_cq_index, DUT_REQ_deq_bank1_cq_index);
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
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0000;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h00000;
		tb_REQ_enq_PO_word = 10'h000;
		tb_REQ_enq_byte_mask = 4'b0000;
		tb_REQ_enq_write_data = 32'h00000000;
		tb_REQ_enq_cq_index = 0;
	    // REQ stage enq feedback
	    // REQ stage deq info bank 0
	    // REQ stage deq feedback bank 0
		tb_REQ_deq_bank0_ack = 1'b0;
	    // REQ stage deq info bank 1
	    // REQ stage deq feedback bank 1
		tb_REQ_deq_bank1_ack = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b0;
	    // REQ stage deq info bank 0
		expected_REQ_deq_bank0_valid = 1'b0;
		expected_REQ_deq_bank0_is_store = 1'b0;
		expected_REQ_deq_bank0_is_amo = 1'b0;
		expected_REQ_deq_bank0_is_fence = 1'b0;
		expected_REQ_deq_bank0_op = 4'b0000;
		expected_REQ_deq_bank0_is_mq = 1'b0;
		expected_REQ_deq_bank0_misaligned = 1'b0;
		expected_REQ_deq_bank0_misaligned_exception = 1'b0;
		expected_REQ_deq_bank0_VPN = 20'h00000;
		expected_REQ_deq_bank0_PO_word = 10'h000;
		expected_REQ_deq_bank0_byte_mask = 4'b0000;
		expected_REQ_deq_bank0_write_data = 32'h00000000;
		expected_REQ_deq_bank0_cq_index = 0;
	    // REQ stage deq feedback bank 0
	    // REQ stage deq info bank 1
		expected_REQ_deq_bank1_valid = 1'b0;
		expected_REQ_deq_bank1_is_store = 1'b0;
		expected_REQ_deq_bank1_is_amo = 1'b0;
		expected_REQ_deq_bank1_is_fence = 1'b0;
		expected_REQ_deq_bank1_op = 4'b0000;
		expected_REQ_deq_bank1_is_mq = 1'b0;
		expected_REQ_deq_bank1_misaligned = 1'b0;
		expected_REQ_deq_bank1_misaligned_exception = 1'b0;
		expected_REQ_deq_bank1_VPN = 20'h00000;
		expected_REQ_deq_bank1_PO_word = 10'h000;
		expected_REQ_deq_bank1_byte_mask = 4'b0000;
		expected_REQ_deq_bank1_write_data = 32'h00000000;
		expected_REQ_deq_bank1_cq_index = 0;
	    // REQ stage deq feedback bank 1

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0000;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h00000;
		tb_REQ_enq_PO_word = 10'h000;
		tb_REQ_enq_byte_mask = 4'b0000;
		tb_REQ_enq_write_data = 32'h00000000;
		tb_REQ_enq_cq_index = 0;
	    // REQ stage enq feedback
	    // REQ stage deq info bank 0
	    // REQ stage deq feedback bank 0
		tb_REQ_deq_bank0_ack = 1'b0;
	    // REQ stage deq info bank 1
	    // REQ stage deq feedback bank 1
		tb_REQ_deq_bank1_ack = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b0;
	    // REQ stage deq info bank 0
		expected_REQ_deq_bank0_valid = 1'b0;
		expected_REQ_deq_bank0_is_store = 1'b0;
		expected_REQ_deq_bank0_is_amo = 1'b0;
		expected_REQ_deq_bank0_is_fence = 1'b0;
		expected_REQ_deq_bank0_op = 4'b0000;
		expected_REQ_deq_bank0_is_mq = 1'b0;
		expected_REQ_deq_bank0_misaligned = 1'b0;
		expected_REQ_deq_bank0_misaligned_exception = 1'b0;
		expected_REQ_deq_bank0_VPN = 20'h00000;
		expected_REQ_deq_bank0_PO_word = 10'h000;
		expected_REQ_deq_bank0_byte_mask = 4'b0000;
		expected_REQ_deq_bank0_write_data = 32'h00000000;
		expected_REQ_deq_bank0_cq_index = 0;
	    // REQ stage deq feedback bank 0
	    // REQ stage deq info bank 1
		expected_REQ_deq_bank1_valid = 1'b0;
		expected_REQ_deq_bank1_is_store = 1'b0;
		expected_REQ_deq_bank1_is_amo = 1'b0;
		expected_REQ_deq_bank1_is_fence = 1'b0;
		expected_REQ_deq_bank1_op = 4'b0000;
		expected_REQ_deq_bank1_is_mq = 1'b0;
		expected_REQ_deq_bank1_misaligned = 1'b0;
		expected_REQ_deq_bank1_misaligned_exception = 1'b0;
		expected_REQ_deq_bank1_VPN = 20'h00000;
		expected_REQ_deq_bank1_PO_word = 10'h000;
		expected_REQ_deq_bank1_byte_mask = 4'b0000;
		expected_REQ_deq_bank1_write_data = 32'h00000000;
		expected_REQ_deq_bank1_cq_index = 0;
	    // REQ stage deq feedback bank 1

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
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0000;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h00000;
		tb_REQ_enq_PO_word = 10'h000;
		tb_REQ_enq_byte_mask = 4'b0000;
		tb_REQ_enq_write_data = 32'h00000000;
		tb_REQ_enq_cq_index = 0;
	    // REQ stage enq feedback
	    // REQ stage deq info bank 0
	    // REQ stage deq feedback bank 0
		tb_REQ_deq_bank0_ack = 1'b0;
	    // REQ stage deq info bank 1
	    // REQ stage deq feedback bank 1
		tb_REQ_deq_bank1_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b0;
	    // REQ stage deq info bank 0
		expected_REQ_deq_bank0_valid = 1'b0;
		expected_REQ_deq_bank0_is_store = 1'b0;
		expected_REQ_deq_bank0_is_amo = 1'b0;
		expected_REQ_deq_bank0_is_fence = 1'b0;
		expected_REQ_deq_bank0_op = 4'b0000;
		expected_REQ_deq_bank0_is_mq = 1'b0;
		expected_REQ_deq_bank0_misaligned = 1'b0;
		expected_REQ_deq_bank0_misaligned_exception = 1'b0;
		expected_REQ_deq_bank0_VPN = 20'h00000;
		expected_REQ_deq_bank0_PO_word = 10'h000;
		expected_REQ_deq_bank0_byte_mask = 4'b0000;
		expected_REQ_deq_bank0_write_data = 32'h00000000;
		expected_REQ_deq_bank0_cq_index = 0;
	    // REQ stage deq feedback bank 0
	    // REQ stage deq info bank 1
		expected_REQ_deq_bank1_valid = 1'b0;
		expected_REQ_deq_bank1_is_store = 1'b0;
		expected_REQ_deq_bank1_is_amo = 1'b0;
		expected_REQ_deq_bank1_is_fence = 1'b0;
		expected_REQ_deq_bank1_op = 4'b0000;
		expected_REQ_deq_bank1_is_mq = 1'b0;
		expected_REQ_deq_bank1_misaligned = 1'b0;
		expected_REQ_deq_bank1_misaligned_exception = 1'b0;
		expected_REQ_deq_bank1_VPN = 20'h00000;
		expected_REQ_deq_bank1_PO_word = 10'h000;
		expected_REQ_deq_bank1_byte_mask = 4'b0000;
		expected_REQ_deq_bank1_write_data = 32'h00000000;
		expected_REQ_deq_bank1_cq_index = 0;
	    // REQ stage deq feedback bank 1

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