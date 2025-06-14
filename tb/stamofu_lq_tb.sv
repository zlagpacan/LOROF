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

    // REQ stage deq info
	logic DUT_REQ_deq_valid, expected_REQ_deq_valid;
	logic DUT_REQ_deq_is_store, expected_REQ_deq_is_store;
	logic DUT_REQ_deq_is_amo, expected_REQ_deq_is_amo;
	logic DUT_REQ_deq_is_fence, expected_REQ_deq_is_fence;
	logic [3:0] DUT_REQ_deq_op, expected_REQ_deq_op;
	logic DUT_REQ_deq_is_mq, expected_REQ_deq_is_mq;
	logic DUT_REQ_deq_misaligned, expected_REQ_deq_misaligned;
	logic DUT_REQ_deq_misaligned_exception, expected_REQ_deq_misaligned_exception;
	logic [VPN_WIDTH-1:0] DUT_REQ_deq_VPN, expected_REQ_deq_VPN;
	logic [PO_WIDTH-3:0] DUT_REQ_deq_PO_word, expected_REQ_deq_PO_word;
	logic [3:0] DUT_REQ_deq_byte_mask, expected_REQ_deq_byte_mask;
	logic [31:0] DUT_REQ_deq_write_data, expected_REQ_deq_write_data;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_REQ_deq_cq_index, expected_REQ_deq_cq_index;

    // REQ stage deq feedback
	logic tb_REQ_deq_ack;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_lq #(
		.STAMOFU_LQ_ENTRIES(4)
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

	    // REQ stage deq info
		.REQ_deq_valid(DUT_REQ_deq_valid),
		.REQ_deq_is_store(DUT_REQ_deq_is_store),
		.REQ_deq_is_amo(DUT_REQ_deq_is_amo),
		.REQ_deq_is_fence(DUT_REQ_deq_is_fence),
		.REQ_deq_op(DUT_REQ_deq_op),
		.REQ_deq_is_mq(DUT_REQ_deq_is_mq),
		.REQ_deq_misaligned(DUT_REQ_deq_misaligned),
		.REQ_deq_misaligned_exception(DUT_REQ_deq_misaligned_exception),
		.REQ_deq_VPN(DUT_REQ_deq_VPN),
		.REQ_deq_PO_word(DUT_REQ_deq_PO_word),
		.REQ_deq_byte_mask(DUT_REQ_deq_byte_mask),
		.REQ_deq_write_data(DUT_REQ_deq_write_data),
		.REQ_deq_cq_index(DUT_REQ_deq_cq_index),

	    // REQ stage deq feedback
		.REQ_deq_ack(tb_REQ_deq_ack)
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

		if (expected_REQ_deq_valid !== DUT_REQ_deq_valid) begin
			$display("TB ERROR: expected_REQ_deq_valid (%h) != DUT_REQ_deq_valid (%h)",
				expected_REQ_deq_valid, DUT_REQ_deq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_is_store !== DUT_REQ_deq_is_store) begin
			$display("TB ERROR: expected_REQ_deq_is_store (%h) != DUT_REQ_deq_is_store (%h)",
				expected_REQ_deq_is_store, DUT_REQ_deq_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_is_amo !== DUT_REQ_deq_is_amo) begin
			$display("TB ERROR: expected_REQ_deq_is_amo (%h) != DUT_REQ_deq_is_amo (%h)",
				expected_REQ_deq_is_amo, DUT_REQ_deq_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_is_fence !== DUT_REQ_deq_is_fence) begin
			$display("TB ERROR: expected_REQ_deq_is_fence (%h) != DUT_REQ_deq_is_fence (%h)",
				expected_REQ_deq_is_fence, DUT_REQ_deq_is_fence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_op !== DUT_REQ_deq_op) begin
			$display("TB ERROR: expected_REQ_deq_op (%h) != DUT_REQ_deq_op (%h)",
				expected_REQ_deq_op, DUT_REQ_deq_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_is_mq !== DUT_REQ_deq_is_mq) begin
			$display("TB ERROR: expected_REQ_deq_is_mq (%h) != DUT_REQ_deq_is_mq (%h)",
				expected_REQ_deq_is_mq, DUT_REQ_deq_is_mq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_misaligned !== DUT_REQ_deq_misaligned) begin
			$display("TB ERROR: expected_REQ_deq_misaligned (%h) != DUT_REQ_deq_misaligned (%h)",
				expected_REQ_deq_misaligned, DUT_REQ_deq_misaligned);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_misaligned_exception !== DUT_REQ_deq_misaligned_exception) begin
			$display("TB ERROR: expected_REQ_deq_misaligned_exception (%h) != DUT_REQ_deq_misaligned_exception (%h)",
				expected_REQ_deq_misaligned_exception, DUT_REQ_deq_misaligned_exception);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_VPN !== DUT_REQ_deq_VPN) begin
			$display("TB ERROR: expected_REQ_deq_VPN (%h) != DUT_REQ_deq_VPN (%h)",
				expected_REQ_deq_VPN, DUT_REQ_deq_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_PO_word !== DUT_REQ_deq_PO_word) begin
			$display("TB ERROR: expected_REQ_deq_PO_word (%h) != DUT_REQ_deq_PO_word (%h)",
				expected_REQ_deq_PO_word, DUT_REQ_deq_PO_word);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_byte_mask !== DUT_REQ_deq_byte_mask) begin
			$display("TB ERROR: expected_REQ_deq_byte_mask (%h) != DUT_REQ_deq_byte_mask (%h)",
				expected_REQ_deq_byte_mask, DUT_REQ_deq_byte_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_write_data !== DUT_REQ_deq_write_data) begin
			$display("TB ERROR: expected_REQ_deq_write_data (%h) != DUT_REQ_deq_write_data (%h)",
				expected_REQ_deq_write_data, DUT_REQ_deq_write_data);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_REQ_deq_cq_index !== DUT_REQ_deq_cq_index) begin
			$display("TB ERROR: expected_REQ_deq_cq_index (%h) != DUT_REQ_deq_cq_index (%h)",
				expected_REQ_deq_cq_index, DUT_REQ_deq_cq_index);
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
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b0;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h00000;
		expected_REQ_deq_PO_word = 10'h000;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'h00000000;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

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
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b0;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h00000;
		expected_REQ_deq_PO_word = 10'h000;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'h00000000;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - enq 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0000;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h0f0f0;
		tb_REQ_enq_PO_word = 10'h0f0;
		tb_REQ_enq_byte_mask = 4'b0000;
		tb_REQ_enq_write_data = 32'hf0f0f0f0;
		tb_REQ_enq_cq_index = 0;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b0;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h00000;
		expected_REQ_deq_PO_word = 10'h000;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'h00000000;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, i, i, i} - enq 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b1;
		tb_REQ_enq_is_amo = 1'b1;
		tb_REQ_enq_is_fence = 1'b1;
		tb_REQ_enq_op = 4'b0001;
		tb_REQ_enq_is_mq = 1'b1;
		tb_REQ_enq_misaligned = 1'b1;
		tb_REQ_enq_misaligned_exception = 1'b1;
		tb_REQ_enq_VPN = 20'h1e1e1;
		tb_REQ_enq_PO_word = 10'h1e1;
		tb_REQ_enq_byte_mask = 4'b0001;
		tb_REQ_enq_write_data = 32'he1e1e1e1;
		tb_REQ_enq_cq_index = 1;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h0f0f0;
		expected_REQ_deq_PO_word = 10'h0f0;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'hf0f0f0f0;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, i, i} - enq 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0010;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h2d2d2;
		tb_REQ_enq_PO_word = 10'h2d2;
		tb_REQ_enq_byte_mask = 4'b0010;
		tb_REQ_enq_write_data = 32'hd2d2d2d2;
		tb_REQ_enq_cq_index = 2;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h0f0f0;
		expected_REQ_deq_PO_word = 10'h0f0;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'hf0f0f0f0;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, 2, i} - enq 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b1;
		tb_REQ_enq_is_amo = 1'b1;
		tb_REQ_enq_is_fence = 1'b1;
		tb_REQ_enq_op = 4'b0011;
		tb_REQ_enq_is_mq = 1'b1;
		tb_REQ_enq_misaligned = 1'b1;
		tb_REQ_enq_misaligned_exception = 1'b1;
		tb_REQ_enq_VPN = 20'h3c3c3;
		tb_REQ_enq_PO_word = 10'h3c3;
		tb_REQ_enq_byte_mask = 4'b0011;
		tb_REQ_enq_write_data = 32'hc3c3c3c3;
		tb_REQ_enq_cq_index = 3;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h0f0f0;
		expected_REQ_deq_PO_word = 10'h0f0;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'hf0f0f0f0;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, 2, 3} - failed enq 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0100;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h4b4b4;
		tb_REQ_enq_PO_word = 10'h4b4;
		tb_REQ_enq_byte_mask = 4'b0100;
		tb_REQ_enq_write_data = 32'hb4b4b4b4;
		tb_REQ_enq_cq_index = 4;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b0;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h0f0f0;
		expected_REQ_deq_PO_word = 10'h0f0;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'hf0f0f0f0;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, 2, 3} - failed enq 4, deq 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0100;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h4b4b4;
		tb_REQ_enq_PO_word = 10'h4b4;
		tb_REQ_enq_byte_mask = 4'b0100;
		tb_REQ_enq_write_data = 32'hb4b4b4b4;
		tb_REQ_enq_cq_index = 4;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b0;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0000;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h0f0f0;
		expected_REQ_deq_PO_word = 10'h0f0;
		expected_REQ_deq_byte_mask = 4'b0000;
		expected_REQ_deq_write_data = 32'hf0f0f0f0;
		expected_REQ_deq_cq_index = 0;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, 1, 2, 3} - enq 4, deq 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0100;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h4b4b4;
		tb_REQ_enq_PO_word = 10'h4b4;
		tb_REQ_enq_byte_mask = 4'b0100;
		tb_REQ_enq_write_data = 32'hb4b4b4b4;
		tb_REQ_enq_cq_index = 4;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b1;
		expected_REQ_deq_is_amo = 1'b1;
		expected_REQ_deq_is_fence = 1'b1;
		expected_REQ_deq_op = 4'b0001;
		expected_REQ_deq_is_mq = 1'b1;
		expected_REQ_deq_misaligned = 1'b1;
		expected_REQ_deq_misaligned_exception = 1'b1;
		expected_REQ_deq_VPN = 20'h1e1e1;
		expected_REQ_deq_PO_word = 10'h1e1;
		expected_REQ_deq_byte_mask = 4'b0001;
		expected_REQ_deq_write_data = 32'he1e1e1e1;
		expected_REQ_deq_cq_index = 1;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, i, 2, 3} - enq 5, deq 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b1;
		tb_REQ_enq_is_amo = 1'b1;
		tb_REQ_enq_is_fence = 1'b1;
		tb_REQ_enq_op = 4'b0101;
		tb_REQ_enq_is_mq = 1'b1;
		tb_REQ_enq_misaligned = 1'b1;
		tb_REQ_enq_misaligned_exception = 1'b1;
		tb_REQ_enq_VPN = 20'h5a5a5;
		tb_REQ_enq_PO_word = 10'h5a5;
		tb_REQ_enq_byte_mask = 4'b0101;
		tb_REQ_enq_write_data = 32'ha5a5a5a5;
		tb_REQ_enq_cq_index = 5;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0010;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h2d2d2;
		expected_REQ_deq_PO_word = 10'h2d2;
		expected_REQ_deq_byte_mask = 4'b0010;
		expected_REQ_deq_write_data = 32'hd2d2d2d2;
		expected_REQ_deq_cq_index = 2;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, 5, i, 3} - deq 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0110;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h69696;
		tb_REQ_enq_PO_word = 10'h696;
		tb_REQ_enq_byte_mask = 4'b0110;
		tb_REQ_enq_write_data = 32'h96969696;
		tb_REQ_enq_cq_index = 6;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b1;
		expected_REQ_deq_is_amo = 1'b1;
		expected_REQ_deq_is_fence = 1'b1;
		expected_REQ_deq_op = 4'b0011;
		expected_REQ_deq_is_mq = 1'b1;
		expected_REQ_deq_misaligned = 1'b1;
		expected_REQ_deq_misaligned_exception = 1'b1;
		expected_REQ_deq_VPN = 20'h3c3c3;
		expected_REQ_deq_PO_word = 10'h3c3;
		expected_REQ_deq_byte_mask = 4'b0011;
		expected_REQ_deq_write_data = 32'hc3c3c3c3;
		expected_REQ_deq_cq_index = 3;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, 5, i, i} - deq 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0110;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h69696;
		tb_REQ_enq_PO_word = 10'h696;
		tb_REQ_enq_byte_mask = 4'b0110;
		tb_REQ_enq_write_data = 32'h96969696;
		tb_REQ_enq_cq_index = 6;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0100;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h4b4b4;
		expected_REQ_deq_PO_word = 10'h4b4;
		expected_REQ_deq_byte_mask = 4'b0100;
		expected_REQ_deq_write_data = 32'hb4b4b4b4;
		expected_REQ_deq_cq_index = 4;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, 5, i, i} - deq 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0110;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h69696;
		tb_REQ_enq_PO_word = 10'h696;
		tb_REQ_enq_byte_mask = 4'b0110;
		tb_REQ_enq_write_data = 32'h96969696;
		tb_REQ_enq_cq_index = 6;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b1;
		expected_REQ_deq_is_amo = 1'b1;
		expected_REQ_deq_is_fence = 1'b1;
		expected_REQ_deq_op = 4'b0101;
		expected_REQ_deq_is_mq = 1'b1;
		expected_REQ_deq_misaligned = 1'b1;
		expected_REQ_deq_misaligned_exception = 1'b1;
		expected_REQ_deq_VPN = 20'h5a5a5;
		expected_REQ_deq_PO_word = 10'h5a5;
		expected_REQ_deq_byte_mask = 4'b0101;
		expected_REQ_deq_write_data = 32'ha5a5a5a5;
		expected_REQ_deq_cq_index = 5;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - failed deq 6/2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0110;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h69696;
		tb_REQ_enq_PO_word = 10'h696;
		tb_REQ_enq_byte_mask = 4'b0110;
		tb_REQ_enq_write_data = 32'h96969696;
		tb_REQ_enq_cq_index = 6;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b0;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0010;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h2d2d2;
		expected_REQ_deq_PO_word = 10'h2d2;
		expected_REQ_deq_byte_mask = 4'b0010;
		expected_REQ_deq_write_data = 32'hd2d2d2d2;
		expected_REQ_deq_cq_index = 2;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - enq 6, failed deq 6/2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b1;
		tb_REQ_enq_is_store = 1'b0;
		tb_REQ_enq_is_amo = 1'b0;
		tb_REQ_enq_is_fence = 1'b0;
		tb_REQ_enq_op = 4'b0110;
		tb_REQ_enq_is_mq = 1'b0;
		tb_REQ_enq_misaligned = 1'b0;
		tb_REQ_enq_misaligned_exception = 1'b0;
		tb_REQ_enq_VPN = 20'h69696;
		tb_REQ_enq_PO_word = 10'h696;
		tb_REQ_enq_byte_mask = 4'b0110;
		tb_REQ_enq_write_data = 32'h96969696;
		tb_REQ_enq_cq_index = 6;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b0;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0010;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h2d2d2;
		expected_REQ_deq_PO_word = 10'h2d2;
		expected_REQ_deq_byte_mask = 4'b0010;
		expected_REQ_deq_write_data = 32'hd2d2d2d2;
		expected_REQ_deq_cq_index = 2;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, 6, i} - deq 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b1;
		tb_REQ_enq_is_amo = 1'b1;
		tb_REQ_enq_is_fence = 1'b1;
		tb_REQ_enq_op = 4'b0111;
		tb_REQ_enq_is_mq = 1'b1;
		tb_REQ_enq_misaligned = 1'b1;
		tb_REQ_enq_misaligned_exception = 1'b1;
		tb_REQ_enq_VPN = 20'h78787;
		tb_REQ_enq_PO_word = 10'h787;
		tb_REQ_enq_byte_mask = 4'b0111;
		tb_REQ_enq_write_data = 32'h87878787;
		tb_REQ_enq_cq_index = 7;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b1;
		expected_REQ_deq_is_store = 1'b0;
		expected_REQ_deq_is_amo = 1'b0;
		expected_REQ_deq_is_fence = 1'b0;
		expected_REQ_deq_op = 4'b0110;
		expected_REQ_deq_is_mq = 1'b0;
		expected_REQ_deq_misaligned = 1'b0;
		expected_REQ_deq_misaligned_exception = 1'b0;
		expected_REQ_deq_VPN = 20'h69696;
		expected_REQ_deq_PO_word = 10'h696;
		expected_REQ_deq_byte_mask = 4'b0110;
		expected_REQ_deq_write_data = 32'h96969696;
		expected_REQ_deq_cq_index = 6;
	    // REQ stage deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - failed deq 7/3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage enq info
		tb_REQ_enq_valid = 1'b0;
		tb_REQ_enq_is_store = 1'b1;
		tb_REQ_enq_is_amo = 1'b1;
		tb_REQ_enq_is_fence = 1'b1;
		tb_REQ_enq_op = 4'b0111;
		tb_REQ_enq_is_mq = 1'b1;
		tb_REQ_enq_misaligned = 1'b1;
		tb_REQ_enq_misaligned_exception = 1'b1;
		tb_REQ_enq_VPN = 20'h78787;
		tb_REQ_enq_PO_word = 10'h787;
		tb_REQ_enq_byte_mask = 4'b0111;
		tb_REQ_enq_write_data = 32'h87878787;
		tb_REQ_enq_cq_index = 7;
	    // REQ stage enq feedback
	    // REQ stage deq info
	    // REQ stage deq feedback
		tb_REQ_deq_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // REQ stage enq info
	    // REQ stage enq feedback
		expected_REQ_enq_ack = 1'b1;
	    // REQ stage deq info
		expected_REQ_deq_valid = 1'b0;
		expected_REQ_deq_is_store = 1'b1;
		expected_REQ_deq_is_amo = 1'b1;
		expected_REQ_deq_is_fence = 1'b1;
		expected_REQ_deq_op = 4'b0011;
		expected_REQ_deq_is_mq = 1'b1;
		expected_REQ_deq_misaligned = 1'b1;
		expected_REQ_deq_misaligned_exception = 1'b1;
		expected_REQ_deq_VPN = 20'h3c3c3;
		expected_REQ_deq_PO_word = 10'h3c3;
		expected_REQ_deq_byte_mask = 4'b0011;
		expected_REQ_deq_write_data = 32'hc3c3c3c3;
		expected_REQ_deq_cq_index = 3;
	    // REQ stage deq feedback

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