/*
    Filename: alu_imm_dq_tb.sv
    Author: zlagpacan
    Description: Testbench for alu_imm_dq module. 
    Spec: LOROF/spec/design/alu_imm_dq.md
*/

`timescale 1ns/100ps

`include "core_types.vh"

module alu_imm_dq_tb #(
	parameter int unsigned ALU_IMM_DQ_ENTRIES = 4
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
	core_types::PR_t [3:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0] tb_dispatch_A_is_zero_by_way;
	core_types::PR_t [3:0] tb_dispatch_dest_PR_by_way;
	core_types::ROB_index_t [3:0] tb_dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // writeback bus by bank
	logic [core_types::PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	core_types::upper_PR_t [core_types::PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // op enqueue to issue queue
	logic DUT_iq_enq_valid, expected_iq_enq_valid;
	logic [3:0] DUT_iq_enq_op, expected_iq_enq_op;
	logic [11:0] DUT_iq_enq_imm12, expected_iq_enq_imm12;
	core_types::PR_t DUT_iq_enq_A_PR, expected_iq_enq_A_PR;
	logic DUT_iq_enq_A_ready, expected_iq_enq_A_ready;
	logic DUT_iq_enq_A_is_zero, expected_iq_enq_A_is_zero;
	core_types::PR_t DUT_iq_enq_dest_PR, expected_iq_enq_dest_PR;
	core_types::ROB_index_t DUT_iq_enq_ROB_index, expected_iq_enq_ROB_index;

    // issue queue enqueue feedback
	logic tb_iq_enq_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu_imm_dq #(
		.ALU_IMM_DQ_ENTRIES(ALU_IMM_DQ_ENTRIES)
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
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // op dispatch feedback
		.dispatch_ack_by_way(DUT_dispatch_ack_by_way),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // op enqueue to issue queue
		.iq_enq_valid(DUT_iq_enq_valid),
		.iq_enq_op(DUT_iq_enq_op),
		.iq_enq_imm12(DUT_iq_enq_imm12),
		.iq_enq_A_PR(DUT_iq_enq_A_PR),
		.iq_enq_A_ready(DUT_iq_enq_A_ready),
		.iq_enq_A_is_zero(DUT_iq_enq_A_is_zero),
		.iq_enq_dest_PR(DUT_iq_enq_dest_PR),
		.iq_enq_ROB_index(DUT_iq_enq_ROB_index),

	    // issue queue enqueue feedback
		.iq_enq_ready(tb_iq_enq_ready)
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

		if (expected_iq_enq_valid !== DUT_iq_enq_valid) begin
			$display("TB ERROR: expected_iq_enq_valid (%h) != DUT_iq_enq_valid (%h)",
				expected_iq_enq_valid, DUT_iq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_op !== DUT_iq_enq_op) begin
			$display("TB ERROR: expected_iq_enq_op (%h) != DUT_iq_enq_op (%h)",
				expected_iq_enq_op, DUT_iq_enq_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_imm12 !== DUT_iq_enq_imm12) begin
			$display("TB ERROR: expected_iq_enq_imm12 (%h) != DUT_iq_enq_imm12 (%h)",
				expected_iq_enq_imm12, DUT_iq_enq_imm12);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_A_PR !== DUT_iq_enq_A_PR) begin
			$display("TB ERROR: expected_iq_enq_A_PR (%h) != DUT_iq_enq_A_PR (%h)",
				expected_iq_enq_A_PR, DUT_iq_enq_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_A_ready !== DUT_iq_enq_A_ready) begin
			$display("TB ERROR: expected_iq_enq_A_ready (%h) != DUT_iq_enq_A_ready (%h)",
				expected_iq_enq_A_ready, DUT_iq_enq_A_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_A_is_zero !== DUT_iq_enq_A_is_zero) begin
			$display("TB ERROR: expected_iq_enq_A_is_zero (%h) != DUT_iq_enq_A_is_zero (%h)",
				expected_iq_enq_A_is_zero, DUT_iq_enq_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_dest_PR !== DUT_iq_enq_dest_PR) begin
			$display("TB ERROR: expected_iq_enq_dest_PR (%h) != DUT_iq_enq_dest_PR (%h)",
				expected_iq_enq_dest_PR, DUT_iq_enq_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_ROB_index !== DUT_iq_enq_ROB_index) begin
			$display("TB ERROR: expected_iq_enq_ROB_index (%h) != DUT_iq_enq_ROB_index (%h)",
				expected_iq_enq_ROB_index, DUT_iq_enq_ROB_index);
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
		tb_dispatch_valid_by_way = '0;
		tb_dispatch_op_by_way = '0;
		tb_dispatch_imm12_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_is_zero_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_iq_enq_ready = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = '0;
	    // writeback bus by bank
	    // op enqueue to issue queue
		expected_iq_enq_valid = '0;
		expected_iq_enq_op = '0;
		expected_iq_enq_imm12 = '0;
		expected_iq_enq_A_PR = '0;
		expected_iq_enq_A_ready = '0;
		expected_iq_enq_A_is_zero = '0;
		expected_iq_enq_dest_PR = '0;
		expected_iq_enq_ROB_index = '0;
	    // issue queue enqueue feedback

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = '0;
		tb_dispatch_valid_by_way = '0;
		tb_dispatch_op_by_way = '0;
		tb_dispatch_imm12_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_is_zero_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_iq_enq_ready = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = '0;
	    // writeback bus by bank
	    // op enqueue to issue queue
		expected_iq_enq_valid = '0;
		expected_iq_enq_op = '0;
		expected_iq_enq_imm12 = '0;
		expected_iq_enq_A_PR = '0;
		expected_iq_enq_A_ready = '0;
		expected_iq_enq_A_is_zero = '0;
		expected_iq_enq_dest_PR = '0;
		expected_iq_enq_ROB_index = '0;
	    // issue queue enqueue feedback

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
		tb_dispatch_valid_by_way = '0;
		tb_dispatch_op_by_way = '0;
		tb_dispatch_imm12_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_is_zero_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_iq_enq_ready = '0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = '0;
	    // writeback bus by bank
	    // op enqueue to issue queue
		expected_iq_enq_valid = '0;
		expected_iq_enq_op = '0;
		expected_iq_enq_imm12 = '0;
		expected_iq_enq_A_PR = '0;
		expected_iq_enq_A_ready = '0;
		expected_iq_enq_A_is_zero = '0;
		expected_iq_enq_dest_PR = '0;
		expected_iq_enq_ROB_index = '0;
	    // issue queue enqueue feedback

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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule