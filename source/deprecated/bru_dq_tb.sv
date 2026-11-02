/*
    Filename: bru_dq_tb.sv
    Author: zlagpacan
    Description: Testbench for bru_dq module. 
    Spec: LOROF/spec/design/bru_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module bru_dq_tb #(
	parameter BRU_DQ_ENTRIES = 4
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
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0] tb_dispatch_pred_info_by_way;
	logic [3:0] tb_dispatch_pred_lru_by_way;
	logic [3:0] tb_dispatch_is_link_ra_by_way;
	logic [3:0] tb_dispatch_is_ret_ra_by_way;
	logic [3:0][31:0] tb_dispatch_PC_by_way;
	logic [3:0][31:0] tb_dispatch_pred_PC_by_way;
	logic [3:0][19:0] tb_dispatch_imm20_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0] tb_dispatch_A_unneeded_or_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_way;
	logic [3:0] tb_dispatch_B_ready_by_way;
	logic [3:0] tb_dispatch_B_unneeded_or_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // op enqueue to issue queue
	logic DUT_iq_enq_valid, expected_iq_enq_valid;
	logic [3:0] DUT_iq_enq_op, expected_iq_enq_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_iq_enq_pred_info, expected_iq_enq_pred_info;
	logic DUT_iq_enq_pred_lru, expected_iq_enq_pred_lru;
	logic DUT_iq_enq_is_link_ra, expected_iq_enq_is_link_ra;
	logic DUT_iq_enq_is_ret_ra, expected_iq_enq_is_ret_ra;
	logic [31:0] DUT_iq_enq_PC, expected_iq_enq_PC;
	logic [31:0] DUT_iq_enq_pred_PC, expected_iq_enq_pred_PC;
	logic [19:0] DUT_iq_enq_imm20, expected_iq_enq_imm20;
	logic [LOG_PR_COUNT-1:0] DUT_iq_enq_A_PR, expected_iq_enq_A_PR;
	logic DUT_iq_enq_A_ready, expected_iq_enq_A_ready;
	logic DUT_iq_enq_A_unneeded_or_is_zero, expected_iq_enq_A_unneeded_or_is_zero;
	logic [LOG_PR_COUNT-1:0] DUT_iq_enq_B_PR, expected_iq_enq_B_PR;
	logic DUT_iq_enq_B_ready, expected_iq_enq_B_ready;
	logic DUT_iq_enq_B_unneeded_or_is_zero, expected_iq_enq_B_unneeded_or_is_zero;
	logic [LOG_PR_COUNT-1:0] DUT_iq_enq_dest_PR, expected_iq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_iq_enq_ROB_index, expected_iq_enq_ROB_index;

    // issue queue enqueue feedback
	logic tb_iq_enq_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bru_dq #(
		.BRU_DQ_ENTRIES(BRU_DQ_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // op dispatch by way
		.dispatch_attempt_by_way(tb_dispatch_attempt_by_way),
		.dispatch_valid_by_way(tb_dispatch_valid_by_way),
		.dispatch_op_by_way(tb_dispatch_op_by_way),
		.dispatch_pred_info_by_way(tb_dispatch_pred_info_by_way),
		.dispatch_pred_lru_by_way(tb_dispatch_pred_lru_by_way),
		.dispatch_is_link_ra_by_way(tb_dispatch_is_link_ra_by_way),
		.dispatch_is_ret_ra_by_way(tb_dispatch_is_ret_ra_by_way),
		.dispatch_PC_by_way(tb_dispatch_PC_by_way),
		.dispatch_pred_PC_by_way(tb_dispatch_pred_PC_by_way),
		.dispatch_imm20_by_way(tb_dispatch_imm20_by_way),
		.dispatch_A_PR_by_way(tb_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_A_unneeded_or_is_zero_by_way(tb_dispatch_A_unneeded_or_is_zero_by_way),
		.dispatch_B_PR_by_way(tb_dispatch_B_PR_by_way),
		.dispatch_B_ready_by_way(tb_dispatch_B_ready_by_way),
		.dispatch_B_unneeded_or_is_zero_by_way(tb_dispatch_B_unneeded_or_is_zero_by_way),
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
		.iq_enq_pred_info(DUT_iq_enq_pred_info),
		.iq_enq_pred_lru(DUT_iq_enq_pred_lru),
		.iq_enq_is_link_ra(DUT_iq_enq_is_link_ra),
		.iq_enq_is_ret_ra(DUT_iq_enq_is_ret_ra),
		.iq_enq_PC(DUT_iq_enq_PC),
		.iq_enq_pred_PC(DUT_iq_enq_pred_PC),
		.iq_enq_imm20(DUT_iq_enq_imm20),
		.iq_enq_A_PR(DUT_iq_enq_A_PR),
		.iq_enq_A_ready(DUT_iq_enq_A_ready),
		.iq_enq_A_unneeded_or_is_zero(DUT_iq_enq_A_unneeded_or_is_zero),
		.iq_enq_B_PR(DUT_iq_enq_B_PR),
		.iq_enq_B_ready(DUT_iq_enq_B_ready),
		.iq_enq_B_unneeded_or_is_zero(DUT_iq_enq_B_unneeded_or_is_zero),
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

		if (expected_iq_enq_pred_info !== DUT_iq_enq_pred_info) begin
			$display("TB ERROR: expected_iq_enq_pred_info (%h) != DUT_iq_enq_pred_info (%h)",
				expected_iq_enq_pred_info, DUT_iq_enq_pred_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_pred_lru !== DUT_iq_enq_pred_lru) begin
			$display("TB ERROR: expected_iq_enq_pred_lru (%h) != DUT_iq_enq_pred_lru (%h)",
				expected_iq_enq_pred_lru, DUT_iq_enq_pred_lru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_is_link_ra !== DUT_iq_enq_is_link_ra) begin
			$display("TB ERROR: expected_iq_enq_is_link_ra (%h) != DUT_iq_enq_is_link_ra (%h)",
				expected_iq_enq_is_link_ra, DUT_iq_enq_is_link_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_is_ret_ra !== DUT_iq_enq_is_ret_ra) begin
			$display("TB ERROR: expected_iq_enq_is_ret_ra (%h) != DUT_iq_enq_is_ret_ra (%h)",
				expected_iq_enq_is_ret_ra, DUT_iq_enq_is_ret_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_PC !== DUT_iq_enq_PC) begin
			$display("TB ERROR: expected_iq_enq_PC (%h) != DUT_iq_enq_PC (%h)",
				expected_iq_enq_PC, DUT_iq_enq_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_pred_PC !== DUT_iq_enq_pred_PC) begin
			$display("TB ERROR: expected_iq_enq_pred_PC (%h) != DUT_iq_enq_pred_PC (%h)",
				expected_iq_enq_pred_PC, DUT_iq_enq_pred_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_imm20 !== DUT_iq_enq_imm20) begin
			$display("TB ERROR: expected_iq_enq_imm20 (%h) != DUT_iq_enq_imm20 (%h)",
				expected_iq_enq_imm20, DUT_iq_enq_imm20);
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

		if (expected_iq_enq_A_unneeded_or_is_zero !== DUT_iq_enq_A_unneeded_or_is_zero) begin
			$display("TB ERROR: expected_iq_enq_A_unneeded_or_is_zero (%h) != DUT_iq_enq_A_unneeded_or_is_zero (%h)",
				expected_iq_enq_A_unneeded_or_is_zero, DUT_iq_enq_A_unneeded_or_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_B_PR !== DUT_iq_enq_B_PR) begin
			$display("TB ERROR: expected_iq_enq_B_PR (%h) != DUT_iq_enq_B_PR (%h)",
				expected_iq_enq_B_PR, DUT_iq_enq_B_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_B_ready !== DUT_iq_enq_B_ready) begin
			$display("TB ERROR: expected_iq_enq_B_ready (%h) != DUT_iq_enq_B_ready (%h)",
				expected_iq_enq_B_ready, DUT_iq_enq_B_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_iq_enq_B_unneeded_or_is_zero !== DUT_iq_enq_B_unneeded_or_is_zero) begin
			$display("TB ERROR: expected_iq_enq_B_unneeded_or_is_zero (%h) != DUT_iq_enq_B_unneeded_or_is_zero (%h)",
				expected_iq_enq_B_unneeded_or_is_zero, DUT_iq_enq_B_unneeded_or_is_zero);
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
		tb_dispatch_pred_info_by_way = '0;
		tb_dispatch_pred_lru_by_way = '0;
		tb_dispatch_is_link_ra_by_way = '0;
		tb_dispatch_is_ret_ra_by_way = '0;
		tb_dispatch_PC_by_way = '0;
		tb_dispatch_pred_PC_by_way = '0;
		tb_dispatch_imm20_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_B_PR_by_way = '0;
		tb_dispatch_B_ready_by_way = '0;
		tb_dispatch_B_unneeded_or_is_zero_by_way = '0;
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
		expected_iq_enq_pred_info = '0;
		expected_iq_enq_pred_lru = '0;
		expected_iq_enq_is_link_ra = '0;
		expected_iq_enq_is_ret_ra = '0;
		expected_iq_enq_PC = '0;
		expected_iq_enq_pred_PC = '0;
		expected_iq_enq_imm20 = '0;
		expected_iq_enq_A_PR = '0;
		expected_iq_enq_A_ready = '0;
		expected_iq_enq_A_unneeded_or_is_zero = '0;
		expected_iq_enq_B_PR = '0;
		expected_iq_enq_B_ready = '0;
		expected_iq_enq_B_unneeded_or_is_zero = '0;
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
		tb_dispatch_pred_info_by_way = '0;
		tb_dispatch_pred_lru_by_way = '0;
		tb_dispatch_is_link_ra_by_way = '0;
		tb_dispatch_is_ret_ra_by_way = '0;
		tb_dispatch_PC_by_way = '0;
		tb_dispatch_pred_PC_by_way = '0;
		tb_dispatch_imm20_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_B_PR_by_way = '0;
		tb_dispatch_B_ready_by_way = '0;
		tb_dispatch_B_unneeded_or_is_zero_by_way = '0;
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
		expected_iq_enq_pred_info = '0;
		expected_iq_enq_pred_lru = '0;
		expected_iq_enq_is_link_ra = '0;
		expected_iq_enq_is_ret_ra = '0;
		expected_iq_enq_PC = '0;
		expected_iq_enq_pred_PC = '0;
		expected_iq_enq_imm20 = '0;
		expected_iq_enq_A_PR = '0;
		expected_iq_enq_A_ready = '0;
		expected_iq_enq_A_unneeded_or_is_zero = '0;
		expected_iq_enq_B_PR = '0;
		expected_iq_enq_B_ready = '0;
		expected_iq_enq_B_unneeded_or_is_zero = '0;
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
		tb_dispatch_pred_info_by_way = '0;
		tb_dispatch_pred_lru_by_way = '0;
		tb_dispatch_is_link_ra_by_way = '0;
		tb_dispatch_is_ret_ra_by_way = '0;
		tb_dispatch_PC_by_way = '0;
		tb_dispatch_pred_PC_by_way = '0;
		tb_dispatch_imm20_by_way = '0;
		tb_dispatch_A_PR_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_A_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_B_PR_by_way = '0;
		tb_dispatch_B_ready_by_way = '0;
		tb_dispatch_B_unneeded_or_is_zero_by_way = '0;
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
		expected_iq_enq_pred_info = '0;
		expected_iq_enq_pred_lru = '0;
		expected_iq_enq_is_link_ra = '0;
		expected_iq_enq_is_ret_ra = '0;
		expected_iq_enq_PC = '0;
		expected_iq_enq_pred_PC = '0;
		expected_iq_enq_imm20 = '0;
		expected_iq_enq_A_PR = '0;
		expected_iq_enq_A_ready = '0;
		expected_iq_enq_A_unneeded_or_is_zero = '0;
		expected_iq_enq_B_PR = '0;
		expected_iq_enq_B_ready = '0;
		expected_iq_enq_B_unneeded_or_is_zero = '0;
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