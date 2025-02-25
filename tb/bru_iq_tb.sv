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
	logic [3:0] tb_dispatch_A_unneeded_or_is_zero_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_way;
	logic [3:0] tb_dispatch_B_unneeded_or_is_zero_by_way;
	logic [3:0] tb_dispatch_B_ready_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // BRU pipeline feedback
	logic tb_pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // BRU op issue to BRU pipeline
	logic DUT_issue_valid, expected_issue_valid;
	logic [3:0] DUT_issue_op, expected_issue_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_issue_pred_info, expected_issue_pred_info;
	logic DUT_issue_pred_lru, expected_issue_pred_lru;
	logic DUT_issue_is_link_ra, expected_issue_is_link_ra;
	logic DUT_issue_is_ret_ra, expected_issue_is_ret_ra;
	logic [31:0] DUT_issue_PC, expected_issue_PC;
	logic [31:0] DUT_issue_pred_PC, expected_issue_pred_PC;
	logic [19:0] DUT_issue_imm20, expected_issue_imm20;
	logic DUT_issue_A_unneeded_or_is_zero, expected_issue_A_unneeded_or_is_zero;
	logic DUT_issue_A_forward, expected_issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] DUT_issue_A_bank, expected_issue_A_bank;
	logic DUT_issue_B_unneeded_or_is_zero, expected_issue_B_unneeded_or_is_zero;
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

	bru_iq #(
		.BRU_IQ_ENTRIES(4)	
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
		.dispatch_A_unneeded_or_is_zero_by_way(tb_dispatch_A_unneeded_or_is_zero_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_B_PR_by_way(tb_dispatch_B_PR_by_way),
		.dispatch_B_unneeded_or_is_zero_by_way(tb_dispatch_B_unneeded_or_is_zero_by_way),
		.dispatch_B_ready_by_way(tb_dispatch_B_ready_by_way),
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // op dispatch feedback
		.dispatch_ack_by_way(DUT_dispatch_ack_by_way),

	    // BRU pipeline feedback
		.pipeline_ready(tb_pipeline_ready),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // BRU op issue to BRU pipeline
		.issue_valid(DUT_issue_valid),
		.issue_op(DUT_issue_op),
		.issue_pred_info(DUT_issue_pred_info),
		.issue_pred_lru(DUT_issue_pred_lru),
		.issue_is_link_ra(DUT_issue_is_link_ra),
		.issue_is_ret_ra(DUT_issue_is_ret_ra),
		.issue_PC(DUT_issue_PC),
		.issue_pred_PC(DUT_issue_pred_PC),
		.issue_imm20(DUT_issue_imm20),
		.issue_A_unneeded_or_is_zero(DUT_issue_A_unneeded_or_is_zero),
		.issue_A_forward(DUT_issue_A_forward),
		.issue_A_bank(DUT_issue_A_bank),
		.issue_B_unneeded_or_is_zero(DUT_issue_B_unneeded_or_is_zero),
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
		if (expected_dispatch_ack_by_way !== DUT_dispatch_ack_by_way) begin
			$display("TB ERROR: expected_dispatch_ack_by_way (%h) != DUT_dispatch_ack_by_way (%h)",
				expected_dispatch_ack_by_way, DUT_dispatch_ack_by_way);
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

		if (expected_issue_pred_info !== DUT_issue_pred_info) begin
			$display("TB ERROR: expected_issue_pred_info (%h) != DUT_issue_pred_info (%h)",
				expected_issue_pred_info, DUT_issue_pred_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_pred_lru !== DUT_issue_pred_lru) begin
			$display("TB ERROR: expected_issue_pred_lru (%h) != DUT_issue_pred_lru (%h)",
				expected_issue_pred_lru, DUT_issue_pred_lru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_is_link_ra !== DUT_issue_is_link_ra) begin
			$display("TB ERROR: expected_issue_is_link_ra (%h) != DUT_issue_is_link_ra (%h)",
				expected_issue_is_link_ra, DUT_issue_is_link_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_is_ret_ra !== DUT_issue_is_ret_ra) begin
			$display("TB ERROR: expected_issue_is_ret_ra (%h) != DUT_issue_is_ret_ra (%h)",
				expected_issue_is_ret_ra, DUT_issue_is_ret_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_PC !== DUT_issue_PC) begin
			$display("TB ERROR: expected_issue_PC (%h) != DUT_issue_PC (%h)",
				expected_issue_PC, DUT_issue_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_pred_PC !== DUT_issue_pred_PC) begin
			$display("TB ERROR: expected_issue_pred_PC (%h) != DUT_issue_pred_PC (%h)",
				expected_issue_pred_PC, DUT_issue_pred_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_imm20 !== DUT_issue_imm20) begin
			$display("TB ERROR: expected_issue_imm20 (%h) != DUT_issue_imm20 (%h)",
				expected_issue_imm20, DUT_issue_imm20);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_issue_A_unneeded_or_is_zero !== DUT_issue_A_unneeded_or_is_zero) begin
			$display("TB ERROR: expected_issue_A_unneeded_or_is_zero (%h) != DUT_issue_A_unneeded_or_is_zero (%h)",
				expected_issue_A_unneeded_or_is_zero, DUT_issue_A_unneeded_or_is_zero);
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

		if (expected_issue_B_unneeded_or_is_zero !== DUT_issue_B_unneeded_or_is_zero) begin
			$display("TB ERROR: expected_issue_B_unneeded_or_is_zero (%h) != DUT_issue_B_unneeded_or_is_zero (%h)",
				expected_issue_B_unneeded_or_is_zero, DUT_issue_B_unneeded_or_is_zero);
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
		tb_dispatch_A_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_B_PR_by_way = '0;
		tb_dispatch_B_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_B_ready_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = '0;
		expected_issue_op = '0;
		expected_issue_pred_info = '0;
		expected_issue_pred_lru = '0;
		expected_issue_is_link_ra = '0;
		expected_issue_is_ret_ra = '0;
		expected_issue_PC = '0;
		expected_issue_pred_PC = '0;
		expected_issue_imm20 = '0;
		expected_issue_A_unneeded_or_is_zero = '0;
		expected_issue_A_forward = '0;
		expected_issue_A_bank = '0;
		expected_issue_B_unneeded_or_is_zero = '0;
		expected_issue_B_forward = '0;
		expected_issue_B_bank = '0;
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = '0;
		expected_PRF_req_A_PR = '0;
		expected_PRF_req_B_valid = '0;
		expected_PRF_req_B_PR = '0;

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
		tb_dispatch_A_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_B_PR_by_way = '0;
		tb_dispatch_B_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_B_ready_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = '0;
		expected_issue_op = '0;
		expected_issue_pred_info = '0;
		expected_issue_pred_lru = '0;
		expected_issue_is_link_ra = '0;
		expected_issue_is_ret_ra = '0;
		expected_issue_PC = '0;
		expected_issue_pred_PC = '0;
		expected_issue_imm20 = '0;
		expected_issue_A_unneeded_or_is_zero = '0;
		expected_issue_A_forward = '0;
		expected_issue_A_bank = '0;
		expected_issue_B_unneeded_or_is_zero = '0;
		expected_issue_B_forward = '0;
		expected_issue_B_bank = '0;
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = '0;
		expected_PRF_req_A_PR = '0;
		expected_PRF_req_B_valid = '0;
		expected_PRF_req_B_PR = '0;

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
		tb_dispatch_A_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_A_ready_by_way = '0;
		tb_dispatch_B_PR_by_way = '0;
		tb_dispatch_B_unneeded_or_is_zero_by_way = '0;
		tb_dispatch_B_ready_by_way = '0;
		tb_dispatch_dest_PR_by_way = '0;
		tb_dispatch_ROB_index_by_way = '0;
	    // op dispatch feedback
	    // BRU pipeline feedback
		tb_pipeline_ready = 1'b1;
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = '0;
		tb_WB_bus_upper_PR_by_bank = '0;
	    // BRU op issue to BRU pipeline
	    // reg read req to PRF

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // BRU pipeline feedback
	    // writeback bus by bank
	    // BRU op issue to BRU pipeline
		expected_issue_valid = '0;
		expected_issue_op = '0;
		expected_issue_pred_info = '0;
		expected_issue_pred_lru = '0;
		expected_issue_is_link_ra = '0;
		expected_issue_is_ret_ra = '0;
		expected_issue_PC = '0;
		expected_issue_pred_PC = '0;
		expected_issue_imm20 = '0;
		expected_issue_A_unneeded_or_is_zero = '0;
		expected_issue_A_forward = '0;
		expected_issue_A_bank = '0;
		expected_issue_B_unneeded_or_is_zero = '0;
		expected_issue_B_forward = '0;
		expected_issue_B_bank = '0;
		expected_issue_dest_PR = '0;
		expected_issue_ROB_index = '0;
	    // reg read req to PRF
		expected_PRF_req_A_valid = '0;
		expected_PRF_req_A_PR = '0;
		expected_PRF_req_B_valid = '0;
		expected_PRF_req_B_PR = '0;

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