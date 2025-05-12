/*
    Filename: stamofu_dq_tb.sv
    Author: zlagpacan
    Description: Testbench for stamofu_dq module. 
    Spec: LOROF/spec/design/stamofu_dq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stamofu_dq_tb ();

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
	logic [3:0] tb_dispatch_valid_store_by_way;
	logic [3:0] tb_dispatch_valid_amo_by_way;
	logic [3:0] tb_dispatch_valid_fence_by_way;
	logic [3:0][3:0] tb_dispatch_op_by_way;
	logic [3:0][11:0] tb_dispatch_imm12_by_way;
	logic [3:0][MDPT_INFO_WIDTH-1:0] tb_dispatch_mdp_info_by_way;
	logic [3:0] tb_dispatch_mem_aq_by_way;
	logic [3:0] tb_dispatch_io_aq_by_way;
	logic [3:0] tb_dispatch_mem_rl_by_way;
	logic [3:0] tb_dispatch_io_rl_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_A_PR_by_way;
	logic [3:0] tb_dispatch_A_ready_by_way;
	logic [3:0] tb_dispatch_A_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_B_PR_by_way;
	logic [3:0] tb_dispatch_B_ready_by_way;
	logic [3:0] tb_dispatch_B_is_zero_by_way;
	logic [3:0][LOG_PR_COUNT-1:0] tb_dispatch_dest_PR_by_way;
	logic [3:0][LOG_ROB_ENTRIES-1:0] tb_dispatch_ROB_index_by_way;

    // op dispatch feedback
	logic [3:0] DUT_dispatch_ack_by_way, expected_dispatch_ack_by_way;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] tb_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] tb_WB_bus_upper_PR_by_bank;

    // op enqueue to central queue
	logic DUT_stamofu_cq_enq_valid, expected_stamofu_cq_enq_valid;
	logic DUT_stamofu_cq_enq_killed, expected_stamofu_cq_enq_killed;
	logic DUT_stamofu_cq_enq_is_store, expected_stamofu_cq_enq_is_store;
	logic DUT_stamofu_cq_enq_is_amo, expected_stamofu_cq_enq_is_amo;
	logic DUT_stamofu_cq_enq_is_fence, expected_stamofu_cq_enq_is_fence;
	logic [3:0] DUT_stamofu_cq_enq_op, expected_stamofu_cq_enq_op;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_cq_enq_mdp_info, expected_stamofu_cq_enq_mdp_info;
	logic DUT_stamofu_cq_enq_mem_aq, expected_stamofu_cq_enq_mem_aq;
	logic DUT_stamofu_cq_enq_io_aq, expected_stamofu_cq_enq_io_aq;
	logic DUT_stamofu_cq_enq_mem_rl, expected_stamofu_cq_enq_mem_rl;
	logic DUT_stamofu_cq_enq_io_rl, expected_stamofu_cq_enq_io_rl;
	logic [LOG_PR_COUNT-1:0] DUT_stamofu_cq_enq_dest_PR, expected_stamofu_cq_enq_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_cq_enq_ROB_index, expected_stamofu_cq_enq_ROB_index;

    // central queue enqueue feedback
	logic tb_stamofu_cq_enq_ready;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] tb_stamofu_cq_enq_index;

    // op enqueue to issue queue
	logic DUT_stamofu_iq_enq_valid, expected_stamofu_iq_enq_valid;
	logic DUT_stamofu_iq_enq_is_store, expected_stamofu_iq_enq_is_store;
	logic DUT_stamofu_iq_enq_is_amo, expected_stamofu_iq_enq_is_amo;
	logic DUT_stamofu_iq_enq_is_fence, expected_stamofu_iq_enq_is_fence;
	logic [3:0] DUT_stamofu_iq_enq_op, expected_stamofu_iq_enq_op;
	logic [11:0] DUT_stamofu_iq_enq_imm12, expected_stamofu_iq_enq_imm12;
	logic [MDPT_INFO_WIDTH-1:0] DUT_stamofu_iq_enq_mdp_info, expected_stamofu_iq_enq_mdp_info;
	logic DUT_stamofu_iq_enq_mem_aq, expected_stamofu_iq_enq_mem_aq;
	logic DUT_stamofu_iq_enq_io_aq, expected_stamofu_iq_enq_io_aq;
	logic [LOG_PR_COUNT-1:0] DUT_stamofu_iq_enq_A_PR, expected_stamofu_iq_enq_A_PR;
	logic DUT_stamofu_iq_enq_A_ready, expected_stamofu_iq_enq_A_ready;
	logic DUT_stamofu_iq_enq_A_is_zero, expected_stamofu_iq_enq_A_is_zero;
	logic [LOG_PR_COUNT-1:0] DUT_stamofu_iq_enq_B_PR, expected_stamofu_iq_enq_B_PR;
	logic DUT_stamofu_iq_enq_B_ready, expected_stamofu_iq_enq_B_ready;
	logic DUT_stamofu_iq_enq_B_is_zero, expected_stamofu_iq_enq_B_is_zero;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_iq_enq_ROB_index, expected_stamofu_iq_enq_ROB_index;
	logic [LOG_STAMOFU_CQ_ENTRIES-1:0] DUT_stamofu_iq_enq_cq_index, expected_stamofu_iq_enq_cq_index;

    // issue queue enqueue feedback
	logic tb_stamofu_iq_enq_ready;

    // op enqueue to acquire queue
	logic DUT_stamofu_aq_enq_valid, expected_stamofu_aq_enq_valid;
	logic DUT_stamofu_aq_enq_mem_aq, expected_stamofu_aq_enq_mem_aq;
	logic DUT_stamofu_aq_enq_io_aq, expected_stamofu_aq_enq_io_aq;
	logic [LOG_ROB_ENTRIES-1:0] DUT_stamofu_aq_enq_ROB_index, expected_stamofu_aq_enq_ROB_index;

    // acquire queue enqueue feedback
	logic tb_stamofu_aq_enq_ready;

    // ROB kill
	logic tb_rob_kill_valid;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_abs_head_index;
	logic [LOG_ROB_ENTRIES-1:0] tb_rob_kill_rel_kill_younger_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	stamofu_dq #(
		.STAMOFU_DQ_ENTRIES(4)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // op dispatch by way
		.dispatch_attempt_by_way(tb_dispatch_attempt_by_way),
		.dispatch_valid_store_by_way(tb_dispatch_valid_store_by_way),
		.dispatch_valid_amo_by_way(tb_dispatch_valid_amo_by_way),
		.dispatch_valid_fence_by_way(tb_dispatch_valid_fence_by_way),
		.dispatch_op_by_way(tb_dispatch_op_by_way),
		.dispatch_imm12_by_way(tb_dispatch_imm12_by_way),
		.dispatch_mdp_info_by_way(tb_dispatch_mdp_info_by_way),
		.dispatch_mem_aq_by_way(tb_dispatch_mem_aq_by_way),
		.dispatch_io_aq_by_way(tb_dispatch_io_aq_by_way),
		.dispatch_mem_rl_by_way(tb_dispatch_mem_rl_by_way),
		.dispatch_io_rl_by_way(tb_dispatch_io_rl_by_way),
		.dispatch_A_PR_by_way(tb_dispatch_A_PR_by_way),
		.dispatch_A_ready_by_way(tb_dispatch_A_ready_by_way),
		.dispatch_A_is_zero_by_way(tb_dispatch_A_is_zero_by_way),
		.dispatch_B_PR_by_way(tb_dispatch_B_PR_by_way),
		.dispatch_B_ready_by_way(tb_dispatch_B_ready_by_way),
		.dispatch_B_is_zero_by_way(tb_dispatch_B_is_zero_by_way),
		.dispatch_dest_PR_by_way(tb_dispatch_dest_PR_by_way),
		.dispatch_ROB_index_by_way(tb_dispatch_ROB_index_by_way),

	    // op dispatch feedback
		.dispatch_ack_by_way(DUT_dispatch_ack_by_way),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(tb_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(tb_WB_bus_upper_PR_by_bank),

	    // op enqueue to central queue
		.stamofu_cq_enq_valid(DUT_stamofu_cq_enq_valid),
		.stamofu_cq_enq_killed(DUT_stamofu_cq_enq_killed),
		.stamofu_cq_enq_is_store(DUT_stamofu_cq_enq_is_store),
		.stamofu_cq_enq_is_amo(DUT_stamofu_cq_enq_is_amo),
		.stamofu_cq_enq_is_fence(DUT_stamofu_cq_enq_is_fence),
		.stamofu_cq_enq_op(DUT_stamofu_cq_enq_op),
		.stamofu_cq_enq_mdp_info(DUT_stamofu_cq_enq_mdp_info),
		.stamofu_cq_enq_mem_aq(DUT_stamofu_cq_enq_mem_aq),
		.stamofu_cq_enq_io_aq(DUT_stamofu_cq_enq_io_aq),
		.stamofu_cq_enq_mem_rl(DUT_stamofu_cq_enq_mem_rl),
		.stamofu_cq_enq_io_rl(DUT_stamofu_cq_enq_io_rl),
		.stamofu_cq_enq_dest_PR(DUT_stamofu_cq_enq_dest_PR),
		.stamofu_cq_enq_ROB_index(DUT_stamofu_cq_enq_ROB_index),

	    // central queue enqueue feedback
		.stamofu_cq_enq_ready(tb_stamofu_cq_enq_ready),
		.stamofu_cq_enq_index(tb_stamofu_cq_enq_index),

	    // op enqueue to issue queue
		.stamofu_iq_enq_valid(DUT_stamofu_iq_enq_valid),
		.stamofu_iq_enq_is_store(DUT_stamofu_iq_enq_is_store),
		.stamofu_iq_enq_is_amo(DUT_stamofu_iq_enq_is_amo),
		.stamofu_iq_enq_is_fence(DUT_stamofu_iq_enq_is_fence),
		.stamofu_iq_enq_op(DUT_stamofu_iq_enq_op),
		.stamofu_iq_enq_imm12(DUT_stamofu_iq_enq_imm12),
		.stamofu_iq_enq_mdp_info(DUT_stamofu_iq_enq_mdp_info),
		.stamofu_iq_enq_mem_aq(DUT_stamofu_iq_enq_mem_aq),
		.stamofu_iq_enq_io_aq(DUT_stamofu_iq_enq_io_aq),
		.stamofu_iq_enq_A_PR(DUT_stamofu_iq_enq_A_PR),
		.stamofu_iq_enq_A_ready(DUT_stamofu_iq_enq_A_ready),
		.stamofu_iq_enq_A_is_zero(DUT_stamofu_iq_enq_A_is_zero),
		.stamofu_iq_enq_B_PR(DUT_stamofu_iq_enq_B_PR),
		.stamofu_iq_enq_B_ready(DUT_stamofu_iq_enq_B_ready),
		.stamofu_iq_enq_B_is_zero(DUT_stamofu_iq_enq_B_is_zero),
		.stamofu_iq_enq_ROB_index(DUT_stamofu_iq_enq_ROB_index),
		.stamofu_iq_enq_cq_index(DUT_stamofu_iq_enq_cq_index),

	    // issue queue enqueue feedback
		.stamofu_iq_enq_ready(tb_stamofu_iq_enq_ready),

	    // op enqueue to acquire queue
		.stamofu_aq_enq_valid(DUT_stamofu_aq_enq_valid),
		.stamofu_aq_enq_mem_aq(DUT_stamofu_aq_enq_mem_aq),
		.stamofu_aq_enq_io_aq(DUT_stamofu_aq_enq_io_aq),
		.stamofu_aq_enq_ROB_index(DUT_stamofu_aq_enq_ROB_index),

	    // acquire queue enqueue feedback
		.stamofu_aq_enq_ready(tb_stamofu_aq_enq_ready),

	    // ROB kill
		.rob_kill_valid(tb_rob_kill_valid),
		.rob_kill_abs_head_index(tb_rob_kill_abs_head_index),
		.rob_kill_rel_kill_younger_index(tb_rob_kill_rel_kill_younger_index)
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

		if (expected_stamofu_cq_enq_valid !== DUT_stamofu_cq_enq_valid) begin
			$display("TB ERROR: expected_stamofu_cq_enq_valid (%h) != DUT_stamofu_cq_enq_valid (%h)",
				expected_stamofu_cq_enq_valid, DUT_stamofu_cq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_killed !== DUT_stamofu_cq_enq_killed) begin
			$display("TB ERROR: expected_stamofu_cq_enq_killed (%h) != DUT_stamofu_cq_enq_killed (%h)",
				expected_stamofu_cq_enq_killed, DUT_stamofu_cq_enq_killed);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_is_store !== DUT_stamofu_cq_enq_is_store) begin
			$display("TB ERROR: expected_stamofu_cq_enq_is_store (%h) != DUT_stamofu_cq_enq_is_store (%h)",
				expected_stamofu_cq_enq_is_store, DUT_stamofu_cq_enq_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_is_amo !== DUT_stamofu_cq_enq_is_amo) begin
			$display("TB ERROR: expected_stamofu_cq_enq_is_amo (%h) != DUT_stamofu_cq_enq_is_amo (%h)",
				expected_stamofu_cq_enq_is_amo, DUT_stamofu_cq_enq_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_is_fence !== DUT_stamofu_cq_enq_is_fence) begin
			$display("TB ERROR: expected_stamofu_cq_enq_is_fence (%h) != DUT_stamofu_cq_enq_is_fence (%h)",
				expected_stamofu_cq_enq_is_fence, DUT_stamofu_cq_enq_is_fence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_op !== DUT_stamofu_cq_enq_op) begin
			$display("TB ERROR: expected_stamofu_cq_enq_op (%h) != DUT_stamofu_cq_enq_op (%h)",
				expected_stamofu_cq_enq_op, DUT_stamofu_cq_enq_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_mdp_info !== DUT_stamofu_cq_enq_mdp_info) begin
			$display("TB ERROR: expected_stamofu_cq_enq_mdp_info (%h) != DUT_stamofu_cq_enq_mdp_info (%h)",
				expected_stamofu_cq_enq_mdp_info, DUT_stamofu_cq_enq_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_mem_aq !== DUT_stamofu_cq_enq_mem_aq) begin
			$display("TB ERROR: expected_stamofu_cq_enq_mem_aq (%h) != DUT_stamofu_cq_enq_mem_aq (%h)",
				expected_stamofu_cq_enq_mem_aq, DUT_stamofu_cq_enq_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_io_aq !== DUT_stamofu_cq_enq_io_aq) begin
			$display("TB ERROR: expected_stamofu_cq_enq_io_aq (%h) != DUT_stamofu_cq_enq_io_aq (%h)",
				expected_stamofu_cq_enq_io_aq, DUT_stamofu_cq_enq_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_mem_rl !== DUT_stamofu_cq_enq_mem_rl) begin
			$display("TB ERROR: expected_stamofu_cq_enq_mem_rl (%h) != DUT_stamofu_cq_enq_mem_rl (%h)",
				expected_stamofu_cq_enq_mem_rl, DUT_stamofu_cq_enq_mem_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_io_rl !== DUT_stamofu_cq_enq_io_rl) begin
			$display("TB ERROR: expected_stamofu_cq_enq_io_rl (%h) != DUT_stamofu_cq_enq_io_rl (%h)",
				expected_stamofu_cq_enq_io_rl, DUT_stamofu_cq_enq_io_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_dest_PR !== DUT_stamofu_cq_enq_dest_PR) begin
			$display("TB ERROR: expected_stamofu_cq_enq_dest_PR (%h) != DUT_stamofu_cq_enq_dest_PR (%h)",
				expected_stamofu_cq_enq_dest_PR, DUT_stamofu_cq_enq_dest_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_cq_enq_ROB_index !== DUT_stamofu_cq_enq_ROB_index) begin
			$display("TB ERROR: expected_stamofu_cq_enq_ROB_index (%h) != DUT_stamofu_cq_enq_ROB_index (%h)",
				expected_stamofu_cq_enq_ROB_index, DUT_stamofu_cq_enq_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_valid !== DUT_stamofu_iq_enq_valid) begin
			$display("TB ERROR: expected_stamofu_iq_enq_valid (%h) != DUT_stamofu_iq_enq_valid (%h)",
				expected_stamofu_iq_enq_valid, DUT_stamofu_iq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_is_store !== DUT_stamofu_iq_enq_is_store) begin
			$display("TB ERROR: expected_stamofu_iq_enq_is_store (%h) != DUT_stamofu_iq_enq_is_store (%h)",
				expected_stamofu_iq_enq_is_store, DUT_stamofu_iq_enq_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_is_amo !== DUT_stamofu_iq_enq_is_amo) begin
			$display("TB ERROR: expected_stamofu_iq_enq_is_amo (%h) != DUT_stamofu_iq_enq_is_amo (%h)",
				expected_stamofu_iq_enq_is_amo, DUT_stamofu_iq_enq_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_is_fence !== DUT_stamofu_iq_enq_is_fence) begin
			$display("TB ERROR: expected_stamofu_iq_enq_is_fence (%h) != DUT_stamofu_iq_enq_is_fence (%h)",
				expected_stamofu_iq_enq_is_fence, DUT_stamofu_iq_enq_is_fence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_op !== DUT_stamofu_iq_enq_op) begin
			$display("TB ERROR: expected_stamofu_iq_enq_op (%h) != DUT_stamofu_iq_enq_op (%h)",
				expected_stamofu_iq_enq_op, DUT_stamofu_iq_enq_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_imm12 !== DUT_stamofu_iq_enq_imm12) begin
			$display("TB ERROR: expected_stamofu_iq_enq_imm12 (%h) != DUT_stamofu_iq_enq_imm12 (%h)",
				expected_stamofu_iq_enq_imm12, DUT_stamofu_iq_enq_imm12);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_mdp_info !== DUT_stamofu_iq_enq_mdp_info) begin
			$display("TB ERROR: expected_stamofu_iq_enq_mdp_info (%h) != DUT_stamofu_iq_enq_mdp_info (%h)",
				expected_stamofu_iq_enq_mdp_info, DUT_stamofu_iq_enq_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_mem_aq !== DUT_stamofu_iq_enq_mem_aq) begin
			$display("TB ERROR: expected_stamofu_iq_enq_mem_aq (%h) != DUT_stamofu_iq_enq_mem_aq (%h)",
				expected_stamofu_iq_enq_mem_aq, DUT_stamofu_iq_enq_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_io_aq !== DUT_stamofu_iq_enq_io_aq) begin
			$display("TB ERROR: expected_stamofu_iq_enq_io_aq (%h) != DUT_stamofu_iq_enq_io_aq (%h)",
				expected_stamofu_iq_enq_io_aq, DUT_stamofu_iq_enq_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_A_PR !== DUT_stamofu_iq_enq_A_PR) begin
			$display("TB ERROR: expected_stamofu_iq_enq_A_PR (%h) != DUT_stamofu_iq_enq_A_PR (%h)",
				expected_stamofu_iq_enq_A_PR, DUT_stamofu_iq_enq_A_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_A_ready !== DUT_stamofu_iq_enq_A_ready) begin
			$display("TB ERROR: expected_stamofu_iq_enq_A_ready (%h) != DUT_stamofu_iq_enq_A_ready (%h)",
				expected_stamofu_iq_enq_A_ready, DUT_stamofu_iq_enq_A_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_A_is_zero !== DUT_stamofu_iq_enq_A_is_zero) begin
			$display("TB ERROR: expected_stamofu_iq_enq_A_is_zero (%h) != DUT_stamofu_iq_enq_A_is_zero (%h)",
				expected_stamofu_iq_enq_A_is_zero, DUT_stamofu_iq_enq_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_B_PR !== DUT_stamofu_iq_enq_B_PR) begin
			$display("TB ERROR: expected_stamofu_iq_enq_B_PR (%h) != DUT_stamofu_iq_enq_B_PR (%h)",
				expected_stamofu_iq_enq_B_PR, DUT_stamofu_iq_enq_B_PR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_B_ready !== DUT_stamofu_iq_enq_B_ready) begin
			$display("TB ERROR: expected_stamofu_iq_enq_B_ready (%h) != DUT_stamofu_iq_enq_B_ready (%h)",
				expected_stamofu_iq_enq_B_ready, DUT_stamofu_iq_enq_B_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_B_is_zero !== DUT_stamofu_iq_enq_B_is_zero) begin
			$display("TB ERROR: expected_stamofu_iq_enq_B_is_zero (%h) != DUT_stamofu_iq_enq_B_is_zero (%h)",
				expected_stamofu_iq_enq_B_is_zero, DUT_stamofu_iq_enq_B_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_ROB_index !== DUT_stamofu_iq_enq_ROB_index) begin
			$display("TB ERROR: expected_stamofu_iq_enq_ROB_index (%h) != DUT_stamofu_iq_enq_ROB_index (%h)",
				expected_stamofu_iq_enq_ROB_index, DUT_stamofu_iq_enq_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_iq_enq_cq_index !== DUT_stamofu_iq_enq_cq_index) begin
			$display("TB ERROR: expected_stamofu_iq_enq_cq_index (%h) != DUT_stamofu_iq_enq_cq_index (%h)",
				expected_stamofu_iq_enq_cq_index, DUT_stamofu_iq_enq_cq_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_enq_valid !== DUT_stamofu_aq_enq_valid) begin
			$display("TB ERROR: expected_stamofu_aq_enq_valid (%h) != DUT_stamofu_aq_enq_valid (%h)",
				expected_stamofu_aq_enq_valid, DUT_stamofu_aq_enq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_enq_mem_aq !== DUT_stamofu_aq_enq_mem_aq) begin
			$display("TB ERROR: expected_stamofu_aq_enq_mem_aq (%h) != DUT_stamofu_aq_enq_mem_aq (%h)",
				expected_stamofu_aq_enq_mem_aq, DUT_stamofu_aq_enq_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_enq_io_aq !== DUT_stamofu_aq_enq_io_aq) begin
			$display("TB ERROR: expected_stamofu_aq_enq_io_aq (%h) != DUT_stamofu_aq_enq_io_aq (%h)",
				expected_stamofu_aq_enq_io_aq, DUT_stamofu_aq_enq_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stamofu_aq_enq_ROB_index !== DUT_stamofu_aq_enq_ROB_index) begin
			$display("TB ERROR: expected_stamofu_aq_enq_ROB_index (%h) != DUT_stamofu_aq_enq_ROB_index (%h)",
				expected_stamofu_aq_enq_ROB_index, DUT_stamofu_aq_enq_ROB_index);
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
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0000;
		tb_dispatch_valid_fence_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_dispatch_mem_aq_by_way = 4'b0000;
		tb_dispatch_io_aq_by_way = 4'b0000;
		tb_dispatch_mem_rl_by_way = 4'b0000;
		tb_dispatch_io_rl_by_way = 4'b0000;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0000;
		expected_stamofu_cq_enq_mdp_info = 8'h0;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h0;
		expected_stamofu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0000;
		expected_stamofu_iq_enq_imm12 = 12'h0;
		expected_stamofu_iq_enq_mdp_info = 8'h0;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h0;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h0;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h0;
		expected_stamofu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0000;
		tb_dispatch_valid_fence_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0000, 4'b0000, 4'b0000, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h0, 12'h0, 12'h0, 12'h0};
		tb_dispatch_mdp_info_by_way = {8'h0, 8'h0, 8'h0, 8'h0};
		tb_dispatch_mem_aq_by_way = 4'b0000;
		tb_dispatch_io_aq_by_way = 4'b0000;
		tb_dispatch_mem_rl_by_way = 4'b0000;
		tb_dispatch_io_rl_by_way = 4'b0000;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_B_ready_by_way = 4'b0000;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
		tb_dispatch_ROB_index_by_way = {7'h0, 7'h0, 7'h0, 7'h0};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0000;
		expected_stamofu_cq_enq_mdp_info = 8'h0;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h0;
		expected_stamofu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0000;
		expected_stamofu_iq_enq_imm12 = 12'h0;
		expected_stamofu_iq_enq_mdp_info = 8'h0;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h0;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h0;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h0;
		expected_stamofu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

        // ------------------------------------------------------------
        // sequence:
        test_case = "sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v s 3 r,n",
			"\n\t\t\t", "2: v f 2 n,n",
			"\n\t\t\t", "1: v a 1 n,r",
			"\n\t\t\t", "0: v s 0 z,z",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: i",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1111;
		tb_dispatch_valid_store_by_way = 4'b1001;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0011, 4'b0010, 4'b0001, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h333, 12'h222, 12'h111, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h33, 8'h22, 8'h11, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b1010;
		tb_dispatch_io_aq_by_way = 4'b1100;
		tb_dispatch_mem_rl_by_way = 4'b0000;
		tb_dispatch_io_rl_by_way = 4'b0000;
		tb_dispatch_A_PR_by_way = {7'h3, 7'h2, 7'h1, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b1000;
		tb_dispatch_A_is_zero_by_way = 4'b0001;
		tb_dispatch_B_PR_by_way = {7'h33, 7'h22, 7'h11, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0010;
		tb_dispatch_B_is_zero_by_way = 4'b0001;
		tb_dispatch_dest_PR_by_way = {7'h33, 7'h22, 7'h11, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h33, 7'h22, 7'h11, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b1111;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0000;
		expected_stamofu_cq_enq_mdp_info = 8'h0;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h0;
		expected_stamofu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0000;
		expected_stamofu_iq_enq_imm12 = 12'h0;
		expected_stamofu_iq_enq_mdp_info = 8'h0;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h0;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h0;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h0;
		expected_stamofu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v s 6 n,n",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v f 5 r,r",
			"\n\t\t\t", "0: v a 4 r,n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v s 3 r,nR",
			"\n\t\t\t", "2: v f 2 nR,n",
			"\n\t\t\t", "1: v a 1 n,r",
			"\n\t\t\t", "0: v s 0 z,z",
			"\n\t\tWB bus: 2,33"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1011;
		tb_dispatch_valid_store_by_way = 4'b1000;
		tb_dispatch_valid_amo_by_way = 4'b0001;
		tb_dispatch_valid_fence_by_way = 4'b0010;
		tb_dispatch_op_by_way = {4'b0110, 4'b0000, 4'b0101, 4'b0100};
		tb_dispatch_imm12_by_way = {12'h666, 12'h000, 12'h555, 12'h444};
		tb_dispatch_mdp_info_by_way = {8'h66, 8'h00, 8'h55, 8'h44};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b1000;
		tb_dispatch_mem_rl_by_way = 4'b1011;
		tb_dispatch_io_rl_by_way = 4'b0000;
		tb_dispatch_A_PR_by_way = {7'h6, 7'h0, 7'h5, 7'h4};
		tb_dispatch_A_ready_by_way = 4'b0011;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_B_ready_by_way = 4'b0010;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_ROB_index_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b1100;
		tb_WB_bus_upper_PR_by_bank = {5'hc, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 0;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b1;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0000;
		expected_stamofu_cq_enq_mdp_info = 8'h0;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h0;
		expected_stamofu_cq_enq_ROB_index = 7'h0;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b1;
		expected_stamofu_iq_enq_is_store = 1'b1;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0000;
		expected_stamofu_iq_enq_imm12 = 12'h000;
		expected_stamofu_iq_enq_mdp_info = 8'h00;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h0;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b1;
		expected_stamofu_iq_enq_B_PR = 7'h00;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b1;
		expected_stamofu_iq_enq_ROB_index = 7'h00;
		expected_stamofu_iq_enq_cq_index = 0;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h0;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v s 6 n,n",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v f 5 r,r",
			"\n\t\t\t", "0: v a 4 r,n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v s 3 r,r",
			"\n\t\t\t", "1: v f 2 r,n",
			"\n\t\t\t", "0: v a 1 nR,r",
			"\n\t\tWB bus: 1"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1011;
		tb_dispatch_valid_store_by_way = 4'b1000;
		tb_dispatch_valid_amo_by_way = 4'b0001;
		tb_dispatch_valid_fence_by_way = 4'b0010;
		tb_dispatch_op_by_way = {4'b0110, 4'b0000, 4'b0101, 4'b0100};
		tb_dispatch_imm12_by_way = {12'h666, 12'h000, 12'h555, 12'h444};
		tb_dispatch_mdp_info_by_way = {8'h66, 8'h00, 8'h55, 8'h44};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b1000;
		tb_dispatch_mem_rl_by_way = 4'b1011;
		tb_dispatch_io_rl_by_way = 4'b0000;
		tb_dispatch_A_PR_by_way = {7'h6, 7'h0, 7'h5, 7'h4};
		tb_dispatch_A_ready_by_way = 4'b0011;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_B_ready_by_way = 4'b0010;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_ROB_index_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0010;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 1;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0001;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b1;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0001;
		expected_stamofu_cq_enq_mdp_info = 8'h11;
		expected_stamofu_cq_enq_mem_aq = 1'b1;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h11;
		expected_stamofu_cq_enq_ROB_index = 7'h11;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b1;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b1;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0001;
		expected_stamofu_iq_enq_imm12 = 12'h111;
		expected_stamofu_iq_enq_mdp_info = 8'h11;
		expected_stamofu_iq_enq_mem_aq = 1'b1;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h1;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h11;
		expected_stamofu_iq_enq_B_ready = 1'b1;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h11;
		expected_stamofu_iq_enq_cq_index = 1;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b1;
		expected_stamofu_aq_enq_mem_aq = 1'b1;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h11;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v s 6 n,n",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v f 5 r,r",
			"\n\t\t\t", "0: i a 4 r,n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v a 4 r,n",
			"\n\t\t\t", "1: v s 3 r,r",
			"\n\t\t\t", "0: v f 2 r,n",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1010;
		tb_dispatch_valid_store_by_way = 4'b1000;
		tb_dispatch_valid_amo_by_way = 4'b0000;
		tb_dispatch_valid_fence_by_way = 4'b0010;
		tb_dispatch_op_by_way = {4'b0110, 4'b0000, 4'b0101, 4'b0100};
		tb_dispatch_imm12_by_way = {12'h666, 12'h000, 12'h555, 12'h444};
		tb_dispatch_mdp_info_by_way = {8'h66, 8'h00, 8'h55, 8'h44};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b1000;
		tb_dispatch_mem_rl_by_way = 4'b1011;
		tb_dispatch_io_rl_by_way = 4'b0000;
		tb_dispatch_A_PR_by_way = {7'h6, 7'h0, 7'h5, 7'h4};
		tb_dispatch_A_ready_by_way = 4'b0011;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_B_ready_by_way = 4'b0010;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_ROB_index_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 2;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h0;
		tb_rob_kill_rel_kill_younger_index = 7'h0;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0010;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b1;
		expected_stamofu_cq_enq_op = 4'b0010;
		expected_stamofu_cq_enq_mdp_info = 8'h22;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b1;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h22;
		expected_stamofu_cq_enq_ROB_index = 7'h22;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b1;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b1;
		expected_stamofu_iq_enq_op = 4'b0010;
		expected_stamofu_iq_enq_imm12 = 12'h222;
		expected_stamofu_iq_enq_mdp_info = 8'h22;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b1;
		expected_stamofu_iq_enq_A_PR = 7'h2;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h22;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h22;
		expected_stamofu_iq_enq_cq_index = 2;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b1;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b1;
		expected_stamofu_aq_enq_ROB_index = 7'h22;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: v s 6 n,n",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i f 5 r,r",
			"\n\t\t\t", "0: i a 4 r,n",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 5 r,r",
			"\n\t\t\t", "1: v a 4 r,n",
			"\n\t\t\t", "0: v s 3 r,r (iq not ready)",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b1000;
		tb_dispatch_valid_store_by_way = 4'b1000;
		tb_dispatch_valid_amo_by_way = 4'b0000;
		tb_dispatch_valid_fence_by_way = 4'b0000;
		tb_dispatch_op_by_way = {4'b0110, 4'b0000, 4'b0101, 4'b0100};
		tb_dispatch_imm12_by_way = {12'h666, 12'h000, 12'h555, 12'h444};
		tb_dispatch_mdp_info_by_way = {8'h66, 8'h00, 8'h55, 8'h44};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b1000;
		tb_dispatch_mem_rl_by_way = 4'b1011;
		tb_dispatch_io_rl_by_way = 4'b0000;
		tb_dispatch_A_PR_by_way = {7'h6, 7'h0, 7'h5, 7'h4};
		tb_dispatch_A_ready_by_way = 4'b0011;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_B_ready_by_way = 4'b0010;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
		tb_dispatch_ROB_index_by_way = {7'h66, 7'h00, 7'h55, 7'h44};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 3;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b1000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b1;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0011;
		expected_stamofu_cq_enq_mdp_info = 8'h33;
		expected_stamofu_cq_enq_mem_aq = 1'b1;
		expected_stamofu_cq_enq_io_aq = 1'b1;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h33;
		expected_stamofu_cq_enq_ROB_index = 7'h33;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b1;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0011;
		expected_stamofu_iq_enq_imm12 = 12'h333;
		expected_stamofu_iq_enq_mdp_info = 8'h33;
		expected_stamofu_iq_enq_mem_aq = 1'b1;
		expected_stamofu_iq_enq_io_aq = 1'b1;
		expected_stamofu_iq_enq_A_PR = 7'h3;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h33;
		expected_stamofu_iq_enq_B_ready = 1'b1;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h33;
		expected_stamofu_iq_enq_cq_index = 3;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b1;
		expected_stamofu_aq_enq_io_aq = 1'b1;
		expected_stamofu_aq_enq_ROB_index = 7'h33;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 8 n,r",
			"\n\t\t\t", "1: v a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v s 6 n,n",
			"\n\t\t\t", "2: v f 5 r,r",
			"\n\t\t\t", "1: v a 4 r,n",
			"\n\t\t\t", "0: v s 3 r,r",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0110;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 3;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b1;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0011;
		expected_stamofu_cq_enq_mdp_info = 8'h33;
		expected_stamofu_cq_enq_mem_aq = 1'b1;
		expected_stamofu_cq_enq_io_aq = 1'b1;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h33;
		expected_stamofu_cq_enq_ROB_index = 7'h33;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b1;
		expected_stamofu_iq_enq_is_store = 1'b1;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0011;
		expected_stamofu_iq_enq_imm12 = 12'h333;
		expected_stamofu_iq_enq_mdp_info = 8'h33;
		expected_stamofu_iq_enq_mem_aq = 1'b1;
		expected_stamofu_iq_enq_io_aq = 1'b1;
		expected_stamofu_iq_enq_A_PR = 7'h3;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h33;
		expected_stamofu_iq_enq_B_ready = 1'b1;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h33;
		expected_stamofu_iq_enq_cq_index = 3;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b1;
		expected_stamofu_aq_enq_mem_aq = 1'b1;
		expected_stamofu_aq_enq_io_aq = 1'b1;
		expected_stamofu_aq_enq_ROB_index = 7'h33;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 8 n,r",
			"\n\t\t\t", "1: v a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v s 6 n,n",
			"\n\t\t\t", "1: v f 5 r,r",
			"\n\t\t\t", "0: v a 4 r,n (cq not ready)",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0110;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b0;
		tb_stamofu_cq_enq_index = 4;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0010;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b1;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0100;
		expected_stamofu_cq_enq_mdp_info = 8'h44;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b1;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h44;
		expected_stamofu_cq_enq_ROB_index = 7'h44;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b1;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0100;
		expected_stamofu_iq_enq_imm12 = 12'h444;
		expected_stamofu_iq_enq_mdp_info = 8'h44;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h4;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h44;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h44;
		expected_stamofu_iq_enq_cq_index = 4;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h44;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v a 7 n,n",
			"\n\t\t\t", "2: v s 6 n,n",
			"\n\t\t\t", "1: v f 5 r,r",
			"\n\t\t\t", "0: v a 4 r,n",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0100;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 4;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b1;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b1;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0100;
		expected_stamofu_cq_enq_mdp_info = 8'h44;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b1;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h44;
		expected_stamofu_cq_enq_ROB_index = 7'h44;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b1;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b1;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0100;
		expected_stamofu_iq_enq_imm12 = 12'h444;
		expected_stamofu_iq_enq_mdp_info = 8'h44;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h4;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h44;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h44;
		expected_stamofu_iq_enq_cq_index = 4;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h44;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: vK a 7 n,n",
			"\n\t\t\t", "1: vK s 6 n,n",
			"\n\t\t\t", "0: v f 5 r,r (aq not ready)",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0100;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 5;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b1;
		tb_rob_kill_abs_head_index = 7'h44;
		tb_rob_kill_rel_kill_younger_index = 7'h11;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0100;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b1;
		expected_stamofu_cq_enq_op = 4'b0101;
		expected_stamofu_cq_enq_mdp_info = 8'h55;
		expected_stamofu_cq_enq_mem_aq = 1'b1;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b1;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h55;
		expected_stamofu_cq_enq_ROB_index = 7'h55;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b1;
		expected_stamofu_iq_enq_op = 4'b0101;
		expected_stamofu_iq_enq_imm12 = 12'h555;
		expected_stamofu_iq_enq_mdp_info = 8'h55;
		expected_stamofu_iq_enq_mem_aq = 1'b1;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h5;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h55;
		expected_stamofu_iq_enq_B_ready = 1'b1;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h55;
		expected_stamofu_iq_enq_cq_index = 5;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b1;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h55;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: v f 8 n,r",
			"\n\t\t\t", "2: k a 7 n,n",
			"\n\t\t\t", "1: k s 6 n,n",
			"\n\t\t\t", "0: v f 5 r,r",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 5;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b1;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b1;
		expected_stamofu_cq_enq_op = 4'b0101;
		expected_stamofu_cq_enq_mdp_info = 8'h55;
		expected_stamofu_cq_enq_mem_aq = 1'b1;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b1;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h55;
		expected_stamofu_cq_enq_ROB_index = 7'h55;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b1;
		expected_stamofu_iq_enq_op = 4'b0101;
		expected_stamofu_iq_enq_imm12 = 12'h555;
		expected_stamofu_iq_enq_mdp_info = 8'h55;
		expected_stamofu_iq_enq_mem_aq = 1'b1;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h5;
		expected_stamofu_iq_enq_A_ready = 1'b1;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h55;
		expected_stamofu_iq_enq_B_ready = 1'b1;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h55;
		expected_stamofu_iq_enq_cq_index = 5;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b1;
		expected_stamofu_aq_enq_mem_aq = 1'b1;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h55;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 8 n,r",
			"\n\t\t\t", "1: k a 7 n,n",
			"\n\t\t\t", "0: k s 6 n,n (cq not ready)",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b0;
		tb_stamofu_cq_enq_index = 6;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b1;
		expected_stamofu_cq_enq_is_store = 1'b1;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0110;
		expected_stamofu_cq_enq_mdp_info = 8'h66;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b1;
		expected_stamofu_cq_enq_mem_rl = 1'b1;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h66;
		expected_stamofu_cq_enq_ROB_index = 7'h66;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b1;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0110;
		expected_stamofu_iq_enq_imm12 = 12'h666;
		expected_stamofu_iq_enq_mdp_info = 8'h66;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b1;
		expected_stamofu_iq_enq_A_PR = 7'h6;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h66;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h66;
		expected_stamofu_iq_enq_cq_index = 6;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b1;
		expected_stamofu_aq_enq_ROB_index = 7'h66;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: v f 8 n,r",
			"\n\t\t\t", "1: k a 7 n,n",
			"\n\t\t\t", "0: k s 6 n,n",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 6;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b1;
		expected_stamofu_cq_enq_is_store = 1'b1;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0110;
		expected_stamofu_cq_enq_mdp_info = 8'h66;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b1;
		expected_stamofu_cq_enq_mem_rl = 1'b1;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h66;
		expected_stamofu_cq_enq_ROB_index = 7'h66;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b1;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0110;
		expected_stamofu_iq_enq_imm12 = 12'h666;
		expected_stamofu_iq_enq_mdp_info = 8'h66;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b1;
		expected_stamofu_iq_enq_A_PR = 7'h6;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h66;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h66;
		expected_stamofu_iq_enq_cq_index = 6;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b1;
		expected_stamofu_aq_enq_ROB_index = 7'h66;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: v f 8 n,r",
			"\n\t\t\t", "0: k a 7 n,n",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 7;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b1;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b1;
		expected_stamofu_cq_enq_is_fence = 1'b0;
		expected_stamofu_cq_enq_op = 4'b0111;
		expected_stamofu_cq_enq_mdp_info = 8'h77;
		expected_stamofu_cq_enq_mem_aq = 1'b1;
		expected_stamofu_cq_enq_io_aq = 1'b1;
		expected_stamofu_cq_enq_mem_rl = 1'b1;
		expected_stamofu_cq_enq_io_rl = 1'b0;
		expected_stamofu_cq_enq_dest_PR = 7'h77;
		expected_stamofu_cq_enq_ROB_index = 7'h77;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b1;
		expected_stamofu_iq_enq_is_fence = 1'b0;
		expected_stamofu_iq_enq_op = 4'b0111;
		expected_stamofu_iq_enq_imm12 = 12'h777;
		expected_stamofu_iq_enq_mdp_info = 8'h77;
		expected_stamofu_iq_enq_mem_aq = 1'b1;
		expected_stamofu_iq_enq_io_aq = 1'b1;
		expected_stamofu_iq_enq_A_PR = 7'h7;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h77;
		expected_stamofu_iq_enq_B_ready = 1'b0;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h77;
		expected_stamofu_iq_enq_cq_index = 7;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b1;
		expected_stamofu_aq_enq_io_aq = 1'b1;
		expected_stamofu_aq_enq_ROB_index = 7'h77;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v f 8 n,r (cq not ready)",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b0;
		tb_stamofu_cq_enq_index = 8;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b0;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b1;
		expected_stamofu_cq_enq_op = 4'b1000;
		expected_stamofu_cq_enq_mdp_info = 8'h88;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b1;
		expected_stamofu_cq_enq_dest_PR = 7'h88;
		expected_stamofu_cq_enq_ROB_index = 7'h88;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b1;
		expected_stamofu_iq_enq_op = 4'b1000;
		expected_stamofu_iq_enq_imm12 = 12'h888;
		expected_stamofu_iq_enq_mdp_info = 8'h88;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h8;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h88;
		expected_stamofu_iq_enq_B_ready = 1'b1;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h88;
		expected_stamofu_iq_enq_cq_index = 8;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h88;
	    // acquire queue enqueue feedback
	    // ROB kill

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"\n\t\tDispatch:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i f 8 n,r",
			"\n\t\t\t", "1: i a 7 n,n",
			"\n\t\t\t", "0: i",
			"\n\t\tEntries:",
			"\n\t\t\t", "3: i",
			"\n\t\t\t", "2: i",
			"\n\t\t\t", "1: i",
			"\n\t\t\t", "0: v f 8 n,r",
			"\n\t\tWB bus:"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // op dispatch by way
		tb_dispatch_attempt_by_way = 4'b0000;
		tb_dispatch_valid_store_by_way = 4'b0000;
		tb_dispatch_valid_amo_by_way = 4'b0010;
		tb_dispatch_valid_fence_by_way = 4'b0100;
		tb_dispatch_op_by_way = {4'b0000, 4'b1000, 4'b0111, 4'b0000};
		tb_dispatch_imm12_by_way = {12'h000, 12'h888, 12'h777, 12'h000};
		tb_dispatch_mdp_info_by_way = {8'h00, 8'h88, 8'h77, 8'h00};
		tb_dispatch_mem_aq_by_way = 4'b0010;
		tb_dispatch_io_aq_by_way = 4'b0010;
		tb_dispatch_mem_rl_by_way = 4'b0010;
		tb_dispatch_io_rl_by_way = 4'b0100;
		tb_dispatch_A_PR_by_way = {7'h0, 7'h8, 7'h7, 7'h0};
		tb_dispatch_A_ready_by_way = 4'b0000;
		tb_dispatch_A_is_zero_by_way = 4'b0000;
		tb_dispatch_B_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_B_ready_by_way = 4'b0100;
		tb_dispatch_B_is_zero_by_way = 4'b0000;
		tb_dispatch_dest_PR_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
		tb_dispatch_ROB_index_by_way = {7'h00, 7'h88, 7'h77, 7'h00};
	    // op dispatch feedback
	    // writeback bus by bank
		tb_WB_bus_valid_by_bank = 4'b0000;
		tb_WB_bus_upper_PR_by_bank = {5'h0, 5'h0, 5'h0, 5'h0};
	    // op enqueue to central queue
	    // central queue enqueue feedback
		tb_stamofu_cq_enq_ready = 1'b1;
		tb_stamofu_cq_enq_index = 8;
	    // op enqueue to issue queue
	    // issue queue enqueue feedback
		tb_stamofu_iq_enq_ready = 1'b0;
	    // op enqueue to acquire queue
	    // acquire queue enqueue feedback
		tb_stamofu_aq_enq_ready = 1'b0;
	    // ROB kill
		tb_rob_kill_valid = 1'b0;
		tb_rob_kill_abs_head_index = 7'h31;
		tb_rob_kill_rel_kill_younger_index = 7'h1;

		@(negedge CLK);

		// outputs:

	    // op dispatch by way
	    // op dispatch feedback
		expected_dispatch_ack_by_way = 4'b0000;
	    // writeback bus by bank
	    // op enqueue to central queue
		expected_stamofu_cq_enq_valid = 1'b1;
		expected_stamofu_cq_enq_killed = 1'b0;
		expected_stamofu_cq_enq_is_store = 1'b0;
		expected_stamofu_cq_enq_is_amo = 1'b0;
		expected_stamofu_cq_enq_is_fence = 1'b1;
		expected_stamofu_cq_enq_op = 4'b1000;
		expected_stamofu_cq_enq_mdp_info = 8'h88;
		expected_stamofu_cq_enq_mem_aq = 1'b0;
		expected_stamofu_cq_enq_io_aq = 1'b0;
		expected_stamofu_cq_enq_mem_rl = 1'b0;
		expected_stamofu_cq_enq_io_rl = 1'b1;
		expected_stamofu_cq_enq_dest_PR = 7'h88;
		expected_stamofu_cq_enq_ROB_index = 7'h88;
	    // central queue enqueue feedback
	    // op enqueue to issue queue
		expected_stamofu_iq_enq_valid = 1'b0;
		expected_stamofu_iq_enq_is_store = 1'b0;
		expected_stamofu_iq_enq_is_amo = 1'b0;
		expected_stamofu_iq_enq_is_fence = 1'b1;
		expected_stamofu_iq_enq_op = 4'b1000;
		expected_stamofu_iq_enq_imm12 = 12'h888;
		expected_stamofu_iq_enq_mdp_info = 8'h88;
		expected_stamofu_iq_enq_mem_aq = 1'b0;
		expected_stamofu_iq_enq_io_aq = 1'b0;
		expected_stamofu_iq_enq_A_PR = 7'h8;
		expected_stamofu_iq_enq_A_ready = 1'b0;
		expected_stamofu_iq_enq_A_is_zero = 1'b0;
		expected_stamofu_iq_enq_B_PR = 7'h88;
		expected_stamofu_iq_enq_B_ready = 1'b1;
		expected_stamofu_iq_enq_B_is_zero = 1'b0;
		expected_stamofu_iq_enq_ROB_index = 7'h88;
		expected_stamofu_iq_enq_cq_index = 8;
	    // issue queue enqueue feedback
	    // op enqueue to acquire queue
		expected_stamofu_aq_enq_valid = 1'b0;
		expected_stamofu_aq_enq_mem_aq = 1'b0;
		expected_stamofu_aq_enq_io_aq = 1'b0;
		expected_stamofu_aq_enq_ROB_index = 7'h88;
	    // acquire queue enqueue feedback
	    // ROB kill

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