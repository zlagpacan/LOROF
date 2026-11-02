/*
    Filename: bru_pipeline_tb.sv
    Author: zlagpacan
    Description: Testbench for bru_pipeline module. 
    Spec: LOROF/spec/design/bru_pipeline.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module bru_pipeline_tb #(
	parameter IS_OC_BUFFER_SIZE = 2,
	parameter OC_ENTRIES = IS_OC_BUFFER_SIZE + 1,
	parameter FAST_FORWARD_PIPE_COUNT = 4,
	parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
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


    // BRU op issue from BRU IQ
	logic tb_issue_valid;
	logic [3:0] tb_issue_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_issue_pred_info;
	logic tb_issue_pred_lru;
	logic tb_issue_is_link_ra;
	logic tb_issue_is_ret_ra;
	logic [31:0] tb_issue_PC;
	logic [31:0] tb_issue_pred_PC;
	logic [19:0] tb_issue_imm20;
	logic tb_issue_A_is_reg;
	logic tb_issue_A_is_bus_forward;
	logic tb_issue_A_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] tb_issue_A_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_A_bank;
	logic tb_issue_B_is_reg;
	logic tb_issue_B_is_bus_forward;
	logic tb_issue_B_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] tb_issue_B_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_issue_B_bank;
	logic [LOG_PR_COUNT-1:0] tb_issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] tb_issue_ROB_index;

    // output feedback to BRU IQ
	logic DUT_issue_ready, expected_issue_ready;

    // reg read data from PRF
	logic tb_A_reg_read_resp_valid;
	logic [31:0] tb_A_reg_read_resp_data;
	logic tb_B_reg_read_resp_valid;
	logic [31:0] tb_B_reg_read_resp_data;

    // bus forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_bus_forward_data_by_bank;

    // fast forward data
	logic [FAST_FORWARD_PIPE_COUNT-1:0] tb_fast_forward_data_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] tb_fast_forward_data_by_pipe;

    // writeback data to PRF
	logic DUT_WB_valid, expected_WB_valid;
	logic [31:0] DUT_WB_data, expected_WB_data;
	logic [LOG_PR_COUNT-1:0] DUT_WB_PR, expected_WB_PR;
	logic [LOG_ROB_ENTRIES-1:0] DUT_WB_ROB_index, expected_WB_ROB_index;

    // writeback backpressure from PRF
	logic tb_WB_ready;

    // branch notification to ROB
	logic DUT_branch_notif_valid, expected_branch_notif_valid;
	logic [LOG_ROB_ENTRIES-1:0] DUT_branch_notif_ROB_index, expected_branch_notif_ROB_index;
	logic DUT_branch_notif_is_mispredict, expected_branch_notif_is_mispredict;
	logic DUT_branch_notif_is_taken, expected_branch_notif_is_taken;
	logic DUT_branch_notif_use_upct, expected_branch_notif_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_branch_notif_updated_pred_info, expected_branch_notif_updated_pred_info;
	logic DUT_branch_notif_pred_lru, expected_branch_notif_pred_lru;
	logic [31:0] DUT_branch_notif_start_PC, expected_branch_notif_start_PC;
	logic [31:0] DUT_branch_notif_target_PC, expected_branch_notif_target_PC;

    // branch notification backpressure from ROB
	logic tb_branch_notif_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bru_pipeline #(
		.IS_OC_BUFFER_SIZE(IS_OC_BUFFER_SIZE),
		.OC_ENTRIES(OC_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // BRU op issue from BRU IQ
		.issue_valid(tb_issue_valid),
		.issue_op(tb_issue_op),
		.issue_pred_info(tb_issue_pred_info),
		.issue_pred_lru(tb_issue_pred_lru),
		.issue_is_link_ra(tb_issue_is_link_ra),
		.issue_is_ret_ra(tb_issue_is_ret_ra),
		.issue_PC(tb_issue_PC),
		.issue_pred_PC(tb_issue_pred_PC),
		.issue_imm20(tb_issue_imm20),
		.issue_A_is_reg(tb_issue_A_is_reg),
		.issue_A_is_bus_forward(tb_issue_A_is_bus_forward),
		.issue_A_is_fast_forward(tb_issue_A_is_fast_forward),
		.issue_A_fast_forward_pipe(tb_issue_A_fast_forward_pipe),
		.issue_A_bank(tb_issue_A_bank),
		.issue_B_is_reg(tb_issue_B_is_reg),
		.issue_B_is_bus_forward(tb_issue_B_is_bus_forward),
		.issue_B_is_fast_forward(tb_issue_B_is_fast_forward),
		.issue_B_fast_forward_pipe(tb_issue_B_fast_forward_pipe),
		.issue_B_bank(tb_issue_B_bank),
		.issue_dest_PR(tb_issue_dest_PR),
		.issue_ROB_index(tb_issue_ROB_index),

	    // output feedback to BRU IQ
		.issue_ready(DUT_issue_ready),

	    // reg read data from PRF
		.A_reg_read_resp_valid(tb_A_reg_read_resp_valid),
		.A_reg_read_resp_data(tb_A_reg_read_resp_data),
		.B_reg_read_resp_valid(tb_B_reg_read_resp_valid),
		.B_reg_read_resp_data(tb_B_reg_read_resp_data),

	    // bus forward data from PRF
		.bus_forward_data_by_bank(tb_bus_forward_data_by_bank),

	    // fast forward data
		.fast_forward_data_valid_by_pipe(tb_fast_forward_data_valid_by_pipe),
		.fast_forward_data_by_pipe(tb_fast_forward_data_by_pipe),

	    // writeback data to PRF
		.WB_valid(DUT_WB_valid),
		.WB_data(DUT_WB_data),
		.WB_PR(DUT_WB_PR),
		.WB_ROB_index(DUT_WB_ROB_index),

	    // writeback backpressure from PRF
		.WB_ready(tb_WB_ready),

	    // branch notification to ROB
		.branch_notif_valid(DUT_branch_notif_valid),
		.branch_notif_ROB_index(DUT_branch_notif_ROB_index),
		.branch_notif_is_mispredict(DUT_branch_notif_is_mispredict),
		.branch_notif_is_taken(DUT_branch_notif_is_taken),
		.branch_notif_use_upct(DUT_branch_notif_use_upct),
		.branch_notif_updated_pred_info(DUT_branch_notif_updated_pred_info),
		.branch_notif_pred_lru(DUT_branch_notif_pred_lru),
		.branch_notif_start_PC(DUT_branch_notif_start_PC),
		.branch_notif_target_PC(DUT_branch_notif_target_PC),

	    // branch notification backpressure from ROB
		.branch_notif_ready(tb_branch_notif_ready)
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

		if (expected_branch_notif_valid !== DUT_branch_notif_valid) begin
			$display("TB ERROR: expected_branch_notif_valid (%h) != DUT_branch_notif_valid (%h)",
				expected_branch_notif_valid, DUT_branch_notif_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_ROB_index !== DUT_branch_notif_ROB_index) begin
			$display("TB ERROR: expected_branch_notif_ROB_index (%h) != DUT_branch_notif_ROB_index (%h)",
				expected_branch_notif_ROB_index, DUT_branch_notif_ROB_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_is_mispredict !== DUT_branch_notif_is_mispredict) begin
			$display("TB ERROR: expected_branch_notif_is_mispredict (%h) != DUT_branch_notif_is_mispredict (%h)",
				expected_branch_notif_is_mispredict, DUT_branch_notif_is_mispredict);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_is_taken !== DUT_branch_notif_is_taken) begin
			$display("TB ERROR: expected_branch_notif_is_taken (%h) != DUT_branch_notif_is_taken (%h)",
				expected_branch_notif_is_taken, DUT_branch_notif_is_taken);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_use_upct !== DUT_branch_notif_use_upct) begin
			$display("TB ERROR: expected_branch_notif_use_upct (%h) != DUT_branch_notif_use_upct (%h)",
				expected_branch_notif_use_upct, DUT_branch_notif_use_upct);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_updated_pred_info !== DUT_branch_notif_updated_pred_info) begin
			$display("TB ERROR: expected_branch_notif_updated_pred_info (%h) != DUT_branch_notif_updated_pred_info (%h)",
				expected_branch_notif_updated_pred_info, DUT_branch_notif_updated_pred_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_pred_lru !== DUT_branch_notif_pred_lru) begin
			$display("TB ERROR: expected_branch_notif_pred_lru (%h) != DUT_branch_notif_pred_lru (%h)",
				expected_branch_notif_pred_lru, DUT_branch_notif_pred_lru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_start_PC !== DUT_branch_notif_start_PC) begin
			$display("TB ERROR: expected_branch_notif_start_PC (%h) != DUT_branch_notif_start_PC (%h)",
				expected_branch_notif_start_PC, DUT_branch_notif_start_PC);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_branch_notif_target_PC !== DUT_branch_notif_target_PC) begin
			$display("TB ERROR: expected_branch_notif_target_PC (%h) != DUT_branch_notif_target_PC (%h)",
				expected_branch_notif_target_PC, DUT_branch_notif_target_PC);
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
	    // BRU op issue from BRU IQ
		tb_issue_valid = '0;
		tb_issue_op = '0;
		tb_issue_pred_info = '0;
		tb_issue_pred_lru = '0;
		tb_issue_is_link_ra = '0;
		tb_issue_is_ret_ra = '0;
		tb_issue_PC = '0;
		tb_issue_pred_PC = '0;
		tb_issue_imm20 = '0;
		tb_issue_A_is_reg = '0;
		tb_issue_A_is_bus_forward = '0;
		tb_issue_A_is_fast_forward = '0;
		tb_issue_A_fast_forward_pipe = '0;
		tb_issue_A_bank = '0;
		tb_issue_B_is_reg = '0;
		tb_issue_B_is_bus_forward = '0;
		tb_issue_B_is_fast_forward = '0;
		tb_issue_B_fast_forward_pipe = '0;
		tb_issue_B_bank = '0;
		tb_issue_dest_PR = '0;
		tb_issue_ROB_index = '0;
	    // output feedback to BRU IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = '0;
		tb_A_reg_read_resp_data = '0;
		tb_B_reg_read_resp_valid = '0;
		tb_B_reg_read_resp_data = '0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = '0;
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = '0;
		tb_fast_forward_data_by_pipe = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // branch notification to ROB
	    // branch notification backpressure from ROB
		tb_branch_notif_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // BRU op issue from BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000004;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // branch notification to ROB
		expected_branch_notif_valid = '0;
		expected_branch_notif_ROB_index = '0;
		expected_branch_notif_is_mispredict = '0;
		expected_branch_notif_is_taken = 1'b1;
		expected_branch_notif_use_upct = '0;
		expected_branch_notif_updated_pred_info = 8'b01000000;
		expected_branch_notif_pred_lru = '0;
		expected_branch_notif_start_PC = 32'h00000002;
		expected_branch_notif_target_PC = '0;
	    // branch notification backpressure from ROB

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // BRU op issue from BRU IQ
		tb_issue_valid = '0;
		tb_issue_op = '0;
		tb_issue_pred_info = '0;
		tb_issue_pred_lru = '0;
		tb_issue_is_link_ra = '0;
		tb_issue_is_ret_ra = '0;
		tb_issue_PC = '0;
		tb_issue_pred_PC = '0;
		tb_issue_imm20 = '0;
		tb_issue_A_is_reg = '0;
		tb_issue_A_is_bus_forward = '0;
		tb_issue_A_is_fast_forward = '0;
		tb_issue_A_fast_forward_pipe = '0;
		tb_issue_A_bank = '0;
		tb_issue_B_is_reg = '0;
		tb_issue_B_is_bus_forward = '0;
		tb_issue_B_is_fast_forward = '0;
		tb_issue_B_fast_forward_pipe = '0;
		tb_issue_B_bank = '0;
		tb_issue_dest_PR = '0;
		tb_issue_ROB_index = '0;
	    // output feedback to BRU IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = '0;
		tb_A_reg_read_resp_data = '0;
		tb_B_reg_read_resp_valid = '0;
		tb_B_reg_read_resp_data = '0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = '0;
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = '0;
		tb_fast_forward_data_by_pipe = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // branch notification to ROB
	    // branch notification backpressure from ROB
		tb_branch_notif_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // BRU op issue from BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000004;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // branch notification to ROB
		expected_branch_notif_valid = '0;
		expected_branch_notif_ROB_index = '0;
		expected_branch_notif_is_mispredict = '0;
		expected_branch_notif_is_taken = 1'b1;
		expected_branch_notif_use_upct = '0;
		expected_branch_notif_updated_pred_info = 8'b01000000;
		expected_branch_notif_pred_lru = '0;
		expected_branch_notif_start_PC = 32'h00000002;
		expected_branch_notif_target_PC = '0;
	    // branch notification backpressure from ROB

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
	    // BRU op issue from BRU IQ
		tb_issue_valid = '0;
		tb_issue_op = '0;
		tb_issue_pred_info = '0;
		tb_issue_pred_lru = '0;
		tb_issue_is_link_ra = '0;
		tb_issue_is_ret_ra = '0;
		tb_issue_PC = '0;
		tb_issue_pred_PC = '0;
		tb_issue_imm20 = '0;
		tb_issue_A_is_reg = '0;
		tb_issue_A_is_bus_forward = '0;
		tb_issue_A_is_fast_forward = '0;
		tb_issue_A_fast_forward_pipe = '0;
		tb_issue_A_bank = '0;
		tb_issue_B_is_reg = '0;
		tb_issue_B_is_bus_forward = '0;
		tb_issue_B_is_fast_forward = '0;
		tb_issue_B_fast_forward_pipe = '0;
		tb_issue_B_bank = '0;
		tb_issue_dest_PR = '0;
		tb_issue_ROB_index = '0;
	    // output feedback to BRU IQ
	    // reg read data from PRF
		tb_A_reg_read_resp_valid = '0;
		tb_A_reg_read_resp_data = '0;
		tb_B_reg_read_resp_valid = '0;
		tb_B_reg_read_resp_data = '0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = '0;
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = '0;
		tb_fast_forward_data_by_pipe = '0;
	    // writeback data to PRF
	    // writeback backpressure from PRF
		tb_WB_ready = 1'b1;
	    // branch notification to ROB
	    // branch notification backpressure from ROB
		tb_branch_notif_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // BRU op issue from BRU IQ
	    // output feedback to BRU IQ
		expected_issue_ready = 1'b1;
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // writeback data to PRF
		expected_WB_valid = 1'b0;
		expected_WB_data = 32'h00000004;
		expected_WB_PR = '0;
		expected_WB_ROB_index = '0;
	    // writeback backpressure from PRF
	    // branch notification to ROB
		expected_branch_notif_valid = '0;
		expected_branch_notif_ROB_index = '0;
		expected_branch_notif_is_mispredict = '0;
		expected_branch_notif_is_taken = 1'b1;
		expected_branch_notif_use_upct = '0;
		expected_branch_notif_updated_pred_info = 8'b01000000;
		expected_branch_notif_pred_lru = '0;
		expected_branch_notif_start_PC = 32'h00000002;
		expected_branch_notif_target_PC = '0;
	    // branch notification backpressure from ROB

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