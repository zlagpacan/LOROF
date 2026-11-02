/*
    Filename: ssu_tb.sv
    Author: zlagpacan
    Description: Testbench for ssu module. 
    Spec: LOROF/spec/design/ssu.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module ssu_tb #(
	parameter STORE_SET_COUNT = 64,
	parameter SSID_WIDTH = $clog2(STORE_SET_COUNT),
	parameter SSU_INPUT_BUFFER_ENTRIES = 2,
	parameter SSU_FUNNEL_BUFFER_ENTRIES = 2
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

    // ldu_cq CAM update
        // implied dep
	logic tb_ldu_cq_CAM_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_cq_CAM_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_cq_CAM_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_cq_CAM_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_cq_CAM_update_stamo_ROB_index;

    // ldu_mq CAM update
        // implied dep
	logic tb_ldu_mq_CAM_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_mq_CAM_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_mq_CAM_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_mq_CAM_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_mq_CAM_update_stamo_ROB_index;

    // ldu_cq commit update
        // implied no dep
        // incorporates ldu_mq commit update
	logic tb_ldu_cq_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_ldu_cq_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_ldu_cq_commit_update_ROB_index;

    // stamofu_cq CAM update bank 0
        // implied dep
        // incorporates stamofu_mq CAM update
	logic tb_stamofu_cq_CAM_bank0_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_cq_CAM_bank0_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_cq_CAM_bank0_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_cq_CAM_bank0_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_cq_CAM_bank0_update_stamo_ROB_index;

    // stamofu_cq CAM update bank 1
        // implied dep
        // incorporates stamofu_mq CAM update
	logic tb_stamofu_cq_CAM_bank1_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_cq_CAM_bank1_update_ld_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_cq_CAM_bank1_update_ld_ROB_index;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_cq_CAM_bank1_update_stamo_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_cq_CAM_bank1_update_stamo_ROB_index;

    // stamofu_cq commit update
        // implied no dep
        // incorporates stamofu_mq commit update
	logic tb_stamofu_cq_commit_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] tb_stamofu_cq_commit_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] tb_stamofu_cq_commit_update_ROB_index;

    // mdp update to ROB
	logic DUT_rob_mdp_update_valid, expected_rob_mdp_update_valid;
	logic [MDPT_INFO_WIDTH-1:0] DUT_rob_mdp_update_mdp_info, expected_rob_mdp_update_mdp_info;
	logic [LOG_ROB_ENTRIES-1:0] DUT_rob_mdp_update_ROB_index, expected_rob_mdp_update_ROB_index;

	// mdp update feedback from ROB
	logic tb_rob_mdp_update_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ssu #(
		.STORE_SET_COUNT(STORE_SET_COUNT),
		.SSID_WIDTH(SSID_WIDTH),
		.SSU_INPUT_BUFFER_ENTRIES(SSU_INPUT_BUFFER_ENTRIES),
		.SSU_FUNNEL_BUFFER_ENTRIES(SSU_FUNNEL_BUFFER_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // ldu_cq CAM update
	        // implied dep
		.ldu_cq_CAM_update_valid(tb_ldu_cq_CAM_update_valid),
		.ldu_cq_CAM_update_ld_mdp_info(tb_ldu_cq_CAM_update_ld_mdp_info),
		.ldu_cq_CAM_update_ld_ROB_index(tb_ldu_cq_CAM_update_ld_ROB_index),
		.ldu_cq_CAM_update_stamo_mdp_info(tb_ldu_cq_CAM_update_stamo_mdp_info),
		.ldu_cq_CAM_update_stamo_ROB_index(tb_ldu_cq_CAM_update_stamo_ROB_index),

	    // ldu_mq CAM update
	        // implied dep
		.ldu_mq_CAM_update_valid(tb_ldu_mq_CAM_update_valid),
		.ldu_mq_CAM_update_ld_mdp_info(tb_ldu_mq_CAM_update_ld_mdp_info),
		.ldu_mq_CAM_update_ld_ROB_index(tb_ldu_mq_CAM_update_ld_ROB_index),
		.ldu_mq_CAM_update_stamo_mdp_info(tb_ldu_mq_CAM_update_stamo_mdp_info),
		.ldu_mq_CAM_update_stamo_ROB_index(tb_ldu_mq_CAM_update_stamo_ROB_index),

	    // ldu_cq commit update
	        // implied no dep
	        // incorporates ldu_mq commit update
		.ldu_cq_commit_update_valid(tb_ldu_cq_commit_update_valid),
		.ldu_cq_commit_update_mdp_info(tb_ldu_cq_commit_update_mdp_info),
		.ldu_cq_commit_update_ROB_index(tb_ldu_cq_commit_update_ROB_index),

	    // stamofu_cq CAM update bank 0
	        // implied dep
	        // incorporates stamofu_mq CAM update
		.stamofu_cq_CAM_bank0_update_valid(tb_stamofu_cq_CAM_bank0_update_valid),
		.stamofu_cq_CAM_bank0_update_ld_mdp_info(tb_stamofu_cq_CAM_bank0_update_ld_mdp_info),
		.stamofu_cq_CAM_bank0_update_ld_ROB_index(tb_stamofu_cq_CAM_bank0_update_ld_ROB_index),
		.stamofu_cq_CAM_bank0_update_stamo_mdp_info(tb_stamofu_cq_CAM_bank0_update_stamo_mdp_info),
		.stamofu_cq_CAM_bank0_update_stamo_ROB_index(tb_stamofu_cq_CAM_bank0_update_stamo_ROB_index),

	    // stamofu_cq CAM update bank 1
	        // implied dep
	        // incorporates stamofu_mq CAM update
		.stamofu_cq_CAM_bank1_update_valid(tb_stamofu_cq_CAM_bank1_update_valid),
		.stamofu_cq_CAM_bank1_update_ld_mdp_info(tb_stamofu_cq_CAM_bank1_update_ld_mdp_info),
		.stamofu_cq_CAM_bank1_update_ld_ROB_index(tb_stamofu_cq_CAM_bank1_update_ld_ROB_index),
		.stamofu_cq_CAM_bank1_update_stamo_mdp_info(tb_stamofu_cq_CAM_bank1_update_stamo_mdp_info),
		.stamofu_cq_CAM_bank1_update_stamo_ROB_index(tb_stamofu_cq_CAM_bank1_update_stamo_ROB_index),

	    // stamofu_cq commit update
	        // implied no dep
	        // incorporates stamofu_mq commit update
		.stamofu_cq_commit_update_valid(tb_stamofu_cq_commit_update_valid),
		.stamofu_cq_commit_update_mdp_info(tb_stamofu_cq_commit_update_mdp_info),
		.stamofu_cq_commit_update_ROB_index(tb_stamofu_cq_commit_update_ROB_index),

	    // mdp update to ROB
		.rob_mdp_update_valid(DUT_rob_mdp_update_valid),
		.rob_mdp_update_mdp_info(DUT_rob_mdp_update_mdp_info),
		.rob_mdp_update_ROB_index(DUT_rob_mdp_update_ROB_index),

		// mdp update feedback from ROB
		.rob_mdp_update_ready(tb_rob_mdp_update_ready)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_rob_mdp_update_valid !== DUT_rob_mdp_update_valid) begin
			$display("TB ERROR: expected_rob_mdp_update_valid (%h) != DUT_rob_mdp_update_valid (%h)",
				expected_rob_mdp_update_valid, DUT_rob_mdp_update_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_mdp_update_mdp_info !== DUT_rob_mdp_update_mdp_info) begin
			$display("TB ERROR: expected_rob_mdp_update_mdp_info (%h) != DUT_rob_mdp_update_mdp_info (%h)",
				expected_rob_mdp_update_mdp_info, DUT_rob_mdp_update_mdp_info);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_rob_mdp_update_ROB_index !== DUT_rob_mdp_update_ROB_index) begin
			$display("TB ERROR: expected_rob_mdp_update_ROB_index (%h) != DUT_rob_mdp_update_ROB_index (%h)",
				expected_rob_mdp_update_ROB_index, DUT_rob_mdp_update_ROB_index);
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
	    // ldu_cq CAM update
		tb_ldu_cq_CAM_update_valid = 1'b0;
		tb_ldu_cq_CAM_update_ld_mdp_info = 8'h00;
		tb_ldu_cq_CAM_update_ld_ROB_index = 7'h00;
		tb_ldu_cq_CAM_update_stamo_mdp_info = 8'h00;
		tb_ldu_cq_CAM_update_stamo_ROB_index = 7'h00;
	    // ldu_mq CAM update
		tb_ldu_mq_CAM_update_valid = 1'b0;
		tb_ldu_mq_CAM_update_ld_mdp_info = 8'h00;
		tb_ldu_mq_CAM_update_ld_ROB_index = 7'h00;
		tb_ldu_mq_CAM_update_stamo_mdp_info = 8'h00;
		tb_ldu_mq_CAM_update_stamo_ROB_index = 7'h00;
	    // ldu_cq commit update
		tb_ldu_cq_commit_update_valid = 1'b0;
		tb_ldu_cq_commit_update_mdp_info = 8'h00;
		tb_ldu_cq_commit_update_ROB_index = 7'h00;
	    // stamofu_cq CAM update bank 0
		tb_stamofu_cq_CAM_bank0_update_valid = 1'b0;
		tb_stamofu_cq_CAM_bank0_update_ld_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank0_update_ld_ROB_index = 7'h00;
		tb_stamofu_cq_CAM_bank0_update_stamo_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank0_update_stamo_ROB_index = 7'h00;
	    // stamofu_cq CAM update bank 1
		tb_stamofu_cq_CAM_bank1_update_valid = 1'b0;
		tb_stamofu_cq_CAM_bank1_update_ld_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank1_update_ld_ROB_index = 7'h00;
		tb_stamofu_cq_CAM_bank1_update_stamo_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank1_update_stamo_ROB_index = 7'h00;
	    // stamofu_cq commit update
		tb_stamofu_cq_commit_update_valid = 1'b0;
		tb_stamofu_cq_commit_update_mdp_info = 8'h00;
		tb_stamofu_cq_commit_update_ROB_index = 7'h00;
	    // mdp update to ROB
		// mdp update feedback from ROB
		tb_rob_mdp_update_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ldu_cq CAM update
	    // ldu_mq CAM update
	    // ldu_cq commit update
	    // stamofu_cq CAM update bank 0
	    // stamofu_cq CAM update bank 1
	    // stamofu_cq commit update
	    // mdp update to ROB
		expected_rob_mdp_update_valid = 1'b0;
		expected_rob_mdp_update_mdp_info = 8'b11000000;
		expected_rob_mdp_update_ROB_index = 7'h00;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // ldu_cq CAM update
		tb_ldu_cq_CAM_update_valid = 1'b0;
		tb_ldu_cq_CAM_update_ld_mdp_info = 8'h00;
		tb_ldu_cq_CAM_update_ld_ROB_index = 7'h00;
		tb_ldu_cq_CAM_update_stamo_mdp_info = 8'h00;
		tb_ldu_cq_CAM_update_stamo_ROB_index = 7'h00;
	    // ldu_mq CAM update
		tb_ldu_mq_CAM_update_valid = 1'b0;
		tb_ldu_mq_CAM_update_ld_mdp_info = 8'h00;
		tb_ldu_mq_CAM_update_ld_ROB_index = 7'h00;
		tb_ldu_mq_CAM_update_stamo_mdp_info = 8'h00;
		tb_ldu_mq_CAM_update_stamo_ROB_index = 7'h00;
	    // ldu_cq commit update
		tb_ldu_cq_commit_update_valid = 1'b0;
		tb_ldu_cq_commit_update_mdp_info = 8'h00;
		tb_ldu_cq_commit_update_ROB_index = 7'h00;
	    // stamofu_cq CAM update bank 0
		tb_stamofu_cq_CAM_bank0_update_valid = 1'b0;
		tb_stamofu_cq_CAM_bank0_update_ld_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank0_update_ld_ROB_index = 7'h00;
		tb_stamofu_cq_CAM_bank0_update_stamo_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank0_update_stamo_ROB_index = 7'h00;
	    // stamofu_cq CAM update bank 1
		tb_stamofu_cq_CAM_bank1_update_valid = 1'b0;
		tb_stamofu_cq_CAM_bank1_update_ld_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank1_update_ld_ROB_index = 7'h00;
		tb_stamofu_cq_CAM_bank1_update_stamo_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank1_update_stamo_ROB_index = 7'h00;
	    // stamofu_cq commit update
		tb_stamofu_cq_commit_update_valid = 1'b0;
		tb_stamofu_cq_commit_update_mdp_info = 8'h00;
		tb_stamofu_cq_commit_update_ROB_index = 7'h00;
	    // mdp update to ROB
		// mdp update feedback from ROB
		tb_rob_mdp_update_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // ldu_cq CAM update
	    // ldu_mq CAM update
	    // ldu_cq commit update
	    // stamofu_cq CAM update bank 0
	    // stamofu_cq CAM update bank 1
	    // stamofu_cq commit update
	    // mdp update to ROB
		expected_rob_mdp_update_valid = 1'b0;
		expected_rob_mdp_update_mdp_info = 8'b11000000;
		expected_rob_mdp_update_ROB_index = 7'h00;

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
	    // ldu_cq CAM update
		tb_ldu_cq_CAM_update_valid = 1'b0;
		tb_ldu_cq_CAM_update_ld_mdp_info = 8'h00;
		tb_ldu_cq_CAM_update_ld_ROB_index = 7'h00;
		tb_ldu_cq_CAM_update_stamo_mdp_info = 8'h00;
		tb_ldu_cq_CAM_update_stamo_ROB_index = 7'h00;
	    // ldu_mq CAM update
		tb_ldu_mq_CAM_update_valid = 1'b0;
		tb_ldu_mq_CAM_update_ld_mdp_info = 8'h00;
		tb_ldu_mq_CAM_update_ld_ROB_index = 7'h00;
		tb_ldu_mq_CAM_update_stamo_mdp_info = 8'h00;
		tb_ldu_mq_CAM_update_stamo_ROB_index = 7'h00;
	    // ldu_cq commit update
		tb_ldu_cq_commit_update_valid = 1'b0;
		tb_ldu_cq_commit_update_mdp_info = 8'h00;
		tb_ldu_cq_commit_update_ROB_index = 7'h00;
	    // stamofu_cq CAM update bank 0
		tb_stamofu_cq_CAM_bank0_update_valid = 1'b0;
		tb_stamofu_cq_CAM_bank0_update_ld_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank0_update_ld_ROB_index = 7'h00;
		tb_stamofu_cq_CAM_bank0_update_stamo_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank0_update_stamo_ROB_index = 7'h00;
	    // stamofu_cq CAM update bank 1
		tb_stamofu_cq_CAM_bank1_update_valid = 1'b0;
		tb_stamofu_cq_CAM_bank1_update_ld_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank1_update_ld_ROB_index = 7'h00;
		tb_stamofu_cq_CAM_bank1_update_stamo_mdp_info = 8'h00;
		tb_stamofu_cq_CAM_bank1_update_stamo_ROB_index = 7'h00;
	    // stamofu_cq commit update
		tb_stamofu_cq_commit_update_valid = 1'b0;
		tb_stamofu_cq_commit_update_mdp_info = 8'h00;
		tb_stamofu_cq_commit_update_ROB_index = 7'h00;
	    // mdp update to ROB
		// mdp update feedback from ROB
		tb_rob_mdp_update_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // ldu_cq CAM update
	    // ldu_mq CAM update
	    // ldu_cq commit update
	    // stamofu_cq CAM update bank 0
	    // stamofu_cq CAM update bank 1
	    // stamofu_cq commit update
	    // mdp update to ROB
		expected_rob_mdp_update_valid = 1'b0;
		expected_rob_mdp_update_mdp_info = 8'b11000000;
		expected_rob_mdp_update_ROB_index = 7'h00;

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