/*
    Filename: btb_tb.sv
    Author: zlagpacan
    Description: Testbench for btb module. 
    Spec: LOROF/spec/design/btb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb_tb ();

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


    // REQ stage
	logic tb_valid_REQ;
	logic [29:0] tb_PC30_REQ;

    // RESP stage
	logic [3:0][29:0] tb_PC30_by_way_RESP;

	logic [3:0] DUT_vtm_by_way_RESP, expected_vtm_by_way_RESP;
	logic [3:0][BTB_PRED_INFO_WIDTH-1:0] DUT_pred_info_by_way_RESP, expected_pred_info_by_way_RESP;
	logic [3:0][BTB_TARGET_WIDTH-1:0] DUT_target_by_way_RESP, expected_target_by_way_RESP;

    // update
	logic tb_update_valid;
	logic [29:0] tb_update_start_PC30;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_update_pred_info;
	logic [29:0] tb_update_target_PC30;

    // ----------------------------------------------------------------
    // DUT instantiation:

	btb DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // REQ stage
		.valid_REQ(tb_valid_REQ),
		.PC30_REQ(tb_PC30_REQ),

	    // RESP stage
		.PC30_by_way_RESP(tb_PC30_by_way_RESP),

		.vtm_by_way_RESP(DUT_vtm_by_way_RESP),
		.pred_info_by_way_RESP(DUT_pred_info_by_way_RESP),
		.target_by_way_RESP(DUT_target_by_way_RESP),

	    // update
		.update_valid(tb_update_valid),
		.update_start_PC30(tb_update_start_PC30),
		.update_pred_info(tb_update_pred_info),
		.update_target_PC30(tb_update_target_PC30)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_vtm_by_way_RESP !== DUT_vtm_by_way_RESP) begin
			$display("TB ERROR: expected_vtm_by_way_RESP (%h) != DUT_vtm_by_way_RESP (%h)",
				expected_vtm_by_way_RESP, DUT_vtm_by_way_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pred_info_by_way_RESP !== DUT_pred_info_by_way_RESP) begin
			$display("TB ERROR: expected_pred_info_by_way_RESP (%h) != DUT_pred_info_by_way_RESP (%h)",
				expected_pred_info_by_way_RESP, DUT_pred_info_by_way_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_target_by_way_RESP !== DUT_target_by_way_RESP) begin
			$display("TB ERROR: expected_target_by_way_RESP (%h) != DUT_target_by_way_RESP (%h)",
				expected_target_by_way_RESP, DUT_target_by_way_RESP);
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
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_PC30_REQ = 30'h0;
	    // RESP stage
		tb_PC30_by_way_RESP = {30'h0, 30'h0, 30'h0, 30'h0};
	    // update
		tb_update_valid = 1'b0;
		tb_update_start_PC30 = 30'h0;
		tb_update_pred_info = 8'h0;
		tb_update_target_PC30 = 30'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_vtm_by_way_RESP = 4'b1111;
		expected_pred_info_by_way_RESP[0] = '0;
		expected_pred_info_by_way_RESP[1] = '0;
		expected_pred_info_by_way_RESP[2] = '0;
		expected_pred_info_by_way_RESP[3] = '0;
		expected_target_by_way_RESP[0] = '0;
		expected_target_by_way_RESP[1] = '0;
		expected_target_by_way_RESP[2] = '0;
		expected_target_by_way_RESP[3] = '0;
	    // update

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_PC30_REQ = 30'h0;
	    // RESP stage
		tb_PC30_by_way_RESP = {30'h0, 30'h0, 30'h0, 30'h0};
	    // update
		tb_update_valid = 1'b0;
		tb_update_start_PC30 = 30'h0;
		tb_update_pred_info = 8'h0;
		tb_update_target_PC30 = 30'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_vtm_by_way_RESP = 4'b1111;
		expected_pred_info_by_way_RESP[0] = '0;
		expected_pred_info_by_way_RESP[1] = '0;
		expected_pred_info_by_way_RESP[2] = '0;
		expected_pred_info_by_way_RESP[3] = '0;
		expected_target_by_way_RESP[0] = '0;
		expected_target_by_way_RESP[1] = '0;
		expected_target_by_way_RESP[2] = '0;
		expected_target_by_way_RESP[3] = '0;
	    // update

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
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_PC30_REQ = 30'h0;
	    // RESP stage
		tb_PC30_by_way_RESP = {30'h0, 30'h0, 30'h0, 30'h0};
	    // update
		tb_update_valid = 1'b0;
		tb_update_start_PC30 = 30'h0;
		tb_update_pred_info = 8'h0;
		tb_update_target_PC30 = 30'h0;

		@(negedge CLK);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_vtm_by_way_RESP = 4'b1111;
		expected_pred_info_by_way_RESP[0] = '0;
		expected_pred_info_by_way_RESP[1] = '0;
		expected_pred_info_by_way_RESP[2] = '0;
		expected_pred_info_by_way_RESP[3] = '0;
		expected_target_by_way_RESP[0] = '0;
		expected_target_by_way_RESP[1] = '0;
		expected_target_by_way_RESP[2] = '0;
		expected_target_by_way_RESP[3] = '0;
	    // update

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