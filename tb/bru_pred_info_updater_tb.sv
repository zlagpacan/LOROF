/*
    Filename: bru_pred_info_updater_tb.sv
    Author: zlagpacan
    Description: Testbench for bru_pred_info_updater module. 
    Spec: LOROF/spec/design/bru_pred_info_updater.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pred_info_updater_tb ();

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

    // inputs
	logic [3:0] tb_op;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_start_pred_info;
	logic tb_is_link_ra;
	logic tb_is_ret_ra;
	logic tb_is_taken;
	logic tb_is_mispredict;
	logic tb_is_out_of_range;

    // outputs
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_updated_pred_info, expected_updated_pred_info;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bru_pred_info_updater DUT (

	    // inputs
		.op(tb_op),
		.start_pred_info(tb_start_pred_info),
		.is_link_ra(tb_is_link_ra),
		.is_ret_ra(tb_is_ret_ra),
		.is_taken(tb_is_taken),
		.is_mispredict(tb_is_mispredict),
		.is_out_of_range(tb_is_out_of_range),

	    // outputs
		.updated_pred_info(DUT_updated_pred_info)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_updated_pred_info !== DUT_updated_pred_info) begin
			$display("TB ERROR: expected_updated_pred_info (%8b) != DUT_updated_pred_info (%8b)",
				expected_updated_pred_info, DUT_updated_pred_info);
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
	    // inputs
		tb_op = 4'b0000;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0000;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

        // ------------------------------------------------------------
        // basic coverage:
        test_case = "basic coverage";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JALR !, 0(!) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0000;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JALR ra, 0(!) -> JAL PC+4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0000;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01011000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JALR !, 0(ra) -> RET";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0000;
		tb_start_pred_info = 8'h66; // don't care
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01100000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JALR ra, 0(ra) -> RETL PC+4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0000;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01111000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JALR !, 0(!) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0001;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JALR ra, 0(!) -> JAL PC+2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0001;
		tb_start_pred_info = 8'h5; // don't care
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JALR !, 0(ra) -> RET";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0001;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01100000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JALR ra, 0(ra) -> RETL PC+2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0001;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01110000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JAL ! -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0010;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JAL ra -> JAL PC+4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0010;
		tb_start_pred_info = 8'h12; // don't care
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01011000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JAL ! bogus 0(ra) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0010;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JAL ra, bogus 0(ra) -> JAL PC+4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0010;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01011000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JAL ! -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0011;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JAL ra -> JAL PC+2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0011;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JAL !, bogus 0(ra) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0011;
		tb_start_pred_info = 8'h3F; // don't care
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JAL ra, bogus 0(ra) -> JAL PC+2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0011;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.J -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0100;
		tb_start_pred_info = 8'hAB; // don't care
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.J bogus ra, 0(!) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0100;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.J bogus !, 0(ra) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0100;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.J bogus ra, 0(ra) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0100;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JR 0(!) -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0101;
		tb_start_pred_info = 8'hAB; // don't care
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JR 0(!), bogus ra -> Jump";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0101;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JR 0(ra) -> RET";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0101;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01100000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "C.JR 0(ra) bogus ra -> RET";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0101;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b1;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b01100000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "LUI -> 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0110;
		tb_start_pred_info = 8'h76;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "AUIPC -> 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b0111;
		tb_start_pred_info = 8'h76;
		tb_is_link_ra = 1'b1;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "inv to N BEQ -> simple branch SN";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1000;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10001001;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "RET to T BLTU -> simple branch ST";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1110;
		tb_start_pred_info = 8'b01100000;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10111001;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "inv to BLT out of range -> complex branch";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1100;
		tb_start_pred_info = 8'h0;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b1;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b11010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "JAL PC+2 to C.BEQZ out of range -> complex branch";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1010;
		tb_start_pred_info = 8'b01010000;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b1;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b11010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple B to BGEU out of range -> complex branch";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1111;
		tb_start_pred_info = 8'b10010101;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b1;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b11010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "complex BGE -> complex branch";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1101;
		tb_start_pred_info = 8'b11100000;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b1;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b11100000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple ST+N BNE accuracy 8 -> simple WT B accuracy 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1001;
		tb_start_pred_info = 8'b10111000;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10100111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple WT+T BLTU accuracy 9 -> simple ST B accuracy 8";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1110;
		tb_start_pred_info = 8'b10101001;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10111000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple ST+N BGE accuracy 7 -> simple WT B accuracy 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1101;
		tb_start_pred_info = 8'b10110111;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10100000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple ST+T BLTU accuracy 6 -> simple ST B accuracy 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1110;
		tb_start_pred_info = 8'b10110110;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10110111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple WT+N BEQ accuracy 7 -> simple SN B accuracy 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1000;
		tb_start_pred_info = 8'b10100111;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple SN+N BNE accuracy 2 -> simple SN B accuracy 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1001;
		tb_start_pred_info = 8'b10000010;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10000011;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple SN+T C.BEQZ accuracy 11 -> simple WN B accuracy 10";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1010;
		tb_start_pred_info = 8'b10001011;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10011010;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple WN+T C.BNEZ accuracy 10 -> simple ST B accuracy 9";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1011;
		tb_start_pred_info = 8'b10011010;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10111001;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple WN+N BLT accuracy 7 -> simple SN B accuracy 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1100;
		tb_start_pred_info = 8'b10010111;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b0;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b10000111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple WT+N BGE accuracy 5 -> complex B";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1101;
		tb_start_pred_info = 8'b10100101;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b11010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple SN+T BLTU accuracy 6 -> complex B";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1110;
		tb_start_pred_info = 8'b10000110;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b1;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b11010000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple WT+N BGEU accuracy 0 -> complex B";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // inputs
		tb_op = 4'b1111;
		tb_start_pred_info = 8'b10100000;
		tb_is_link_ra = 1'b0;
		tb_is_ret_ra = 1'b0;
		tb_is_taken = 1'b0;
		tb_is_mispredict = 1'b1;
		tb_is_out_of_range = 1'b0;
	    // outputs

		@(negedge CLK);

		// outputs:

	    // inputs
	    // outputs
		expected_updated_pred_info = 8'b11010000;

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