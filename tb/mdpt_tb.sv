/*
    Filename: mdpt_tb.sv
    Author: zlagpacan
    Description: Testbench for mdpt module. 
    Spec: LOROF/spec/design/mdpt.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module mdpt_tb ();

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
	logic [31:0] tb_full_PC_REQ;
	logic [ASID_WIDTH-1:0] tb_ASID_REQ;

    // RESP stage
	logic [MDPT_ENTRIES_PER_BLOCK-1:0] DUT_dep_pred_by_instr_RESP, expected_dep_pred_by_instr_RESP;

    // Dep Update 0 stage
	logic tb_dep_update0_valid;
	logic [31:0] tb_dep_update0_start_full_PC;
	logic [ASID_WIDTH-1:0] tb_dep_update0_ASID;
	logic tb_dep_update0_dep_truth;

    // ----------------------------------------------------------------
    // DUT instantiation:

	mdpt DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // REQ stage
		.valid_REQ(tb_valid_REQ),
		.full_PC_REQ(tb_full_PC_REQ),
		.ASID_REQ(tb_ASID_REQ),

	    // RESP stage
		.dep_pred_by_instr_RESP(DUT_dep_pred_by_instr_RESP),

	    // Dep Update 0 stage
		.dep_update0_valid(tb_dep_update0_valid),
		.dep_update0_start_full_PC(tb_dep_update0_start_full_PC),
		.dep_update0_ASID(tb_dep_update0_ASID),
		.dep_update0_dep_truth(tb_dep_update0_dep_truth)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_dep_pred_by_instr_RESP !== DUT_dep_pred_by_instr_RESP) begin
			$display("TB ERROR: expected_dep_pred_by_instr_RESP (%h) != DUT_dep_pred_by_instr_RESP (%h)",
				expected_dep_pred_by_instr_RESP, DUT_dep_pred_by_instr_RESP);
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
		tb_full_PC_REQ = {
            19'h0,
            9'h0,
            3'h0,
            1'b0
        };
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Dep Update 0 stage
		tb_dep_update0_valid = 1'b0;
		tb_dep_update0_start_full_PC = {
            19'h0,
            9'h0,
            3'h0,
            1'b0
        };
		tb_dep_update0_ASID = 9'h0;
		tb_dep_update0_dep_truth = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_dep_pred_by_instr_RESP = 8'b00000000;
	    // Dep Update 0 stage

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
            19'h0,
            9'h0,
            3'h0,
            1'b0
        };
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Dep Update 0 stage
		tb_dep_update0_valid = 1'b0;
		tb_dep_update0_start_full_PC = {
            19'h0,
            9'h0,
            3'h0,
            1'b0
        };
		tb_dep_update0_ASID = 9'h0;
		tb_dep_update0_dep_truth = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_dep_pred_by_instr_RESP = 8'b00000000;
	    // Dep Update 0 stage

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
		tb_full_PC_REQ = {
            19'h0,
            9'h0,
            3'h0,
            1'b0
        };
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Dep Update 0 stage
		tb_dep_update0_valid = 1'b0;
		tb_dep_update0_start_full_PC = {
            19'h0,
            9'h0,
            3'h0,
            1'b0
        };
		tb_dep_update0_ASID = 9'h0;
		tb_dep_update0_dep_truth = 1'b0;

		@(negedge CLK);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_dep_pred_by_instr_RESP = 8'b00000000;
	    // Dep Update 0 stage

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