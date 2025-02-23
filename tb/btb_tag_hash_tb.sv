/*
    Filename: btb_tag_hash_tb.sv
    Author: zlagpacan
    Description: Testbench for btb_tag_hash module. 
    Spec: LOROF/spec/design/btb_tag_hash.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb_tag_hash_tb ();

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
	logic [31:0] tb_PC;
	logic [8:0] tb_ASID;
	logic [BTB_TAG_WIDTH-1:0] DUT_tag, expected_tag;

    // ----------------------------------------------------------------
    // DUT instantiation:

	btb_tag_hash DUT (
		.PC(tb_PC),
		.ASID(tb_ASID),
		.tag(DUT_tag)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_tag !== DUT_tag) begin
			$display("TB ERROR: expected_tag (%h) != DUT_tag (%h)",
				expected_tag, DUT_tag);
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
		tb_PC = '0;
		tb_ASID = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_tag = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = '0;
		tb_ASID = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_tag = '0;

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "0 ^ 0 ^ 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b000000, // upper tag bits
            6'b000000, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b000000 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "0 ^ 0 ^ 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b000000, // upper tag bits
            6'b111111, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b000000 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b111111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "0 ^ 1 ^ 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b111111, // upper tag bits
            6'b000000, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b000000 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b111111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "0 ^ 1 ^ 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b111111, // upper tag bits
            6'b111111, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b000000 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1 ^ 0 ^ 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b000000, // upper tag bits
            6'b000000, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b111111 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b111111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1 ^ 0 ^ 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b111111, // upper tag bits
            6'b000000, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b111111 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1 ^ 1 ^ 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b000000, // upper tag bits
            6'b111111, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b111111 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "1 ^ 1 ^ 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_PC = {
            8'h0, // untouched bits
            6'b111111, // upper tag bits
            6'b111111, // lower tag bits
            8'h0, // set index
            3'h0, // within-block index
            1'b0 // 2B offset
        };
		tb_ASID = {
            3'h0, // untouched bits
            6'b111111 // tag bits
        };

		@(negedge CLK);

		// outputs:

		expected_tag = 6'b111111;

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