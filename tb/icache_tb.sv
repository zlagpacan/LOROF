/*
    Filename: icache_tb.sv
    Author: zlagpacan
    Description: Testbench for icache module. 
    Spec: LOROF/spec/design/icache.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

parameter ICACHE_NUM_SETS = 2**7;
parameter ICACHE_INDEX_WIDTH = $clog2(ICACHE_NUM_SETS);
parameter ICACHE_BLOCK_SIZE = 32;
parameter ICACHE_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE);
parameter ICACHE_TAG_WIDTH = 22;
parameter ICACHE_FETCH_WIDTH = 16;
parameter ICACHE_FETCH_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE / ICACHE_FETCH_WIDTH);

module icache_tb ();

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

    // req from core
	logic tb_core_req_valid;
	logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] tb_core_req_block_offset;
	logic [ICACHE_INDEX_WIDTH-1:0] tb_core_req_index;

    // resp to core
	logic [1:0] DUT_core_resp_valid_by_way, expected_core_resp_valid_by_way;
	logic [1:0][ICACHE_TAG_WIDTH-1:0] DUT_core_resp_tag_by_way, expected_core_resp_tag_by_way;
	logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0] DUT_core_resp_instr_16B_by_way, expected_core_resp_instr_16B_by_way;

    // resp feedback from core
	logic tb_core_resp_hit_valid;
	logic tb_core_resp_hit_way;
	logic tb_core_resp_miss_valid;
	logic [ICACHE_TAG_WIDTH-1:0] tb_core_resp_miss_tag;

    // req to L2
	logic DUT_l2_req_valid, expected_l2_req_valid;
	logic [L1_BLOCK_ADDR_WIDTH-1:0] DUT_l2_req_PA29, expected_l2_req_PA29;
	logic tb_l2_req_ready;

    // resp from L2
	logic tb_l2_resp_valid;
	logic [L1_BLOCK_ADDR_WIDTH-1:0] tb_l2_resp_PA29;
	logic [L1_BLOCK_SIZE_BITS-1:0] tb_l2_resp_data256;

    // L2 snoop inv
	logic tb_l2_snoop_inv_valid;
	logic [L1_BLOCK_ADDR_WIDTH-1:0] tb_l2_snoop_inv_PA29;

    // ----------------------------------------------------------------
    // DUT instantiation:

	icache #(
		.ICACHE_NUM_SETS(ICACHE_NUM_SETS),
		.ICACHE_INDEX_WIDTH(ICACHE_INDEX_WIDTH),
		.ICACHE_BLOCK_SIZE(ICACHE_BLOCK_SIZE),
		.ICACHE_BLOCK_OFFSET_WIDTH(ICACHE_BLOCK_OFFSET_WIDTH),
		.ICACHE_TAG_WIDTH(ICACHE_TAG_WIDTH),
		.ICACHE_FETCH_WIDTH(ICACHE_FETCH_WIDTH),
		.ICACHE_FETCH_BLOCK_OFFSET_WIDTH(ICACHE_FETCH_BLOCK_OFFSET_WIDTH)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // req from core
		.core_req_valid(tb_core_req_valid),
		.core_req_block_offset(tb_core_req_block_offset),
		.core_req_index(tb_core_req_index),

	    // resp to core
		.core_resp_valid_by_way(DUT_core_resp_valid_by_way),
		.core_resp_tag_by_way(DUT_core_resp_tag_by_way),
		.core_resp_instr_16B_by_way(DUT_core_resp_instr_16B_by_way),

	    // resp feedback from core
		.core_resp_hit_valid(tb_core_resp_hit_valid),
		.core_resp_hit_way(tb_core_resp_hit_way),
		.core_resp_miss_valid(tb_core_resp_miss_valid),
		.core_resp_miss_tag(tb_core_resp_miss_tag),

	    // req to L2
		.l2_req_valid(DUT_l2_req_valid),
		.l2_req_PA29(DUT_l2_req_PA29),
		.l2_req_ready(tb_l2_req_ready),

	    // resp from L2
		.l2_resp_valid(tb_l2_resp_valid),
		.l2_resp_PA29(tb_l2_resp_PA29),
		.l2_resp_data256(tb_l2_resp_data256),

	    // L2 snoop inv
		.l2_snoop_inv_valid(tb_l2_snoop_inv_valid),
		.l2_snoop_inv_PA29(tb_l2_snoop_inv_PA29)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_core_resp_valid_by_way !== DUT_core_resp_valid_by_way) begin
			$display("TB ERROR: expected_core_resp_valid_by_way (%h) != DUT_core_resp_valid_by_way (%h)",
				expected_core_resp_valid_by_way, DUT_core_resp_valid_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_core_resp_tag_by_way !== DUT_core_resp_tag_by_way) begin
			$display("TB ERROR: expected_core_resp_tag_by_way (%h) != DUT_core_resp_tag_by_way (%h)",
				expected_core_resp_tag_by_way, DUT_core_resp_tag_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_core_resp_instr_16B_by_way !== DUT_core_resp_instr_16B_by_way) begin
			$display("TB ERROR: expected_core_resp_instr_16B_by_way (%h) != DUT_core_resp_instr_16B_by_way (%h)",
				expected_core_resp_instr_16B_by_way, DUT_core_resp_instr_16B_by_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_req_valid !== DUT_l2_req_valid) begin
			$display("TB ERROR: expected_l2_req_valid (%h) != DUT_l2_req_valid (%h)",
				expected_l2_req_valid, DUT_l2_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_req_PA29 !== DUT_l2_req_PA29) begin
			$display("TB ERROR: expected_l2_req_PA29 (%h) != DUT_l2_req_PA29 (%h)",
				expected_l2_req_PA29, DUT_l2_req_PA29);
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
	    // req from core
		tb_core_req_valid = 1'b0;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {128'h00000000000000000000000000000000, 128'h00000000000000000000000000000000};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = 29'h00000000;
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b0;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {128'h00000000000000000000000000000000, 128'h00000000000000000000000000000000};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = 29'h00000000;
	    // resp from L2
	    // L2 snoop inv

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
	    // req from core
		tb_core_req_valid = 1'b0;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {128'h00000000000000000000000000000000, 128'h00000000000000000000000000000000};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = 29'h00000000;
	    // resp from L2
	    // L2 snoop inv

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