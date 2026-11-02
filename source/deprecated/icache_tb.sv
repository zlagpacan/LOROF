/*
    Filename: icache_tb.sv
    Author: zlagpacan
    Description: Testbench for icache module. 
    Spec: LOROF/spec/design/icache.md
*/

`timescale 1ns/100ps

`include "system_types.vh"

module icache_tb #(
	parameter int unsigned ICACHE_SIZE = 2**13, // 8KB, 4KB page per way,
	parameter int unsigned ICACHE_BLOCK_SIZE = system_types::L1_BLOCK_SIZE, // 32B,
	parameter int unsigned ICACHE_ASSOC = 2, // 2x,
	parameter int unsigned LOG_ICACHE_ASSOC = $clog2(ICACHE_ASSOC), // 1b,
	parameter int unsigned ICACHE_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE), // 5b,
	parameter int unsigned ICACHE_NUM_SETS = ICACHE_SIZE / ICACHE_ASSOC / ICACHE_BLOCK_SIZE, // 128x,
	parameter int unsigned ICACHE_INDEX_WIDTH = $clog2(ICACHE_NUM_SETS), // 7b,
	parameter int unsigned ICACHE_TAG_WIDTH = system_types::PA_WIDTH - ICACHE_INDEX_WIDTH - ICACHE_BLOCK_OFFSET_WIDTH, // 34b - 7b - 5b = 22b,
	parameter int unsigned ICACHE_FETCH_WIDTH = 16, // 16B,
	parameter int unsigned ICACHE_FETCH_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE / ICACHE_FETCH_WIDTH) // 1b
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

    // req from core
	logic tb_core_req_valid;
	logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] tb_core_req_block_offset;
	logic [ICACHE_INDEX_WIDTH-1:0] tb_core_req_index;

    // resp to core
	logic [ICACHE_ASSOC-1:0] DUT_core_resp_valid_by_way, expected_core_resp_valid_by_way;
	logic [ICACHE_ASSOC-1:0][ICACHE_TAG_WIDTH-1:0] DUT_core_resp_tag_by_way, expected_core_resp_tag_by_way;
	logic [ICACHE_ASSOC-1:0][ICACHE_FETCH_WIDTH-1:0][7:0] DUT_core_resp_instr_16B_by_way, expected_core_resp_instr_16B_by_way;

    // resp feedback from core
	logic tb_core_resp_hit_valid;
	logic [LOG_ICACHE_ASSOC-1:0] tb_core_resp_hit_way;
	logic tb_core_resp_miss_valid;
	logic [ICACHE_TAG_WIDTH-1:0] tb_core_resp_miss_tag;

    // req to L2
	logic DUT_l2_req_valid, expected_l2_req_valid;
	logic [system_types::L1_BLOCK_ADDR_WIDTH-1:0] DUT_l2_req_PA29, expected_l2_req_PA29;
	logic tb_l2_req_ready;

    // resp from L2
	logic tb_l2_resp_valid;
	logic [system_types::L1_BLOCK_ADDR_WIDTH-1:0] tb_l2_resp_PA29;
	logic [system_types::L1_BLOCK_SIZE_BITS-1:0] tb_l2_resp_data256;

    // L2 snoop inv
	logic tb_l2_snoop_inv_valid;
	logic [system_types::L1_BLOCK_ADDR_WIDTH-1:0] tb_l2_snoop_inv_PA29;

    // ----------------------------------------------------------------
    // DUT instantiation:

	icache #(
		.ICACHE_SIZE(ICACHE_SIZE),
		.ICACHE_BLOCK_SIZE(ICACHE_BLOCK_SIZE),
		.ICACHE_ASSOC(ICACHE_ASSOC),
		.LOG_ICACHE_ASSOC(LOG_ICACHE_ASSOC),
		.ICACHE_BLOCK_OFFSET_WIDTH(ICACHE_BLOCK_OFFSET_WIDTH),
		.ICACHE_NUM_SETS(ICACHE_NUM_SETS),
		.ICACHE_INDEX_WIDTH(ICACHE_INDEX_WIDTH),
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
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 000000,0,0",
            "\n\t\t", "resp: ",
            "\n\t\t", "miss reg: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
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

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 000000,0,0",
            "\n\t\t", "resp: miss 000000,0,0",
            "\n\t\t", "miss reg: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
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

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 000000,0,0",
            "\n\t\t", "resp: miss 000000,0,0",
            "\n\t\t", "miss reg: miss 0,0 -> l2 req not ready"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b0;
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
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 000000,0,0",
            "\n\t\t", "resp: miss 000000,0,0",
            "\n\t\t", "miss reg: miss 0,0 -> l2 req"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
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
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 000000,0,0",
            "\n\t\t", "resp: miss 000000,0,0",
            "\n\t\t", "miss reg: miss 0,0 -> waiting l2 resp"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
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
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 000000,0,0",
            "\n\t\t", "resp: miss 000000,0,0",
            "\n\t\t", "miss reg: miss 0,0 -> garbage l2 resp"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = 29'h10203040;
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
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 000000,0,0",
            "\n\t\t", "resp: miss 000000,0,0",
            "\n\t\t", "miss reg: miss 0,0 -> l2 resp 7654,3210"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = {{8{16'h7654}}, {8{16'h3210}}};
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
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss return 000000,0,1",
            "\n\t\t", "resp: miss 000000,0,0",
            "\n\t\t", "miss reg: miss 0,0 -> miss return 3210, miss fill 3210"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = {{8{16'h0000}}, {8{16'h0000}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss return 000000,0,0",
            "\n\t\t", "resp: miss return 000000,0,1",
            "\n\t\t", "miss reg: miss 0,0 -> miss return 7654, miss fill 7654"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = {{8{16'h0000}}, {8{16'h0000}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h7654}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: hit 000000,0,1",
            "\n\t\t", "resp: miss return 000000,0,0",
            "\n\t\t", "miss reg: miss 0,0 -> delay cycle"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = {{8{16'h0000}}, {8{16'h0000}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: hit 000000,0,0",
            "\n\t\t", "resp: hit 000000,0,1",
            "\n\t\t", "miss reg: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = {{8{16'h0000}}, {8{16'h0000}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h7654}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 123456,0,1",
            "\n\t\t", "resp: hit 000000,0,0",
            "\n\t\t", "miss reg: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = {{8{16'h0000}}, {8{16'h0000}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 123456,0,1",
            "\n\t\t", "resp: miss 123456,0,1",
            "\n\t\t", "miss reg: "
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h123456;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = 29'h00000000;
		tb_l2_resp_data256 = {{8{16'h0000}}, {8{16'h0000}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h7654}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h000000, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 123456,0,1",
            "\n\t\t", "resp: miss 123456,0,1",
            "\n\t\t", "miss reg: miss 123456,0 -> l2 req / early resp fedc;ba98"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h123456;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = {22'h123456, 7'h00};
		tb_l2_resp_data256 = {{8{16'hfedc}}, {8{16'hba98}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h7654}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h123456, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 010203,1,0",
            "\n\t\t", "resp: miss 123456,0,1",
            "\n\t\t", "miss reg: miss 123456,0 -> miss return fedc, miss fill ba98"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h123456;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h123456, 7'h00};
		tb_l2_resp_data256 = {{8{16'hfedc}}, {8{16'hba98}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hfedc}}, {8{16'h7654}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h123456, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 010203,1,0",
            "\n\t\t", "resp: miss 010203,1,0",
            "\n\t\t", "miss reg: miss 123456,0 -> miss fill fedc"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h010203;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h123456, 7'h00};
		tb_l2_resp_data256 = {{8{16'hfedc}}, {8{16'hba98}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h0000}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h123456, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 010203,1,0",
            "\n\t\t", "resp: miss 010203,1,0",
            "\n\t\t", "miss reg: miss 010203,1 -> l2 req"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h010203;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h123456, 7'h00};
		tb_l2_resp_data256 = {{8{16'hfedc}}, {8{16'hba98}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h0000}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h010203, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 010203,1,0",
            "\n\t\t", "resp: miss 010203,1,0",
            "\n\t\t", "miss reg: miss 010203,1 -> l2 resp f0f0;e1e1"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h010203;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = {22'h010203, 7'h01};
		tb_l2_resp_data256 = {{8{16'hf0f0}}, {8{16'he1e1}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h0000}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h010203, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: hit hit 000000,0,0",
            "\n\t\t", "resp: miss 010203,1,0",
            "\n\t\t", "miss reg: miss 010203,1 -> miss fill e1e1, miss return e1e1"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h010203;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h010203, 7'h01};
		tb_l2_resp_data256 = {{8{16'hf0f0}}, {8{16'he1e1}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h010203};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'he1e1}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h010203, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: hit 000000,0,0",
            "\n\t\t", "miss reg: miss 010203,1 -> miss fill f0f0"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h000000;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h010203, 7'h01};
		tb_l2_resp_data256 = {{8{16'hf0f0}}, {8{16'he1e1}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h010203, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: miss 010203,1 -> delay cycle"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h010203, 7'h01};
		tb_l2_resp_data256 = {{8{16'hf0f0}}, {8{16'he1e1}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h010203, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: miss 789abc,0 -> l2 req"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h010203, 7'h01};
		tb_l2_resp_data256 = {{8{16'hf0f0}}, {8{16'he1e1}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = 29'h00000000;

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: miss 789abc,0 -> l2 resp, l2 snooped",
            "\n\t\t", "l2 snoop: 789abc,0"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b1;
		tb_l2_snoop_inv_PA29 = {22'h789abc, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: ",
            "\n\t\t", "l2 snoop: 010203,1"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b1;
		tb_l2_snoop_inv_PA29 = {22'h010203, 7'h01};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: blocked by snoop inv writing",
            "\n\t\t", "l2 snoop: 000000,0"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b1;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h010203};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: blocked by snoop inv writing"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: blocked by snoop inv writing"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h000000};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: blocked by snoop inv writing delay cycle"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b10;
		expected_core_resp_tag_by_way = {22'h123456, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: 789abc,0 -> l2 req"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b10;
		expected_core_resp_tag_by_way = {22'h123456, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 789abc,0,0",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: 789abc,0 -> l2 resp d2d2;c3c3"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b10;
		expected_core_resp_tag_by_way = {22'h123456, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'h3210}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: hit 123456,0,1",
            "\n\t\t", "resp: miss 789abc,0,0",
            "\n\t\t", "miss reg: 789abc,0 -> fill c3c3, return c3c3"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h789abc;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'hc3c3}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 010203,1,1",
            "\n\t\t", "resp: hit 123456,0,1",
            "\n\t\t", "miss reg: 789abc,0 -> fill d2d2"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b1;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h123456;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'hfedc}}, {8{16'hd2d2}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: hit 789abc,0,0",
            "\n\t\t", "resp: miss 010203,1,1",
            "\n\t\t", "miss reg: 789abc,0 -> delay cycle"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h010203;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'hf0f0}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h789abc, 7'h00};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 040506,1,1",
            "\n\t\t", "resp: hit 789abc,0,0",
            "\n\t\t", "miss reg: 010203,1 -> l2 req"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h010203;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b11;
		expected_core_resp_tag_by_way = {22'h123456, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'hba98}}, {8{16'hc3c3}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h010203, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 040506,1,1",
            "\n\t\t", "resp: miss 040506,1,1",
            "\n\t\t", "miss reg: 010203,1 -> l2 resp b4b4;a5a5"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h040506;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = {22'h010203, 7'h01};
		tb_l2_resp_data256 = {{8{16'hb4b4}}, {8{16'ha5a5}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'hf0f0}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h010203, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 040506,1,1",
            "\n\t\t", "resp: miss 040506,1,1",
            "\n\t\t", "miss reg: 040506,1 -> l2 req"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h040506;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h789abc, 7'h00};
		tb_l2_resp_data256 = {{8{16'hd2d2}}, {8{16'hc3c3}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'hf0f0}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b1;
		expected_l2_req_PA29 = {22'h040506, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss 040506,1,1",
            "\n\t\t", "resp: miss 040506,1,1",
            "\n\t\t", "miss reg: 040506,1 -> l2 resp 9696;8787"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b1;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b0;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b1;
		tb_core_resp_miss_tag = 22'h040506;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b1;
		tb_l2_resp_PA29 = {22'h040506, 7'h01};
		tb_l2_resp_data256 = {{8{16'h9696}}, {8{16'h8787}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b00;
		expected_core_resp_tag_by_way = {22'h000000, 22'h789abc};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'hf0f0}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h040506, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: miss return 040506,1,0",
            "\n\t\t", "resp: miss 040506,1,1",
            "\n\t\t", "miss reg: 040506,1 -> fill 8787, return 9696"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b1;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h01;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h040506;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h040506, 7'h01};
		tb_l2_resp_data256 = {{8{16'h9696}}, {8{16'h8787}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h040506};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h9696}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h040506, 7'h01};
	    // resp from L2
	    // L2 snoop inv

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\t", "req: ",
            "\n\t\t", "resp: miss return 040506,1,0",
            "\n\t\t", "miss reg: 040506,1 -> fill 8787, return 9696"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // req from core
		tb_core_req_valid = 1'b0;
		tb_core_req_block_offset = 1'b0;
		tb_core_req_index = 7'h00;
	    // resp to core
	    // resp feedback from core
		tb_core_resp_hit_valid = 1'b1;
		tb_core_resp_hit_way = 1'b0;
		tb_core_resp_miss_valid = 1'b0;
		tb_core_resp_miss_tag = 22'h040506;
	    // req to L2
		tb_l2_req_ready = 1'b1;
	    // resp from L2
		tb_l2_resp_valid = 1'b0;
		tb_l2_resp_PA29 = {22'h040506, 7'h01};
		tb_l2_resp_data256 = {{8{16'h9696}}, {8{16'h8787}}};
	    // L2 snoop inv
		tb_l2_snoop_inv_valid = 1'b0;
		tb_l2_snoop_inv_PA29 = {22'h000000, 7'h00};

		@(negedge CLK);

		// outputs:

	    // req from core
	    // resp to core
		expected_core_resp_valid_by_way = 2'b01;
		expected_core_resp_tag_by_way = {22'h000000, 22'h040506};
		expected_core_resp_instr_16B_by_way = {{8{16'h0000}}, {8{16'h8787}}};
	    // resp feedback from core
	    // req to L2
		expected_l2_req_valid = 1'b0;
		expected_l2_req_PA29 = {22'h040506, 7'h01};
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