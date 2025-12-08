/*
    Filename: operand_collector_tb.sv
    Author: zlagpacan
    Description: Testbench for operand_collector module. 
    Spec: LOROF/spec/design/operand_collector.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module operand_collector_tb #(
	parameter OC_ENTRIES = 3,
	parameter LOG_OC_ENTRIES = $clog2(OC_ENTRIES),
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

    // issue info
	logic tb_enq_valid;
	logic tb_enq_is_reg;
	logic tb_enq_is_bus_forward;
	logic tb_enq_is_fast_forward;
	logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] tb_enq_fast_forward_pipe;
	logic [LOG_PRF_BANK_COUNT-1:0] tb_enq_bank;

    // reg read data from PRF
	logic tb_reg_read_resp_valid;
	logic [31:0] tb_reg_read_resp_data;

    // bus forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] tb_bus_forward_data_by_bank;

    // fast forward data
	logic [FAST_FORWARD_PIPE_COUNT-1:0] tb_fast_forward_data_valid_by_pipe;
	logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] tb_fast_forward_data_by_pipe;

    // operand collection control
	logic DUT_operand_collected, expected_operand_collected;
	logic tb_operand_collected_ack;
	logic [31:0] DUT_operand_data, expected_operand_data;
	logic tb_operand_data_ack;

    // ----------------------------------------------------------------
    // DUT instantiation:

	operand_collector #(
		.OC_ENTRIES(OC_ENTRIES),
		.LOG_OC_ENTRIES(LOG_OC_ENTRIES),
		.FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT),
		.LOG_FAST_FORWARD_PIPE_COUNT(LOG_FAST_FORWARD_PIPE_COUNT)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // issue info
		.enq_valid(tb_enq_valid),
		.enq_is_reg(tb_enq_is_reg),
		.enq_is_bus_forward(tb_enq_is_bus_forward),
		.enq_is_fast_forward(tb_enq_is_fast_forward),
		.enq_fast_forward_pipe(tb_enq_fast_forward_pipe),
		.enq_bank(tb_enq_bank),

	    // reg read data from PRF
		.reg_read_resp_valid(tb_reg_read_resp_valid),
		.reg_read_resp_data(tb_reg_read_resp_data),

	    // bus forward data from PRF
		.bus_forward_data_by_bank(tb_bus_forward_data_by_bank),

	    // fast forward data
		.fast_forward_data_valid_by_pipe(tb_fast_forward_data_valid_by_pipe),
		.fast_forward_data_by_pipe(tb_fast_forward_data_by_pipe),

	    // operand collection control
		.operand_collected(DUT_operand_collected),
		.operand_collected_ack(tb_operand_collected_ack),
		.operand_data(DUT_operand_data),
		.operand_data_ack(tb_operand_data_ack)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_operand_collected !== DUT_operand_collected) begin
			$display("TB ERROR: expected_operand_collected (%h) != DUT_operand_collected (%h)",
				expected_operand_collected, DUT_operand_collected);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_operand_data !== DUT_operand_data) begin
			$display("TB ERROR: expected_operand_data (%h) != DUT_operand_data (%h)",
				expected_operand_data, DUT_operand_data);
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
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'h00000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'h00000000;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i} : enq reg0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b1;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, reg0} : enq reg1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b1;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'h00000000;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, reg1, reg0:c} : enq reg2, resp reg0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b1;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b1;
		tb_reg_read_resp_data = 32'hf0f0f0f0;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{reg2, reg1, reg0:c} : no ack";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'hf0f0f0f0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{reg2, reg1, reg0:c} : notif ack reg0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b1;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'hf0f0f0f0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{reg2, reg1, reg0:ca} : data ack reg0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'hf0f0f0f0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, reg2, reg1} : enq busfwd3, reg1 resp, notif ack reg1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b1;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h3;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b1;
		tb_reg_read_resp_data = 32'he1e1e1e1;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b1;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{busfwd3, reg2, reg1:ca} : busfwd3 bus, reg2 resp, notif ack reg2, data ack reg1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b1;
		tb_reg_read_resp_data = 32'hd2d2d2d2;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hc3c3c3c3,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b1;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'he1e1e1e1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, busfwd3:c, reg2:ca} : enq fastfwd4, notif ack busfwd3, data ack reg2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b1;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b1;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'hd2d2d2d2;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, fastfwd4, busfwd3:ca} : enq fastfwd5, data ack busfwd3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b1;
		tb_enq_fast_forward_pipe = 2'h1;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'hc3c3c3c3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{fastfwd5, fastfwd4, busfwd3:ca} : fastfwd5 resp";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b1;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0010;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'ha5a5a5a5,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, fastfwd5:c, fastfwd4} : enq fastfwd4p2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b1;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1110;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{fastfwd4p2, fastfwd5:c, fastfwd4} : fastfwd4[p2] resp, fastfwd4 notif ack";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1111;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hb4b4b4b4
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b1;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{fastfwd4p2:c, fastfwd5:c, fastfwd4:ca} : fastfwd5 notif ack, fastfwd4 data ack";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1111;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b1;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'hb4b4b4b4;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, fastfwd4p2:c, fastfwd5:ca} : enq zero, fastfwdp24 notif ack, fastfwd5 data ack";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b1;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b1111;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b1;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'ha5a5a5a5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, zero:c, fastfwd5:ca} : zero notif ack, fastfwdp24 data ack";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'hb4b4b4b4;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, zero:ca} : zero data ack";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b1;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b1;
		expected_operand_data = 32'h00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i} : none";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // issue info
		tb_enq_valid = 1'b0;
		tb_enq_is_reg = 1'b0;
		tb_enq_is_bus_forward = 1'b0;
		tb_enq_is_fast_forward = 1'b0;
		tb_enq_fast_forward_pipe = 2'h0;
		tb_enq_bank = 2'h0;
	    // reg read data from PRF
		tb_reg_read_resp_valid = 1'b0;
		tb_reg_read_resp_data = 32'hdeadbeef;
	    // bus forward data from PRF
		tb_bus_forward_data_by_bank = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // fast forward data
		tb_fast_forward_data_valid_by_pipe = 4'b0000;
		tb_fast_forward_data_by_pipe = {
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef,
            32'hdeadbeef
        };
	    // operand collection control
		tb_operand_collected_ack = 1'b0;
		tb_operand_data_ack = 1'b0;

		@(negedge CLK);

		// outputs:

	    // issue info
	    // reg read data from PRF
	    // bus forward data from PRF
	    // fast forward data
	    // operand collection control
		expected_operand_collected = 1'b0;
		expected_operand_data = 32'ha5a5a5a5; // don't care

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