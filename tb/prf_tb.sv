/*
    Filename: prf_tb.sv
    Author: zlagpacan
    Description: Testbench for prf module. 
    Spec: LOROF/spec/design/prf.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf_tb ();

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


    // reg read req by read requester
	logic [PRF_RR_COUNT-1:0] tb_reg_read_req_valid_by_rr;
	logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_reg_read_req_PR_by_rr;

    // reg read info by read requestor
	logic [PRF_RR_COUNT-1:0] DUT_reg_read_ack_by_rr, expected_reg_read_ack_by_rr;
	logic [PRF_RR_COUNT-1:0] DUT_reg_read_port_by_rr, expected_reg_read_port_by_rr;

    // reg read data by bank
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] DUT_reg_read_data_by_bank_by_port, expected_reg_read_data_by_bank_by_port;

    // writeback data by write requestor
	logic [PRF_WR_COUNT-1:0] tb_WB_valid_by_wr;
	logic [PRF_WR_COUNT-1:0][31:0] tb_WB_data_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_WB_PR_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0] tb_WB_ROB_index_by_wr;

    // writeback backpressure by write requestor
	logic [PRF_WR_COUNT-1:0] DUT_WB_ready_by_wr, expected_WB_ready_by_wr;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] DUT_WB_bus_valid_by_bank, expected_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][31:0] DUT_WB_bus_data_by_bank, expected_WB_bus_data_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] DUT_WB_bus_upper_PR_by_bank, expected_WB_bus_upper_PR_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] DUT_WB_bus_ROB_index_by_bank, expected_WB_bus_ROB_index_by_bank;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] DUT_forward_data_by_bank, expected_forward_data_by_bank;

    // ----------------------------------------------------------------
    // DUT instantiation:

	prf DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // reg read req by read requester
		.reg_read_req_valid_by_rr(tb_reg_read_req_valid_by_rr),
		.reg_read_req_PR_by_rr(tb_reg_read_req_PR_by_rr),

	    // reg read info by read requestor
		.reg_read_ack_by_rr(DUT_reg_read_ack_by_rr),
		.reg_read_port_by_rr(DUT_reg_read_port_by_rr),

	    // reg read data by bank
		.reg_read_data_by_bank_by_port(DUT_reg_read_data_by_bank_by_port),

	    // writeback data by write requestor
		.WB_valid_by_wr(tb_WB_valid_by_wr),
		.WB_data_by_wr(tb_WB_data_by_wr),
		.WB_PR_by_wr(tb_WB_PR_by_wr),
		.WB_ROB_index_by_wr(tb_WB_ROB_index_by_wr),

	    // writeback backpressure by write requestor
		.WB_ready_by_wr(DUT_WB_ready_by_wr),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(DUT_WB_bus_valid_by_bank),
		.WB_bus_data_by_bank(DUT_WB_bus_data_by_bank),
		.WB_bus_upper_PR_by_bank(DUT_WB_bus_upper_PR_by_bank),
		.WB_bus_ROB_index_by_bank(DUT_WB_bus_ROB_index_by_bank),

	    // forward data from PRF
		.forward_data_by_bank(DUT_forward_data_by_bank)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_reg_read_ack_by_rr !== DUT_reg_read_ack_by_rr) begin
			$display("TB ERROR: expected_reg_read_ack_by_rr (%h) != DUT_reg_read_ack_by_rr (%h)",
				expected_reg_read_ack_by_rr, DUT_reg_read_ack_by_rr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_reg_read_port_by_rr !== DUT_reg_read_port_by_rr) begin
			$display("TB ERROR: expected_reg_read_port_by_rr (%h) != DUT_reg_read_port_by_rr (%h)",
				expected_reg_read_port_by_rr, DUT_reg_read_port_by_rr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_reg_read_data_by_bank_by_port !== DUT_reg_read_data_by_bank_by_port) begin
			$display("TB ERROR: expected_reg_read_data_by_bank_by_port (%h) != DUT_reg_read_data_by_bank_by_port (%h)",
				expected_reg_read_data_by_bank_by_port, DUT_reg_read_data_by_bank_by_port);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_ready_by_wr !== DUT_WB_ready_by_wr) begin
			$display("TB ERROR: expected_WB_ready_by_wr (%h) != DUT_WB_ready_by_wr (%h)",
				expected_WB_ready_by_wr, DUT_WB_ready_by_wr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_bus_valid_by_bank !== DUT_WB_bus_valid_by_bank) begin
			$display("TB ERROR: expected_WB_bus_valid_by_bank (%h) != DUT_WB_bus_valid_by_bank (%h)",
				expected_WB_bus_valid_by_bank, DUT_WB_bus_valid_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_bus_data_by_bank !== DUT_WB_bus_data_by_bank) begin
			$display("TB ERROR: expected_WB_bus_data_by_bank (%h) != DUT_WB_bus_data_by_bank (%h)",
				expected_WB_bus_data_by_bank, DUT_WB_bus_data_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_bus_upper_PR_by_bank !== DUT_WB_bus_upper_PR_by_bank) begin
			$display("TB ERROR: expected_WB_bus_upper_PR_by_bank (%h) != DUT_WB_bus_upper_PR_by_bank (%h)",
				expected_WB_bus_upper_PR_by_bank, DUT_WB_bus_upper_PR_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_WB_bus_ROB_index_by_bank !== DUT_WB_bus_ROB_index_by_bank) begin
			$display("TB ERROR: expected_WB_bus_ROB_index_by_bank (%h) != DUT_WB_bus_ROB_index_by_bank (%h)",
				expected_WB_bus_ROB_index_by_bank, DUT_WB_bus_ROB_index_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_forward_data_by_bank !== DUT_forward_data_by_bank) begin
			$display("TB ERROR: expected_forward_data_by_bank (%h) != DUT_forward_data_by_bank (%h)",
				expected_forward_data_by_bank, DUT_forward_data_by_bank);
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
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = '0;
		tb_WB_data_by_wr = '0;
		tb_WB_PR_by_wr = '0;
		tb_WB_ROB_index_by_wr = '0;
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(posedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = '0;
		expected_reg_read_port_by_rr = '0;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = '0;
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = '1;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = '0;
		expected_WB_bus_data_by_bank = '0;
		expected_WB_bus_upper_PR_by_bank = '0;
		expected_WB_bus_ROB_index_by_bank = '0;
	    // forward data from PRF
		expected_forward_data_by_bank = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = '0;
		tb_WB_data_by_wr = '0;
		tb_WB_PR_by_wr = '0;
		tb_WB_ROB_index_by_wr = '0;
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(posedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = '0;
		expected_reg_read_port_by_rr = '0;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = '0;
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = '1;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = '0;
		expected_WB_bus_data_by_bank = '0;
		expected_WB_bus_upper_PR_by_bank = '0;
		expected_WB_bus_ROB_index_by_bank = '0;
	    // forward data from PRF
		expected_forward_data_by_bank = '0;

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK);

		// inputs
		sub_test_case = "default";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = '0;
		tb_WB_data_by_wr = '0;
		tb_WB_PR_by_wr = '0;
		tb_WB_ROB_index_by_wr = '0;
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = '0;
		expected_reg_read_port_by_rr = '0;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = '0;
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = '1;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = '0;
		expected_WB_bus_data_by_bank = '0;
		expected_WB_bus_upper_PR_by_bank = '0;
		expected_WB_bus_ROB_index_by_bank = '0;
	    // forward data from PRF
		expected_forward_data_by_bank = '0;

		check_outputs();

        // ------------------------------------------------------------
        // finish:
        @(posedge CLK);
        
        test_case = "finish";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        @(posedge CLK);

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