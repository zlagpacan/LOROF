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

	prf #(.USE_BRAM(1'b0)) DUT (
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
        // fill up writes:
        test_case = "fill up writes";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK);

		// inputs
		sub_test_case = "no conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0001111;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFFFF0000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h03,
			7'h02,
			7'h01,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'hFC,
			7'hFD,
			7'hFE,
			7'hFF
		};
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

		@(posedge CLK);

		// inputs
		sub_test_case = "no conflicts 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1110000;
		tb_WB_data_by_wr = {
			32'hF9F90606,
			32'hFAFA0505,
			32'hFBFB0404,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFFFF0000
		};
		tb_WB_PR_by_wr = {
			7'h06,
			7'h05,
			7'h04,
			7'h03,
			7'h02,
			7'h01,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'hF9,
			7'hFA,
			7'hFB,
			7'hFC,
			7'hFD,
			7'hFE,
			7'hFF
		};
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
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_data_by_bank = {
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFFFF0000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hFC,
			7'hFD,
			7'hFE,
			7'hFF
		};
	    // forward data from PRF
		expected_forward_data_by_bank = '0;

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hF2F20D0D,
			32'hF3F30C0C,
			32'hF4F40B0B,
			32'hF5F50A0A,
			32'hF6F60909,
			32'hF7F70808,
			32'hF8F80707
		};
		tb_WB_PR_by_wr = {
			7'h0D,
			7'h0C,
			7'h0B,
			7'h0A,
			7'h09,
			7'h08,
			7'h07
		};
		tb_WB_ROB_index_by_wr = {
			7'hF2,
			7'hF3,
			7'hF4,
			7'hF5,
			7'hF6,
			7'hF7,
			7'hF8
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0111;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'hF9F90606,
			32'hFAFA0505,
			32'hFBFB0404
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h01,
			5'h01,
			5'h01
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'hF9,
			7'hFA,
			7'hFB
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFFFF0000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hEBEB1414,
			32'hECEC1313,
			32'hEDED1212,
			32'hEEEE1111,
			32'hEFEF1010,
			32'hF0F00F0F,
			32'hF1F10E0E
		};
		tb_WB_PR_by_wr = {
			7'h14,
			7'h13,
			7'h12,
			7'h11,
			7'h10,
			7'h0F,
			7'h0E
		};
		tb_WB_ROB_index_by_wr = {
			7'hEB,
			7'hEC,
			7'hED,
			7'hEE,
			7'hEF,
			7'hF0,
			7'hF1
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b0011110;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_data_by_bank = {
			32'hf4f40b0b,
			32'hf5f50a0a,
			32'hf6f60909,
			32'hf7f70808
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h02,
			5'h02,
			5'h02,
			5'h02
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hF4,
			7'hF5,
			7'hF6,
			7'hF7
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'hf9f90606,
			32'hfafa0505,
			32'hfbfb0404
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hEBEB1414,
			32'hECEC1313,
			32'hE7E71818,
			32'hE8E81717,
			32'hE9E91616,
			32'hEAEA1515,
			32'hF1F10E0E
		};
		tb_WB_PR_by_wr = {
			7'h14,
			7'h13,
			7'h18,
			7'h17,
			7'h16,
			7'h15,
			7'h0E
		};
		tb_WB_ROB_index_by_wr = {
			7'hEB,
			7'hEC,
			7'hE7,
			7'hE8,
			7'hE9,
			7'hEA,
			7'hF1
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1110010;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_data_by_bank = {
			32'hf0f00f0f,
			32'heded1212,
			32'hf2f20d0d,
			32'hf3f30c0c
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h03,
			5'h04,
			5'h03,
			5'h03
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hF0,
			7'hED,
			7'hF2,
			7'hF3
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'hf4f40b0b,
			32'hf5f50a0a,
			32'hf6f60909,
			32'hf7f70808
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hE3E31C1C,
			32'hE4E41B1B,
			32'hE5E51A1A,
			32'hE8E81717,
			32'hE9E91616,
			32'hE6E61919,
			32'hF1F10E0E
		};
		tb_WB_PR_by_wr = {
			7'h1C,
			7'h1B,
			7'h1A,
			7'h17,
			7'h16,
			7'h19,
			7'h0E
		};
		tb_WB_ROB_index_by_wr = {
			7'hE3,
			7'hE4,
			7'hE5,
			7'hE8,
			7'hE9,
			7'hE6,
			7'hF1
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b0011001;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1011;
		expected_WB_bus_data_by_bank = {
			32'hf8f80707,
			32'h00000000,
			32'heeee1111,
			32'he7e71818
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h01,
			5'h00,
			5'h04,
			5'h06
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hF8,
			7'h00,
			7'hEE,
			7'hE7
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'hf0f00f0f,
			32'heded1212,
			32'hf2f20d0d,
			32'hf3f30c0c
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hE3E31C1C,
			32'hE4E41B1B,
			32'hE0E01F1F,
			32'hE1E11E1E,
			32'hE9E91616,
			32'hE6E61919,
			32'hE2E21D1D
		};
		tb_WB_PR_by_wr = {
			7'h1C,
			7'h1B,
			7'h1F,
			7'h1E,
			7'h16,
			7'h19,
			7'h1D
		};
		tb_WB_ROB_index_by_wr = {
			7'hE3,
			7'hE4,
			7'hE0,
			7'hE1,
			7'hE9,
			7'hE6,
			7'hE2
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b0110110;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_data_by_bank = {
			32'hecec1313,
			32'he5e51a1a,
			32'heaea1515,
			32'hefef1010
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h04,
			5'h06,
			5'h05,
			5'h04
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hEC,
			7'hE5,
			7'hEA,
			7'hEF
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'hf8f80707,
			32'h00000000,
			32'heeee1111,
			32'he7e71818
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hE3E31C1C,
			32'hDCDC2323,
			32'hDDDD2222,
			32'hE1E11E1E,
			32'hDEDE2121,
			32'hDFDF2020,
			32'hE2E21D1D
		};
		tb_WB_PR_by_wr = {
			7'h1C,
			7'h23,
			7'h22,
			7'h1E,
			7'h21,
			7'h20,
			7'h1D
		};
		tb_WB_ROB_index_by_wr = {
			7'hE3,
			7'hDC,
			7'hDD,
			7'hE1,
			7'hDE,
			7'hDF,
			7'hE2
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1010110;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_data_by_bank = {
			32'he0e01f1f,
			32'he9e91616,
			32'he6e61919,
			32'hebeb1414
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h07,
			5'h05,
			5'h06,
			5'h05
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hE0,
			7'hE9,
			7'hE6,
			7'hEB
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'hecec1313,
			32'he5e51a1a,
			32'heaea1515,
			32'hefef1010
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 6 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0101001;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'hDCDC2323,
			32'h00000000,
			32'hE1E11E1E,
			32'h00000000,
			32'h00000000,
			32'hE2E21D1D
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h23,
			7'h00,
			7'h1E,
			7'h00,
			7'h00,
			7'h1D
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'hDC,
			7'h00,
			7'hE1,
			7'h00,
			7'h00,
			7'hE2
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1011111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_data_by_bank = {
			32'he8e81717,
			32'hf1f10e0e,
			32'hdede2121,
			32'hdfdf2020
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h05,
			5'h03,
			5'h08,
			5'h08
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hE8,
			7'hF1,
			7'hDE,
			7'hDF
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'he0e01f1f,
			32'he9e91616,
			32'he6e61919,
			32'hebeb1414
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 7 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0100000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'hDCDC2323,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h23,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'hDC,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_data_by_bank = {
			32'he4e41b1b,
			32'hdddd2222,
			32'he2e21d1d,
			32'he3e31c1c
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h06,
			5'h08,
			5'h07,
			5'h07
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hE4,
			7'hDD,
			7'hE2,
			7'hE3
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'he8e81717,
			32'hf1f10e0e,
			32'hdede2121,
			32'hdfdf2020
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 8 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1100;
		expected_WB_bus_data_by_bank = {
			32'hdcdc2323,
			32'he1e11e1e,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h08,
			5'h07,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'hDC,
			7'hE1,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'he4e41b1b,
			32'hdddd2222,
			32'he2e21d1d,
			32'he3e31c1c
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 9 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'hdcdc2323,
			32'he1e11e1e,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts A (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = '0;
		tb_reg_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
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
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

        // ------------------------------------------------------------
        // reads:
        test_case = "reads";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK);

		// inputs
		sub_test_case = "no conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b00000011111111;
		tb_reg_read_req_PR_by_rr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h07,
			7'h06,
			7'h05,
			7'h04,
			7'h03,
			7'h02,
			7'h01,
			7'h00
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b00000000000000;
		expected_reg_read_port_by_rr = 14'b00000000000000;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "no conflicts 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b11111100000011;
		tb_reg_read_req_PR_by_rr = {
			7'h0F,
			7'h0E,
			7'h0D,
			7'h0C,
			7'h0B,
			7'h0A,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h09,
			7'h08
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b00000011111111;
		expected_reg_read_port_by_rr = 14'b00000000001111;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hF8F80707,
			32'hFDFD0202,
			32'hF9F90606,
			32'hFEFE0101,
			32'hFAFA0505,
			32'hFFFF0000,
			32'hFBFB0404
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "no conflicts 2 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b00000000000000;
		tb_reg_read_req_PR_by_rr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b11111100000011;
		expected_reg_read_port_by_rr = 14'b00001100000011;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hF4F40B0B,
			32'hF0F00F0F,
			32'hF5F50A0A,
			32'hF1F10E0E,
			32'hF6F60909,
			32'hF2F20D0D,
			32'hF7F70808,
			32'hF3F30C0C
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "no conflicts 3 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b00000000000000;
		tb_reg_read_req_PR_by_rr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b00000000000000;
		expected_reg_read_port_by_rr = 14'b00000000000000;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b11111111111111;
		tb_reg_read_req_PR_by_rr = {
			7'h10,
			7'h11,
			7'h12,
			7'h13,
			7'h14,
			7'h15,
			7'h16,
			7'h17,
			7'h18,
			7'h19,
			7'h1A,
			7'h1B,
			7'h1C,
			7'h1D
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b00000000000000;
		expected_reg_read_port_by_rr = 14'b00000000000000;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'hFFFF0000,
			32'hFFFF0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b11111111000000;
		tb_reg_read_req_PR_by_rr = {
			7'h1E,
			7'h1F,
			7'h20,
			7'h21,
			7'h22,
			7'h23,
			7'h00,
			7'h01,
			7'h18,
			7'h19,
			7'h1A,
			7'h1B,
			7'h1C,
			7'h1D
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b11111111000000;
		expected_reg_read_port_by_rr = 14'b00001111000000;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hE8E81717,
			32'hECEC1313,
			32'hE9E91616,
			32'hEDED1212,
			32'hEAEA1515,
			32'hEEEE1111,
			32'hEBEB1414,
			32'hEFEF1010
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b11000011111100;
		tb_reg_read_req_PR_by_rr = {
			7'h02,
			7'h03,
			7'h20,
			7'h21,
			7'h22,
			7'h23,
			7'h04,
			7'h05,
			7'h06,
			7'h07,
			7'h08,
			7'h09,
			7'h1C,
			7'h1D
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b11000011111100;
		expected_reg_read_port_by_rr = 14'b11000000110000;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'he0e01f1f,
			32'he4e41b1b,
			32'he1e11e1e,
			32'he5e51a1a,
			32'he6e61919,
			32'hfefe0101,
			32'he7e71818,
			32'hffff0000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b00001100111111;
		tb_reg_read_req_PR_by_rr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h10,
			7'h11,
			7'h00,
			7'h00,
			7'h12,
			7'h13,
			7'h14,
			7'h15,
			7'h16,
			7'h17
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b00001100111111;
		expected_reg_read_port_by_rr = 14'b00000000110011;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hf8f80707,
			32'hdcdc2323,
			32'hf9f90606,
			32'hdddd2222,
			32'he2e21d1d,
			32'hf6f60909,
			32'he3e31c1c,
			32'hf7f70808
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 4 (cooling down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b00000000000000;
		tb_reg_read_req_PR_by_rr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b11111100000011;
		expected_reg_read_port_by_rr = 14'b11001100000000;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'he8e81717,
			32'hfdfd0202,
			32'he9e91616,
			32'heeee1111,
			32'hdede2121,
			32'hefef1010,
			32'hdfdf2020
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK);

		// inputs
		sub_test_case = "conflicts 5 (cooling down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_reg_read_req_valid_by_rr = 14'b00000000000000;
		tb_reg_read_req_PR_by_rr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_reg_read_ack_by_rr = 14'b00000011111100;
		expected_reg_read_port_by_rr = 14'b00000000001100;
	    // reg read data by bank
		expected_reg_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hecec1313,
			32'hfdfd0202,
			32'heded1212,
			32'heaea1515,
			32'hfafa0505,
			32'hebeb1414,
			32'hfbfb0404
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_WB_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

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