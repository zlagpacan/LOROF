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

	parameter PR_COUNT = 128;
	parameter PRF_BANK_COUNT = 4;
	parameter PRF_RR_COUNT = 11;
	parameter PRF_WR_COUNT = 7;

    // reg read req by read requester
	logic [PRF_RR_COUNT-1:0] tb_read_req_valid_by_rr;
	logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_read_req_PR_by_rr;

    // reg read info by read requestor
	logic [PRF_RR_COUNT-1:0] DUT_read_resp_ack_by_rr, expected_read_resp_ack_by_rr;
	logic [PRF_RR_COUNT-1:0] DUT_read_resp_port_by_rr, expected_read_resp_port_by_rr;

    // reg read data by bank
	logic [PRF_BANK_COUNT-1:0][1:0][31:0] DUT_read_data_by_bank_by_port, expected_read_data_by_bank_by_port;

    // writeback data by write requestor
	logic [PRF_WR_COUNT-1:0] tb_WB_valid_by_wr;
	logic [PRF_WR_COUNT-1:0] tb_WB_send_complete_by_wr;
	logic [PRF_WR_COUNT-1:0][31:0] tb_WB_data_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_WB_PR_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0] tb_WB_ROB_index_by_wr;

    // writeback backpressure by write requestor
	logic [PRF_WR_COUNT-1:0] DUT_WB_ready_by_wr, expected_WB_ready_by_wr;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] DUT_WB_bus_valid_by_bank, expected_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] DUT_WB_bus_upper_PR_by_bank, expected_WB_bus_upper_PR_by_bank;

    // forward data from PRF
	logic [PRF_BANK_COUNT-1:0][31:0] DUT_forward_data_bus_by_bank, expected_forward_data_bus_by_bank;

	// complete bus by bank
	logic [PRF_BANK_COUNT-1:0] DUT_complete_bus_valid_by_bank, expected_complete_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] DUT_complete_bus_ROB_index_by_bank, expected_complete_bus_ROB_index_by_bank;

    // ----------------------------------------------------------------
    // DUT instantiation:

	prf #(
		.PR_COUNT(128),
		.PRF_BANK_COUNT(4),
		.PRF_RR_COUNT(11),
		.PRF_WR_COUNT(7),
		.USE_BRAM(1'b0)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // reg read req by read requester
		.read_req_valid_by_rr(tb_read_req_valid_by_rr),
		.read_req_PR_by_rr(tb_read_req_PR_by_rr),

	    // reg read info by read requestor
		.read_resp_ack_by_rr(DUT_read_resp_ack_by_rr),
		.read_resp_port_by_rr(DUT_read_resp_port_by_rr),

	    // reg read data by bank
		.read_data_by_bank_by_port(DUT_read_data_by_bank_by_port),

	    // writeback data by write requestor
		.WB_valid_by_wr(tb_WB_valid_by_wr),
		.WB_send_complete_by_wr(tb_WB_send_complete_by_wr),
		.WB_data_by_wr(tb_WB_data_by_wr),
		.WB_PR_by_wr(tb_WB_PR_by_wr),
		.WB_ROB_index_by_wr(tb_WB_ROB_index_by_wr),

	    // writeback backpressure by write requestor
		.WB_ready_by_wr(DUT_WB_ready_by_wr),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(DUT_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(DUT_WB_bus_upper_PR_by_bank),

	    // forward data from PRF
		.forward_data_bus_by_bank(DUT_forward_data_bus_by_bank),

		// complete bus by bank
		.complete_bus_valid_by_bank(DUT_complete_bus_valid_by_bank),
		.complete_bus_ROB_index_by_bank(DUT_complete_bus_ROB_index_by_bank)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_resp_ack_by_rr !== DUT_read_resp_ack_by_rr) begin
			$display("TB ERROR: expected_read_resp_ack_by_rr (%h) != DUT_read_resp_ack_by_rr (%h)",
				expected_read_resp_ack_by_rr, DUT_read_resp_ack_by_rr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_port_by_rr !== DUT_read_resp_port_by_rr) begin
			$display("TB ERROR: expected_read_resp_port_by_rr (%h) != DUT_read_resp_port_by_rr (%h)",
				expected_read_resp_port_by_rr, DUT_read_resp_port_by_rr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_data_by_bank_by_port !== DUT_read_data_by_bank_by_port) begin
			$display("TB ERROR: expected_read_data_by_bank_by_port (%h) != DUT_read_data_by_bank_by_port (%h)",
				expected_read_data_by_bank_by_port, DUT_read_data_by_bank_by_port);
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

		if (expected_WB_bus_upper_PR_by_bank !== DUT_WB_bus_upper_PR_by_bank) begin
			$display("TB ERROR: expected_WB_bus_upper_PR_by_bank (%h) != DUT_WB_bus_upper_PR_by_bank (%h)",
				expected_WB_bus_upper_PR_by_bank, DUT_WB_bus_upper_PR_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_forward_data_bus_by_bank !== DUT_forward_data_bus_by_bank) begin
			$display("TB ERROR: expected_forward_data_bus_by_bank (%h) != DUT_forward_data_bus_by_bank (%h)",
				expected_forward_data_bus_by_bank, DUT_forward_data_bus_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_complete_bus_valid_by_bank !== DUT_complete_bus_valid_by_bank) begin
			$display("TB ERROR: expected_complete_bus_valid_by_bank (%h) != DUT_complete_bus_valid_by_bank (%h)",
				expected_complete_bus_valid_by_bank, DUT_complete_bus_valid_by_bank);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_complete_bus_ROB_index_by_bank !== DUT_complete_bus_ROB_index_by_bank) begin
			$display("TB ERROR: expected_complete_bus_ROB_index_by_bank (%h) != DUT_complete_bus_ROB_index_by_bank (%h)",
				expected_complete_bus_ROB_index_by_bank, DUT_complete_bus_ROB_index_by_bank);
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
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = '0;
		tb_WB_send_complete_by_wr = '0;
		tb_WB_data_by_wr = '0;
		tb_WB_PR_by_wr = '0;
		tb_WB_ROB_index_by_wr = '0;
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = '0;
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = '1;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = '0;
		expected_WB_bus_upper_PR_by_bank = '0;
		// complete bus by bank
		expected_complete_bus_valid_by_bank = '0;
		expected_complete_bus_ROB_index_by_bank = '0;
	    // forward data from PRF
		expected_forward_data_bus_by_bank = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = '0;
		tb_WB_send_complete_by_wr = '0;
		tb_WB_data_by_wr = '0;
		tb_WB_PR_by_wr = '0;
		tb_WB_ROB_index_by_wr = '0;
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = '0;
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = '1;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = '0;
		expected_WB_bus_upper_PR_by_bank = '0;
		// complete bus by bank
		expected_complete_bus_valid_by_bank = '0;
		expected_complete_bus_ROB_index_by_bank = '0;
	    // forward data from PRF
		expected_forward_data_bus_by_bank = '0;

		check_outputs();

        // ------------------------------------------------------------
        // fill up writes:
        test_case = "fill up writes";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "no conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0001111;
		tb_WB_send_complete_by_wr = 7'b0001010;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = '0;
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = '1;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = '0;
		expected_WB_bus_upper_PR_by_bank = '0;
		// complete bus by bank
		expected_complete_bus_valid_by_bank = '0;
		expected_complete_bus_ROB_index_by_bank = '0;
	    // forward data from PRF
		expected_forward_data_bus_by_bank = '0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "no conflicts 1 (write to PR 0 from conflicts 1 is complete but no WB)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1110000;
		tb_WB_send_complete_by_wr = 7'b1010000;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = '0;
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = '1;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1110;
		// expected_WB_bus_data_by_bank = {
		// 	32'hFCFC0303,
		// 	32'hFDFD0202,
		// 	32'hFEFE0101,
		// 	32'hFFFF0000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		// complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b1010;
		expected_complete_bus_ROB_index_by_bank = {
			7'hFC,
			7'hFD,
			7'hFE,
			7'hFF
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = '0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_send_complete_by_wr = 7'b1010101;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0111;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'hF9F90606,
		// 	32'hFAFA0505,
		// 	32'hFBFB0404
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h01,
			5'h01,
			5'h01
		};
		expected_complete_bus_valid_by_bank = 4'b0101;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'hF9,
			7'hFA,
			7'hFB
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFFFF0000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_send_complete_by_wr = 7'b1111111;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1101001;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		// expected_WB_bus_data_by_bank = {
		// 	32'hF8F80707,
		// 	32'hF5F50A0A,
		// 	32'hF2F20D0D,
		// 	32'hF3F30C0C
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h01,
			5'h02,
			5'h03,
			5'h03
		};
		expected_complete_bus_valid_by_bank = 4'b1010;
		expected_complete_bus_ROB_index_by_bank = {
			7'hF8,
			7'hF5,
			7'hF2,
			7'hF3
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'hf9f90606,
			32'hfafa0505,
			32'hfbfb0404
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_send_complete_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hE7E71818,
			32'hE8E81717,
			32'hEDED1212,
			32'hE9E91616,
			32'hEFEF1010,
			32'hF0F00F0F,
			32'hEAEA1515
		};
		tb_WB_PR_by_wr = {
			7'h18,
			7'h17,
			7'h12,
			7'h16,
			7'h10,
			7'h0F,
			7'h15
		};
		tb_WB_ROB_index_by_wr = {
			7'hE7,
			7'hE8,
			7'hED,
			7'hE9,
			7'hEF,
			7'hF0,
			7'hEA
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1010101;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		// expected_WB_bus_data_by_bank = {
		// 	32'hf4f40b0b,
		// 	32'hf1f10e0e,
		// 	32'hf6f60909,
		// 	32'hebeb1414
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h02,
			5'h03,
			5'h02,
			5'h05
		};
		expected_complete_bus_valid_by_bank = 4'b1111;
		expected_complete_bus_ROB_index_by_bank = {
			7'hf4,
			7'hf1,
			7'hf6,
			7'heb
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'hF8F80707,
			32'hF5F50A0A,
			32'hF2F20D0D,
			32'hF3F30C0C
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_send_complete_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hE3E31C1C,
			32'hE8E81717,
			32'hE4E41B1B,
			32'hE9E91616,
			32'hE5E51A1A,
			32'hF0F00F0F,
			32'hE6E61919
		};
		tb_WB_PR_by_wr = {
			7'h1C,
			7'h17,
			7'h1B,
			7'h16,
			7'h1A,
			7'h0F,
			7'h19
		};
		tb_WB_ROB_index_by_wr = {
			7'hE3,
			7'hE8,
			7'hE4,
			7'hE9,
			7'hE5,
			7'hF0,
			7'hE6
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b0111010;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		// expected_WB_bus_data_by_bank = {
		// 	32'hecec1313,
		// 	32'heded1212,
		// 	32'heeee1111,
		// 	32'hf7f70808
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h04,
			5'h04,
			5'h04,
			5'h02
		};
		expected_complete_bus_valid_by_bank = 4'b1110;
		expected_complete_bus_ROB_index_by_bank = {
			7'hec,
			7'hed,
			7'hee,
			7'hf7
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'hf4f40b0b,
			32'hf1f10e0e,
			32'hf6f60909,
			32'hebeb1414
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_send_complete_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hE3E31C1C,
			32'hDFDF2020,
			32'hE0E01F1F,
			32'hE1E11E1E,
			32'hE5E51A1A,
			32'hE2E21D1D,
			32'hE6E61919
		};
		tb_WB_PR_by_wr = {
			7'h1C,
			7'h20,
			7'h1F,
			7'h1E,
			7'h1A,
			7'h1D,
			7'h19
		};
		tb_WB_ROB_index_by_wr = {
			7'hE3,
			7'hDF,
			7'hE0,
			7'hE1,
			7'hE5,
			7'hE2,
			7'hE6
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b0001111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		// expected_WB_bus_data_by_bank = {
		// 	32'hf0f00f0f,
		// 	32'he9e91616,
		// 	32'heaea1515,
		// 	32'hefef1010
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h03,
			5'h05,
			5'h05,
			5'h04
		};
		expected_complete_bus_valid_by_bank = 4'b1111;
		expected_complete_bus_ROB_index_by_bank = {
			7'hf0,
			7'he9,
			7'hea,
			7'hef
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'hecec1313,
			32'heded1212,
			32'heeee1111,
			32'hf7f70808
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b1111111;
		tb_WB_send_complete_by_wr = 7'b1111111;
		tb_WB_data_by_wr = {
			32'hE3E31C1C,
			32'hDFDF2020,
			32'hE0E01F1F,
			32'hDBDB2424,
			32'hDCDC2323,
			32'hDDDD2222,
			32'hDEDE2121
		};
		tb_WB_PR_by_wr = {
			7'h1C,
			7'h20,
			7'h1F,
			7'h24,
			7'h23,
			7'h22,
			7'h21
		};
		tb_WB_ROB_index_by_wr = {
			7'hE3,
			7'hDF,
			7'hE0,
			7'hDB,
			7'hDC,
			7'hDD,
			7'hDE
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1010110;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		// expected_WB_bus_data_by_bank = {
		// 	32'he4e41b1b,
		// 	32'he5e51a1a,
		// 	32'he2e21d1d,
		// 	32'he7e71818
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h06,
			5'h06,
			5'h07,
			5'h06
		};
		expected_complete_bus_valid_by_bank = 4'b1111;
		expected_complete_bus_ROB_index_by_bank = {
			7'he4,
			7'he5,
			7'he2,
			7'he7
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'hf0f00f0f,
			32'he9e91616,
			32'heaea1515,
			32'hefef1010
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 6 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0101001;
		tb_WB_send_complete_by_wr = 7'b0101001;
		tb_WB_data_by_wr = {
			32'h00000000,
			32'hDFDF2020,
			32'h00000000,
			32'hDBDB2424,
			32'h00000000,
			32'h00000000,
			32'hDEDE2121
		};
		tb_WB_PR_by_wr = {
			7'h00,
			7'h20,
			7'h00,
			7'h24,
			7'h00,
			7'h00,
			7'h21
		};
		tb_WB_ROB_index_by_wr = {
			7'h00,
			7'hDF,
			7'h00,
			7'hDB,
			7'h00,
			7'h00,
			7'hDE
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1101001;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		// expected_WB_bus_data_by_bank = {
		// 	32'he8e81717,
		// 	32'he1e11e1e,
		// 	32'he6e61919,
		// 	32'he3e31c1c
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h05,
			5'h07,
			5'h06,
			5'h07
		};
		expected_complete_bus_valid_by_bank = 4'b1111;
		expected_complete_bus_ROB_index_by_bank = {
			7'he8,
			7'he1,
			7'he6,
			7'he3
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'he4e41b1b,
			32'he5e51a1a,
			32'he2e21d1d,
			32'he7e71818
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 7 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1001111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		// expected_WB_bus_data_by_bank = {
		// 	32'hdcdc2323,
		// 	32'hdddd2222,
		// 	32'hdede2121,
		// 	32'hdbdb2424
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h08,
			5'h08,
			5'h08,
			5'h09
		};
		expected_complete_bus_valid_by_bank = 4'b1111;
		expected_complete_bus_ROB_index_by_bank = {
			7'hdc,
			7'hdd,
			7'hde,
			7'hdb
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'he8e81717,
			32'he1e11e1e,
			32'he6e61919,
			32'he3e31c1c
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 8 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1001;
		// expected_WB_bus_data_by_bank = {
		// 	32'he0e01f1f,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'hdfdf2020
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h07,
			5'h00,
			5'h00,
			5'h08
		};
		expected_complete_bus_valid_by_bank = 4'b1001;
		expected_complete_bus_ROB_index_by_bank = {
			7'he0,
			7'h00,
			7'h00,
			7'hdf
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'hdcdc2323,
			32'hdddd2222,
			32'hdede2121,
			32'hdbdb2424
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 9 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'he0e01f1f,
			32'h00000000,
			32'h00000000,
			32'hdfdf2020
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts A (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = '0;
		tb_read_req_PR_by_rr = '0;
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = '0;
		expected_read_resp_port_by_rr = '0;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
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

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "no conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00011111111;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "no conflicts 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b11100011111;
		tb_read_req_PR_by_rr = {
			7'h0A,
			7'h09,
			7'h08,
			7'h00,
			7'h00,
			7'h00,
			7'h0F,
			7'h0E,
			7'h0D,
			7'h0C,
			7'h0B
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00011111111;
		expected_read_resp_port_by_rr = 11'b00011110000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hf8f80707,
			32'hfcfc0303,
			32'hF9F90606,
			32'hFDFD0202,
			32'hFAFA0505,
			32'hFEFE0101,
			32'hFBFB0404,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "no conflicts 2 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b11100011111;
		expected_read_resp_port_by_rr = 11'b00000011110;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hF0F00F0F,
			32'hF4F40B0B,
			32'hF1F10E0E,
			32'hF5F50A0A,
			32'hF2F20D0D,
			32'hF6F60909,
			32'hF3F30C0C,
			32'hF7F70808
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "no conflicts 3 (winding down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b11111111111;
		tb_read_req_PR_by_rr = {
			7'h1A,
			7'h19,
			7'h18,
			7'h17,
			7'h16,
			7'h15,
			7'h14,
			7'h13,
			7'h12,
			7'h11,
			7'h10
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hFCFC0303,
			32'hFCFC0303,
			32'hFDFD0202,
			32'hFDFD0202,
			32'hFEFE0101,
			32'hFEFE0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00011111111;
		tb_read_req_PR_by_rr = {
			7'h1A,
			7'h19,
			7'h18,
			7'h22,
			7'h21,
			7'h20,
			7'h1F,
			7'h1E,
			7'h1D,
			7'h1C,
			7'h1B
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00011111111;
		expected_read_resp_port_by_rr = 11'b00011110000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
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
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b11111110001;
		tb_read_req_PR_by_rr = {
			7'h05,
			7'h04,
			7'h03,
			7'h02,
			7'h01,
			7'h00,
			7'h24,
			7'h1E,
			7'h1D,
			7'h1C,
			7'h23
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b11111110001;
		expected_read_resp_port_by_rr = 11'b11100010000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'he0e01f1f,
			32'he4e41b1b,
			32'he5e51a1a,
			32'hdddd2222,
			32'he6e61919,
			32'hdede2121,
			32'he7e71818,
			32'hdfdf2020
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b11110001111;
		tb_read_req_PR_by_rr = {
			7'h0D,
			7'h0C,
			7'h0B,
			7'h0A,
			7'h01,
			7'h00,
			7'h24,
			7'h09,
			7'h08,
			7'h07,
			7'h06
		};
	    // reg read info by read requestor
	    // reg read data by bank
	    // writeback data by write requestor
		tb_WB_valid_by_wr = 7'b0000000;
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b11110001111;
		expected_read_resp_port_by_rr = 11'b00010000111;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hdcdc2323,
			32'hfcfc0303,
			32'hfdfd0202,
			32'he1e11e1e,
			32'he2e21d1d,
			32'hfafa0505,
			32'he3e31c1c,
			32'hfbfb0404
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 4 (cooling down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00111011111;
		expected_read_resp_port_by_rr = 11'b00111010000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hf4f40b0b,
			32'hf8f80707,
			32'hf5f50a0a,
			32'hf9f90606,
			32'hfefe0101,
			32'hf6f60909,
			32'hdbdb2424,
			32'hf7f70808
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "conflicts 5 (cooling down)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b11000100000;
		expected_read_resp_port_by_rr = 11'b01000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hfcfc0303,
			32'hfdfd0202,
			32'hfdfd0202,
			32'hfefe0101,
			32'hf2f20d0d,
			32'hf3f30c0c,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

        // ------------------------------------------------------------
        // PR 0 write check:
        test_case = "PR 0 write check";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "PR 0 write req's";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_valid_by_wr = 7'b1001001;
		tb_WB_send_complete_by_wr = 7'b1001001;
		tb_WB_data_by_wr = {
			32'h96969696,
			32'h00000000,
			32'h00000000,
			32'hC3C3C3C3,
			32'h00000000,
			32'h00000000,
			32'hF0F0F0F0
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
			7'h96,
			7'h00,
			7'h00,
			7'hC3,
			7'h00,
			7'h00,
			7'hF0
		};
	    // writeback backpressure by write requestor
	    // writeback bus by bank
	    // forward data from PRF

		@(negedge CLK);

		// outputs:

	    // reg read req by read requester
	    // reg read info by read requestor
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hfcfc0303,
			32'hfdfd0202,
			32'hfdfd0202,
			32'hfefe0101,
			32'hfefe0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "PR 0 write resp 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hfcfc0303,
			32'hfdfd0202,
			32'hfdfd0202,
			32'hfefe0101,
			32'hfefe0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b0110111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0001;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'hF0
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "PR 0 write resp 3, forward 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hfcfc0303,
			32'hfdfd0202,
			32'hfdfd0202,
			32'hfefe0101,
			32'hfefe0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b0111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0001;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'hC3
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'hF0F0F0F0
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "PR 0 write resp 6, forward 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hfcfc0303,
			32'hfdfd0202,
			32'hfdfd0202,
			32'hfefe0101,
			32'hfefe0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0001;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h96
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'hC3C3C3C3
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "PR 0 forward 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hfcfc0303,
			32'hfdfd0202,
			32'hfdfd0202,
			32'hfefe0101,
			32'hfefe0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h96969696
		};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "PR 0 writes winded down";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // reg read req by read requester
		tb_read_req_valid_by_rr = 11'b00000000000;
		tb_read_req_PR_by_rr = {
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
		tb_WB_send_complete_by_wr = 7'b0000000;
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
		expected_read_resp_ack_by_rr = 11'b00000000000;
		expected_read_resp_port_by_rr = 11'b00000000000;
	    // reg read data by bank
		expected_read_data_by_bank_by_port = {
			32'hfcfc0303,
			32'hfcfc0303,
			32'hfdfd0202,
			32'hfdfd0202,
			32'hfefe0101,
			32'hfefe0101,
			32'h00000000,
			32'h00000000
		};
	    // writeback data by write requestor
	    // writeback backpressure by write requestor
		expected_WB_ready_by_wr = 7'b1111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		// expected_WB_bus_data_by_bank = {
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000,
		// 	32'h00000000
		// };
		expected_WB_bus_upper_PR_by_bank = {
			5'h00,
			5'h00,
			5'h00,
			5'h00
		};
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
			7'h00,
			7'h00,
			7'h00,
			7'h00
		};
	    // forward data from PRF
		expected_forward_data_bus_by_bank = {
			32'h00000000,
			32'h00000000,
			32'h00000000,
			32'h00000000
		};

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