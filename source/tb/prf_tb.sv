/*
    Filename: prf_tb.sv
    Author: zlagpacan
    Description: Testbench for prf module. 
    Spec: LOROF/spec/design/prf.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module prf_tb #(
	parameter PR_COUNT = 128,
	parameter LOG_PR_COUNT = $clog2(PR_COUNT),
	parameter PRF_BANK_COUNT = 4,
	parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT),
	parameter PRF_RR_COUNT = 9,
	parameter PRF_RR_INPUT_BUFFER_SIZE = 2,
	parameter PRF_WR_COUNT = 8,
	parameter PRF_WR_INPUT_BUFFER_SIZE = 2
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


    // read req info by read requestor
	logic [PRF_RR_COUNT-1:0] tb_read_req_valid_by_rr;
	logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_read_req_PR_by_rr;

    // read req feedback by read requestor
	logic [PRF_RR_COUNT-1:0] DUT_read_req_ready_by_rr, expected_read_req_ready_by_rr;

    // read resp info by read requestor
	logic [PRF_RR_COUNT-1:0] DUT_read_resp_valid_by_rr, expected_read_resp_valid_by_rr;
	logic [PRF_RR_COUNT-1:0][31:0] DUT_read_resp_data_by_rr, expected_read_resp_data_by_rr;

    // writeback info by write requestor
	logic [PRF_WR_COUNT-1:0] tb_WB_valid_by_wr;
	logic [PRF_WR_COUNT-1:0] tb_WB_send_complete_by_wr;
	logic [PRF_WR_COUNT-1:0][31:0] tb_WB_data_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_WB_PR_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0] tb_WB_ROB_index_by_wr;

    // writeback feedback by write requestor
	logic [PRF_WR_COUNT-1:0] DUT_WB_ready_by_wr, expected_WB_ready_by_wr;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] DUT_WB_bus_valid_by_bank, expected_WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] DUT_WB_bus_upper_PR_by_bank, expected_WB_bus_upper_PR_by_bank;

    // forward data by bank
	logic [PRF_BANK_COUNT-1:0][31:0] DUT_forward_data_bus_by_bank, expected_forward_data_bus_by_bank;

    // complete bus by bank
	logic [PRF_BANK_COUNT-1:0] DUT_complete_bus_valid_by_bank, expected_complete_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0] DUT_complete_bus_ROB_index_by_bank, expected_complete_bus_ROB_index_by_bank;

    // ----------------------------------------------------------------
    // DUT instantiation:

	prf #(
		.PR_COUNT(PR_COUNT),
		.LOG_PR_COUNT(LOG_PR_COUNT),
		.PRF_BANK_COUNT(PRF_BANK_COUNT),
		.LOG_PRF_BANK_COUNT(LOG_PRF_BANK_COUNT),
		.PRF_RR_COUNT(PRF_RR_COUNT),
		.PRF_RR_INPUT_BUFFER_SIZE(PRF_RR_INPUT_BUFFER_SIZE),
		.PRF_WR_COUNT(PRF_WR_COUNT),
		.PRF_WR_INPUT_BUFFER_SIZE(PRF_WR_INPUT_BUFFER_SIZE)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // read req info by read requestor
		.read_req_valid_by_rr(tb_read_req_valid_by_rr),
		.read_req_PR_by_rr(tb_read_req_PR_by_rr),

	    // read req feedback by read requestor
		.read_req_ready_by_rr(DUT_read_req_ready_by_rr),

	    // read resp info by read requestor
		.read_resp_valid_by_rr(DUT_read_resp_valid_by_rr),
		.read_resp_data_by_rr(DUT_read_resp_data_by_rr),

	    // writeback info by write requestor
		.WB_valid_by_wr(tb_WB_valid_by_wr),
		.WB_send_complete_by_wr(tb_WB_send_complete_by_wr),
		.WB_data_by_wr(tb_WB_data_by_wr),
		.WB_PR_by_wr(tb_WB_PR_by_wr),
		.WB_ROB_index_by_wr(tb_WB_ROB_index_by_wr),

	    // writeback feedback by write requestor
		.WB_ready_by_wr(DUT_WB_ready_by_wr),

	    // writeback bus by bank
		.WB_bus_valid_by_bank(DUT_WB_bus_valid_by_bank),
		.WB_bus_upper_PR_by_bank(DUT_WB_bus_upper_PR_by_bank),

	    // forward data by bank
		.forward_data_bus_by_bank(DUT_forward_data_bus_by_bank),

	    // complete bus by bank
		.complete_bus_valid_by_bank(DUT_complete_bus_valid_by_bank),
		.complete_bus_ROB_index_by_bank(DUT_complete_bus_ROB_index_by_bank)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_req_ready_by_rr !== DUT_read_req_ready_by_rr) begin
			$display("TB ERROR: expected_read_req_ready_by_rr (%h) != DUT_read_req_ready_by_rr (%h)",
				expected_read_req_ready_by_rr, DUT_read_req_ready_by_rr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_valid_by_rr !== DUT_read_resp_valid_by_rr) begin
			$display("TB ERROR: expected_read_resp_valid_by_rr (%h) != DUT_read_resp_valid_by_rr (%h)",
				expected_read_resp_valid_by_rr, DUT_read_resp_valid_by_rr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_read_resp_data_by_rr !== DUT_read_resp_data_by_rr) begin
			$display("TB ERROR: expected_read_resp_data_by_rr (%h) != DUT_read_resp_data_by_rr (%h)",
				expected_read_resp_data_by_rr, DUT_read_resp_data_by_rr);
            for (int i = 8; i >= 0; i--) begin
                $display("        h%h vs h%h",
                    expected_read_resp_data_by_rr[i], DUT_read_resp_data_by_rr[i]);
            end
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
            for (int i = 3; i >= 0; i--) begin
                $display("        h%h vs h%h",
                    expected_WB_bus_upper_PR_by_bank[i], DUT_WB_bus_upper_PR_by_bank[i]);
            end
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_forward_data_bus_by_bank !== DUT_forward_data_bus_by_bank) begin
			$display("TB ERROR: expected_forward_data_bus_by_bank (%h) != DUT_forward_data_bus_by_bank (%h)",
				expected_forward_data_bus_by_bank, DUT_forward_data_bus_by_bank);
            for (int i = 3; i >= 0; i--) begin
                $display("        h%h vs h%h",
                    expected_forward_data_bus_by_bank[i], DUT_forward_data_bus_by_bank[i]);
            end
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
            for (int i = 3; i >= 0; i--) begin
                $display("        h%h vs h%h",
                    expected_complete_bus_ROB_index_by_bank[i], DUT_complete_bus_ROB_index_by_bank[i]);
            end
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
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b00000000;
		tb_WB_data_by_wr = {
            32'h00000000,
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
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b00000000;
		tb_WB_data_by_wr = {
            32'h00000000,
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
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

        // ------------------------------------------------------------
        // simple write chain:
        test_case = "simple write chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b11111111;
		tb_WB_send_complete_by_wr = 8'b11101110;
		tb_WB_data_by_wr = {
            32'h7F7F0000,
            32'h78780707,
            32'h79790606,
            32'h7A7A0505,
            32'h7B7B0404,
            32'h7C7C0303,
            32'h7D7D0202,
            32'h7E7E0101
        };
		tb_WB_PR_by_wr = {
            7'h00,
            7'h07,
            7'h06,
            7'h05,
            7'h04,
            7'h03,
            7'h02,
            7'h01
        };
		tb_WB_ROB_index_by_wr = {
            7'h7F,
            7'h78,
            7'h79,
            7'h7A,
            7'h7B,
            7'h7C,
            7'h7D,
            7'h7E
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b11111111;
		tb_WB_send_complete_by_wr = 8'b01110111;
		tb_WB_data_by_wr = {
            32'h70700F0F,
            32'h71710E0E,
            32'h72720D0D,
            32'h73730C0C,
            32'h77770808,
            32'h76760909,
            32'h75750A0A,
            32'h74740B0B
        };
		tb_WB_PR_by_wr = {
            7'h0F,
            7'h0E,
            7'h0D,
            7'h0C,
            7'h08,
            7'h09,
            7'h0A,
            7'h0B
        };
		tb_WB_ROB_index_by_wr = {
            7'h70,
            7'h71,
            7'h72,
            7'h73,
            7'h77,
            7'h76,
            7'h75,
            7'h74
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h01
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b1101;
		expected_complete_bus_ROB_index_by_bank = {
            7'h7c,
            7'h7d,
            7'h7e,
            7'h7b
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b11111111;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h6A6A1515,
            32'h6B6B1414,
            32'h6C6C1313,
            32'h6D6D1212,
            32'h6E6E1111,
            32'h6F6F1010,
            32'h69691616,
            32'h68681717
        };
		tb_WB_PR_by_wr = {
            7'h15,
            7'h14,
            7'h13,
            7'h12,
            7'h11,
            7'h10,
            7'h16,
            7'h17
        };
		tb_WB_ROB_index_by_wr = {
            7'h6A,
            7'h6B,
            7'h6C,
            7'h6D,
            7'h6E,
            7'h6F,
            7'h69,
            7'h68
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111; // still send WB bus for PRF0 write (ready_table and backend dq's, iq's, and pipe's are fine with this)
		expected_WB_bus_upper_PR_by_bank = {
            5'h01,
            5'h01,
            5'h01,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h7c7c0303,
            32'h7d7d0202,
            32'h7e7e0101,
            32'h7b7b0404
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b1101;
		expected_complete_bus_ROB_index_by_bank = {
            7'h78,
            7'h79,
            7'h7a,
            7'h7f
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b00000000;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11101000;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_upper_PR_by_bank = {
            5'h03,
            5'h03,
            5'h03,
            5'h02
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h78780707,
            32'h79790606,
            32'h7a7a0505,
            32'h7f7f0000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0110;
		expected_complete_bus_ROB_index_by_bank = {
            7'h70,
            7'h71,
            7'h72,
            7'h77
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b00000000;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111011;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_upper_PR_by_bank = {
            5'h02,
            5'h02,
            5'h05,
            5'h03
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h70700f0f,
            32'h71710e0e,
            32'h72720d0d,
            32'h77770808
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b1101;
		expected_complete_bus_ROB_index_by_bank = {
            7'h74,
            7'h75,
            7'h6a,
            7'h73
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_upper_PR_by_bank = {
            5'h04,
            5'h04,
            5'h02,
            5'h05
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h74740b0b,
            32'h75750a0a,
            32'h6a6a1515,
            32'h73730c0c
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b1011;
		expected_complete_bus_ROB_index_by_bank = {
            7'h6c,
            7'h6d,
            7'h76,
            7'h6b
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b1111;
		expected_WB_bus_upper_PR_by_bank = {
            5'h05,
            5'h05,
            5'h04,
            5'h04
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h6c6c1313,
            32'h6d6d1212,
            32'h76760909,
            32'h6b6b1414
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0101;
		expected_complete_bus_ROB_index_by_bank = {
            7'h68,
            7'h69,
            7'h6e,
            7'h6f
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple write cycle 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
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
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h68681717,
            32'h69691616,
            32'h6e6e1111,
            32'h6f6f1010
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

        // ------------------------------------------------------------
        // simple read chain:
        test_case = "simple read chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple read cycle 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b111111111;
		tb_read_req_PR_by_rr = {
            7'h06,
            7'h07,
            7'h08,
            7'h00,
            7'h01,
            7'h02,
            7'h03,
            7'h04,
            7'h05
        };
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple read cycle 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b111111111;
		tb_read_req_PR_by_rr = {
            7'h0F,
            7'h10,
            7'h11,
            7'h0E,
            7'h0D,
            7'h0C,
            7'h0B,
            7'h09,
            7'h0A
        };
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b110111111;
		expected_read_resp_data_by_rr = {
            32'h79790606,
            32'h78780707,
            32'h00000000,
            32'h00000000,
            32'h7e7e0101,
            32'h7d7d0202,
            32'h7c7c0303,
            32'h7b7b0404,
            32'h7a7a0505
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple read cycle 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b110111111;
		tb_read_req_PR_by_rr = {
            7'h16,
            7'h17,
            7'h02,
            7'h01,
            7'h00,
            7'h12,
            7'h13,
            7'h14,
            7'h15
        };
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b110111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b111110111;
		expected_read_resp_data_by_rr = {
            32'h70700f0f,
            32'h6f6f1010,
            32'h77770808,
            32'h71710e0e,
            32'h72720d0d,
            32'h00000000,
            32'h74740b0b,
            32'h76760909,
            32'h75750a0a
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple read cycle 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b001000000;
		tb_read_req_PR_by_rr = {
            7'h7F,
            7'h7F,
            7'h02,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111110111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b111101110;
		expected_read_resp_data_by_rr = {
            32'h69691616,
            32'h68681717,
            32'h6e6e1111,
            32'h7e7e0101,
            32'h00000000,
            32'h73730c0c,
            32'h6c6c1313,
            32'h6b6b1414,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple read cycle 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b001011001;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h7d7d0202,
            32'h00000000,
            32'h00000000,
            32'h6d6d1212,
            32'h00000000,
            32'h00000000,
            32'h6a6a1515
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "simple read cycle 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requestor
		tb_read_req_valid_by_rr = 9'b000000000;
		tb_read_req_PR_by_rr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
	    // read req feedback by read requestor
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = 8'b00000000;
		tb_WB_send_complete_by_wr = 8'b01100110;
		tb_WB_data_by_wr = {
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F,
            32'h00007F7F
        };
		tb_WB_PR_by_wr = {
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F,
            7'h7F
        };
		tb_WB_ROB_index_by_wr = {
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00,
            7'h00
        };
	    // writeback feedback by write requestor
	    // writeback bus by bank
	    // forward data by bank
	    // complete bus by bank

		@(negedge CLK);

		// outputs:

	    // read req info by read requestor
	    // read req feedback by read requestor
		expected_read_req_ready_by_rr = 9'b111111111;
	    // read resp info by read requestor
		expected_read_resp_valid_by_rr = 9'b000000000;
		expected_read_resp_data_by_rr = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // writeback info by write requestor
	    // writeback feedback by write requestor
		expected_WB_ready_by_wr = 8'b11111111;
	    // writeback bus by bank
		expected_WB_bus_valid_by_bank = 4'b0000;
		expected_WB_bus_upper_PR_by_bank = {
            5'h00,
            5'h00,
            5'h00,
            5'h00
        };
	    // forward data by bank
		expected_forward_data_bus_by_bank = {
            32'h00000000,
            32'h00000000,
            32'h00000000,
            32'h00000000
        };
	    // complete bus by bank
		expected_complete_bus_valid_by_bank = 4'b0000;
		expected_complete_bus_ROB_index_by_bank = {
            7'h00,
            7'h00,
            7'h00,
            7'h00
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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule