/*
    Filename: prf_ff_tb.sv
    Author: zlagpacan
    Description: Testbench for prf_ff module. 
    Spec: LOROF/spec/design/prf_ff.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf_ff_tb ();

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


    // read req info by read requester
	logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_read_req_PR_by_rr;

    // read resp info by read requestor
	logic [PRF_RR_COUNT-1:0][31:0] DUT_read_resp_data_by_rr, expected_read_resp_data_by_rr;

    // writeback info by write requestor
	logic [PRF_WR_COUNT-1:0] tb_WB_valid_by_wr;
	logic [PRF_WR_COUNT-1:0][31:0] tb_WB_data_by_wr;
	logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0] tb_WB_PR_by_wr;

    // ----------------------------------------------------------------
    // DUT instantiation:

	prf_ff DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // read req info by read requester
		.read_req_PR_by_rr(tb_read_req_PR_by_rr),

	    // read resp info by read requestor
		.read_resp_data_by_rr(DUT_read_resp_data_by_rr),

	    // writeback info by write requestor
		.WB_valid_by_wr(tb_WB_valid_by_wr),
		.WB_data_by_wr(tb_WB_data_by_wr),
		.WB_PR_by_wr(tb_WB_PR_by_wr)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_read_resp_data_by_rr !== DUT_read_resp_data_by_rr) begin
			$display("TB ERROR: expected_read_resp_data_by_rr (%h) != DUT_read_resp_data_by_rr (%h)",
				expected_read_resp_data_by_rr, DUT_read_resp_data_by_rr);
			num_errors++;
			tb_error = 1'b1;
		end

        #(PERIOD / 10);
        tb_error = 1'b0;
    end
    endtask

	function automatic logic [6:0] i_addr_map (int i);
	begin
		i_addr_map = {i}[6:0];
	end
	endfunction

	function automatic logic [31:0] i_data_map (int i);
	begin
		logic [7:0] addr_byte = {1'b0, i_addr_map(i)};
		i_data_map = addr_byte == 0 ? 32'h0 : {{2{~addr_byte}}, {2{addr_byte}}};
	end
	endfunction

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
	    // read req info by read requester
		tb_read_req_PR_by_rr = '0;
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = '0;
		tb_WB_data_by_wr = '0;
		tb_WB_PR_by_wr = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // read req info by read requester
	    // read resp info by read requestor
		expected_read_resp_data_by_rr = '0;
	    // writeback info by write requestor

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // read req info by read requester
		tb_read_req_PR_by_rr = '0;
	    // read resp info by read requestor
	    // writeback info by write requestor
		tb_WB_valid_by_wr = '0;
		tb_WB_data_by_wr = '0;
		tb_WB_PR_by_wr = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // read req info by read requester
	    // read resp info by read requestor
		expected_read_resp_data_by_rr = '0;
	    // writeback info by write requestor

		check_outputs();

        // ------------------------------------------------------------
        // writes:
        test_case = "writes";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 128; i+=7) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("write p%0h:p%0h", i, i+7);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// read req info by read requester
			tb_read_req_PR_by_rr = '0;
			// read resp info by read requestor
			// writeback info by write requestor
			tb_WB_valid_by_wr = 7'b1111111;
			tb_WB_data_by_wr = {
				i_data_map(i+0),
				i_data_map(i+1),
				i_data_map(i+2),
				i_data_map(i+3),
				i_data_map(i+4),
				i_data_map(i+5),
				i_data_map(i+6)
			};
			tb_WB_PR_by_wr = {
				i_addr_map(i+0),
				i_addr_map(i+1),
				i_addr_map(i+2),
				i_addr_map(i+3),
				i_addr_map(i+4),
				i_addr_map(i+5),
				i_addr_map(i+6)
			};

			@(negedge CLK);

			// read req info by read requester
			// read resp info by read requestor
			expected_read_resp_data_by_rr = '0;
			// writeback info by write requestor

			check_outputs();

		end

        // ------------------------------------------------------------
        // reads:
        test_case = "reads";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 128; i+=11) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("read p%0h:p%0h", i, i+11);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// read req info by read requester
			tb_read_req_PR_by_rr = {
				i_addr_map(i+0),
				i_addr_map(i+1),
				i_addr_map(i+2),
				i_addr_map(i+3),
				i_addr_map(i+4),
				i_addr_map(i+5),
				i_addr_map(i+6),
				i_addr_map(i+7),
				i_addr_map(i+8),
				i_addr_map(i+9),
				i_addr_map(i+10)
			};
			// read resp info by read requestor
			// writeback info by write requestor
			tb_WB_valid_by_wr = 7'b0000000;
			tb_WB_data_by_wr = '0;
			tb_WB_PR_by_wr = '0;

			@(negedge CLK);

			// read req info by read requester
			// read resp info by read requestor
			expected_read_resp_data_by_rr = {
				i_data_map(i+0),
				i_data_map(i+1),
				i_data_map(i+2),
				i_data_map(i+3),
				i_data_map(i+4),
				i_data_map(i+5),
				i_data_map(i+6),
				i_data_map(i+7),
				i_data_map(i+8),
				i_data_map(i+9),
				i_data_map(i+10)
			};
			// writeback info by write requestor

			check_outputs();

		end

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