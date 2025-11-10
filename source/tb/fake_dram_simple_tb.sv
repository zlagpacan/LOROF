/*
    Filename: fake_dram_simple_tb.sv
    Author: zlagpacan
    Description: Testbench for fake_dram_simple module. 
    Spec: LOROF/spec/design/fake_dram_simple.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module fake_dram_simple_tb #(
	parameter SIZE = 2**16,
	parameter INDEX_WIDTH = $clog2(SIZE),
	parameter INIT_FILE = "fake_dram_simple_test.mem"
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

	logic [INDEX_WIDTH-1:0] tb_rindex;
	logic [7:0] DUT_rbyte, expected_rbyte;

	logic tb_wen;
	logic [INDEX_WIDTH-1:0] tb_windex;
	logic [7:0] tb_wbyte;

    // ----------------------------------------------------------------
    // DUT instantiation:

	fake_dram_simple #(
		.SIZE(SIZE),
		.INDEX_WIDTH(INDEX_WIDTH),
		.INIT_FILE(INIT_FILE)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

		.rindex(tb_rindex),
		.rbyte(DUT_rbyte),

		.wen(tb_wen),
		.windex(tb_windex),
		.wbyte(tb_wbyte)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_rbyte !== DUT_rbyte) begin
			$display("TB ERROR: expected_rbyte (%h) != DUT_rbyte (%h)",
				expected_rbyte, DUT_rbyte);
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
		tb_rindex = '0;
		tb_wen = '0;
		tb_windex = '0;
		tb_wbyte = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_rbyte = 8'h93;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = '0;
		tb_wen = '0;
		tb_windex = '0;
		tb_wbyte = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_rbyte = 8'h93;

		check_outputs();

        // ------------------------------------------------------------
        // check bunch of addr's:
        test_case = "check bunch of addr's";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0000;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h93;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0001;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h06;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0002;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h10;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0003;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hFF;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0004;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h23;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0xD";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h000D;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hC3;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0xE";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h000E;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h13;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x11";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0011;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h01;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x12";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0012;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h5A;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x13";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0013;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hC5;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x14";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0014;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h13;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x15";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0015;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h00;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x2000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h2000;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h67;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x2001";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h2001;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h45;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x200B";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h200B;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hFF;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x200C";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h200C;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h00;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x0700";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0700;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h10;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x0701";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0701;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h32;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x0708";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0708;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h01;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x0709";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h0709;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h00;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x3000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h3000;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h0F;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x1024";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h1024;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hB7;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x4000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4000;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hCA;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x4001";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4001;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h89;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x4002";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4002;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h82;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x4003";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4003;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h80;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "@ 0x4004";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4004;
		tb_wen = 1'b0;
		tb_windex = 16'h0000;
		tb_wbyte = 8'h00;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h00;

		check_outputs();

        // ------------------------------------------------------------
        // writes:
        test_case = "writes";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "write @ 0x4000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4000;
		tb_wen = 1'b1;
		tb_windex = 16'h4000;
		tb_wbyte = 8'hAC;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hCA;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "write @ 0x4001";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4001;
		tb_wen = 1'b1;
		tb_windex = 16'h4001;
		tb_wbyte = 8'h98;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h89;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "write @ 0x4002";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4002;
		tb_wen = 1'b1;
		tb_windex = 16'h4002;
		tb_wbyte = 8'h28;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h82;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "write @ 0x4003";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4003;
		tb_wen = 1'b1;
		tb_windex = 16'h4003;
		tb_wbyte = 8'h08;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h80;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "write @ 0x4004";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4004;
		tb_wen = 1'b1;
		tb_windex = 16'h4004;
		tb_wbyte = 8'hFF;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h00;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "read @ 0x4000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4000;
		tb_wen = 1'b0;
		tb_windex = 16'h4000;
		tb_wbyte = 8'hAC;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hAC;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "read @ 0x4001";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4001;
		tb_wen = 1'b0;
		tb_windex = 16'h4001;
		tb_wbyte = 8'h98;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h98;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "read @ 0x4002";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4002;
		tb_wen = 1'b0;
		tb_windex = 16'h4002;
		tb_wbyte = 8'h28;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h28;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "read @ 0x4003";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4003;
		tb_wen = 1'b0;
		tb_windex = 16'h4003;
		tb_wbyte = 8'h08;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'h08;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "read @ 0x4004";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_rindex = 16'h4004;
		tb_wen = 1'b0;
		tb_windex = 16'h4004;
		tb_wbyte = 8'hFF;

		@(negedge CLK);

		// outputs:

		expected_rbyte = 8'hFF;

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