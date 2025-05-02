/*
    Filename: bram_2rport_1wport_tb.sv
    Author: zlagpacan
    Description: Testbench for bram_2rport_1wport module. 
    Spec: LOROF/spec/design/bram_2rport_1wport.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

parameter INNER_WIDTH = 32;
parameter OUTER_WIDTH = 32;
parameter INIT_FILE = "";

module bram_2rport_1wport_tb ();

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

	logic tb_port0_ren;
	logic [$clog2(OUTER_WIDTH)-1:0] tb_port0_rindex;
	logic [INNER_WIDTH-1:0] DUT_port0_rdata, expected_port0_rdata;

	logic tb_port1_ren;
	logic [$clog2(OUTER_WIDTH)-1:0] tb_port1_rindex;
	logic [INNER_WIDTH-1:0] DUT_port1_rdata, expected_port1_rdata;

	logic [INNER_WIDTH/8-1:0] tb_wen_byte;
	logic [$clog2(OUTER_WIDTH)-1:0] tb_windex;
	logic [INNER_WIDTH-1:0] tb_wdata;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bram_2rport_1wport #(
		.INNER_WIDTH(32),
		.OUTER_WIDTH(32),
		.INIT_FILE(INIT_FILE)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

		.port0_ren(tb_port0_ren),
		.port0_rindex(tb_port0_rindex),
		.port0_rdata(DUT_port0_rdata),

		.port1_ren(tb_port1_ren),
		.port1_rindex(tb_port1_rindex),
		.port1_rdata(DUT_port1_rdata),

		.wen_byte(tb_wen_byte),
		.windex(tb_windex),
		.wdata(tb_wdata)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_port0_rdata !== DUT_port0_rdata) begin
			$display("TB ERROR: expected_port0_rdata (%h) != DUT_port0_rdata (%h)",
				expected_port0_rdata, DUT_port0_rdata);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_port1_rdata !== DUT_port1_rdata) begin
			$display("TB ERROR: expected_port1_rdata (%h) != DUT_port1_rdata (%h)",
				expected_port1_rdata, DUT_port1_rdata);
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
		tb_port0_ren = 1'b0;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b0;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b0000;
		tb_windex = 5'h0;
		tb_wdata = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_port0_rdata = 32'h0;
		expected_port1_rdata = 32'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_port0_ren = 1'b0;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b0;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b0000;
		tb_windex = 5'h0;
		tb_wdata = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_port0_rdata = 32'h0;
		expected_port1_rdata = 32'h0;

		check_outputs();

        // ------------------------------------------------------------
        // write sequence:
        test_case = "write sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 32; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("write %0h", i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			tb_port0_ren = 1'b1;
			tb_port0_rindex = i[4:0];
			tb_port1_ren = 1'b1;
			tb_port1_rindex = i[4:0];
			tb_wen_byte = 4'b1111;
			tb_windex = i[4:0];
			tb_wdata = {~i[7:0], i[7:0], ~i[7:0], i[7:0]};

			@(negedge CLK);

			// outputs:

			expected_port0_rdata = 32'h0;
			expected_port1_rdata = 32'h0;

			check_outputs();
		end

        // ------------------------------------------------------------
        // read sequence:
        test_case = "read sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("read req 0, read resp NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_port0_ren = 1'b1;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b1;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b1111;
		tb_windex = 5'h0;
		tb_wdata = 32'hFF00FF00;

		@(negedge CLK);

		// outputs:

		expected_port0_rdata = 32'h0;
		expected_port1_rdata = 32'h0;

		check_outputs();

		for (int i = 0; i < 31; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("read req %0h, read resp %0h", i+1, i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			tb_port0_ren = 1'b1;
			tb_port0_rindex = {i+1};
			tb_port1_ren = 1'b1;
			tb_port1_rindex = {i+1};
			tb_wen_byte = 4'b0000;
			tb_windex = 5'h0;
			tb_wdata = 32'h0;

			@(negedge CLK);

			// outputs:

			expected_port0_rdata = {~i[7:0], i[7:0], ~i[7:0], i[7:0]};
			expected_port1_rdata = {~i[7:0], i[7:0], ~i[7:0], i[7:0]};

			check_outputs();
		end

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("read req 0, read resp 1f");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_port0_ren = 1'b1;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b1;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b0000;
		tb_windex = 5'h0;
		tb_wdata = 32'h0;

		@(negedge CLK);

		// outputs:

		expected_port0_rdata = 32'hE01FE01F;
		expected_port1_rdata = 32'hE01FE01F;

		check_outputs();

        // ------------------------------------------------------------
        // RAW sequence:
        test_case = "RAW sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("read req 0, read resp 0, first write 0");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_port0_ren = 1'b1;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b1;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b1111;
		tb_windex = 5'h0;
		tb_wdata = 32'h01234567;

		@(negedge CLK);

		// outputs:

		expected_port0_rdata = 32'hFF00FF00;
		expected_port1_rdata = 32'hFF00FF00;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("read req 0, read resp old 0, second write 0");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_port0_ren = 1'b1;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b1;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b1111;
		tb_windex = 5'h0;
		tb_wdata = 32'h89abcdef;

		@(negedge CLK);

		// outputs:

		expected_port0_rdata = 32'hFF00FF00;
		expected_port1_rdata = 32'hFF00FF00;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("read req 0, read resp first 0");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_port0_ren = 1'b1;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b1;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b0000;
		tb_windex = 5'h0;
		tb_wdata = 32'h0;

		@(negedge CLK);

		// outputs:

		expected_port0_rdata = 32'h01234567;
		expected_port1_rdata = 32'h01234567;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("read req 0, read resp second 0");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_port0_ren = 1'b1;
		tb_port0_rindex = 5'h0;
		tb_port1_ren = 1'b1;
		tb_port1_rindex = 5'h0;
		tb_wen_byte = 4'b0000;
		tb_windex = 5'h0;
		tb_wdata = 32'h0;

		@(negedge CLK);

		// outputs:

		expected_port0_rdata = 32'h89abcdef;
		expected_port1_rdata = 32'h89abcdef;

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