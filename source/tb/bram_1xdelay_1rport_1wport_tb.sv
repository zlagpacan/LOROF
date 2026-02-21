/*
    Filename: bram_1xdelay_1rport_1wport_tb.sv
    Author: zlagpacan
    Description: Testbench for bram_1xdelay_1rport_1wport module. 
    Spec: LOROF/spec/design/bram_1xdelay_1rport_1wport.md
*/

`timescale 1ns/100ps


module bram_1xdelay_1rport_1wport_tb #(
	parameter INNER_WIDTH = 32,
	parameter OUTER_WIDTH = 32,
	parameter INIT_FILE = ""
) ();

    // ----------------------------------------------------------------
    // TB setup:

    // parameters
    parameter int unsigned PERIOD = 10;

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

	logic tb_ren0;
	logic tb_ren1;
	logic [$clog2(OUTER_WIDTH)-1:0] tb_rindex;
	logic [INNER_WIDTH-1:0] DUT_rdata, expected_rdata;

	logic [INNER_WIDTH/8-1:0] tb_wen_byte;
	logic [$clog2(OUTER_WIDTH)-1:0] tb_windex;
	logic [INNER_WIDTH-1:0] tb_wdata;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bram_1xdelay_1rport_1wport #(
		.INNER_WIDTH(INNER_WIDTH),
		.OUTER_WIDTH(OUTER_WIDTH),
		.INIT_FILE(INIT_FILE)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

		.ren0(tb_ren0),
		.ren1(tb_ren1),
		.rindex(tb_rindex),
		.rdata(DUT_rdata),

		.wen_byte(tb_wen_byte),
		.windex(tb_windex),
		.wdata(tb_wdata)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_rdata !== DUT_rdata) begin
			$display("TB ERROR: expected_rdata (%h) != DUT_rdata (%h)",
				expected_rdata, DUT_rdata);
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
		tb_ren0 = '0;
		tb_ren1 = '0;
		tb_rindex = '0;
		tb_wen_byte = '0;
		tb_windex = '0;
		tb_wdata = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_rdata = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_ren0 = '0;
		tb_ren1 = '0;
		tb_rindex = '0;
		tb_wen_byte = '0;
		tb_windex = '0;
		tb_wdata = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_rdata = '0;

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
		tb_ren0 = '0;
		tb_ren1 = '0;
		tb_rindex = '0;
		tb_wen_byte = '0;
		tb_windex = '0;
		tb_wdata = '0;

		@(negedge CLK);

		// outputs:

		expected_rdata = '0;

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