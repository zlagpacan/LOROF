/*
    Filename: q_fast_ready_tb.sv
    Author: zlagpacan
    Description: Testbench for q_fast_ready module. 
    Spec: LOROF/spec/design/q_fast_ready.md
*/

`timescale 1ns/100ps

module q_fast_ready_tb #(
	parameter DATA_WIDTH = 32,
	parameter NUM_ENTRIES = 4,
	parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
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

    // enq
	logic tb_enq_valid;
	logic [DATA_WIDTH-1:0] tb_enq_data;

    // enq feedback
	logic DUT_enq_ready, expected_enq_ready;

    // deq
	logic DUT_deq_valid, expected_deq_valid;
	logic [DATA_WIDTH-1:0] DUT_deq_data, expected_deq_data;

    // deq feedback
	logic tb_deq_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

	q_fast_ready #(
		.DATA_WIDTH(DATA_WIDTH),
    	.NUM_ENTRIES(NUM_ENTRIES)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // enq
		.enq_valid(tb_enq_valid),
		.enq_data(tb_enq_data),

	    // enq feedback
		.enq_ready(DUT_enq_ready),

	    // deq
		.deq_valid(DUT_deq_valid),
		.deq_data(DUT_deq_data),

	    // deq feedback
		.deq_ready(tb_deq_ready)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_enq_ready !== DUT_enq_ready) begin
			$display("TB ERROR: expected_enq_ready (%h) != DUT_enq_ready (%h)",
				expected_enq_ready, DUT_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_valid !== DUT_deq_valid) begin
			$display("TB ERROR: expected_deq_valid (%h) != DUT_deq_valid (%h)",
				expected_deq_valid, DUT_deq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_data !== DUT_deq_data) begin
			$display("TB ERROR: expected_deq_data (%h) != DUT_deq_data (%h)",
				expected_deq_data, DUT_deq_data);
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
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h00000000;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h00000000;
	    // deq feedback

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h00000000;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h00000000;
	    // deq feedback

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - enq 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hff00ff00;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'h00000000;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, i, i, i} - enq 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hee11ee11;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hff00ff00;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, i, i} - enq 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hdd22dd22;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hff00ff00;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, 2, i} - enq 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hcc33cc33;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hff00ff00;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, 2, 3} - failed enq 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hbb44bb44;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hff00ff00;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{0, 1, 2, 3} - failed enq 4, deq 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hbb44bb44;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hff00ff00;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, 1, 2, 3} - enq 4, deq 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'hbb44bb44;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hee11ee11;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, i, 2, 3} - enq 5, deq 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'haa55aa55;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hdd22dd22;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, 5, i, 3} - deq 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h99669966;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hcc33cc33;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{4, 5, i, i} - deq 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h99669966;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'hbb44bb44;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, 5, i, i} - deq 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h99669966;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'haa55aa55;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - failed deq 6/2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h99669966;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'hdd22dd22;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - enq 6, failed deq 6/2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_data = 32'h99669966;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'hdd22dd22;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, 6, i} - deq 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h88778877;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b1;
		expected_deq_data = 32'h99669966;
	    // deq feedback

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i} - failed deq 7/3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_data = 32'h88778877;
	    // enq feedback
	    // deq
	    // deq feedback
		tb_deq_ready = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
	    // deq
		expected_deq_valid = 1'b0;
		expected_deq_data = 32'hcc33cc33;
	    // deq feedback

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