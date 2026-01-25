/*
    Filename: plru_updater_tb.sv
    Author: zlagpacan
    Description: Testbench for plru_updater module. 
    Spec: LOROF/spec/design/plru_updater.md
*/

`timescale 1ns/100ps

module plru_updater_tb #(
	parameter int unsigned NUM_ENTRIES = 8,
	parameter int unsigned LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
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
	logic [NUM_ENTRIES-2:0] tb_plru_in;

	logic tb_new_valid;
	logic [LOG_NUM_ENTRIES-1:0] DUT_new_way, expected_new_way;

	logic tb_touch_valid;
	logic [LOG_NUM_ENTRIES-1:0] tb_touch_way;

	logic [NUM_ENTRIES-2:0] DUT_plru_out, expected_plru_out;

    // ----------------------------------------------------------------
    // DUT instantiation:

	plru_updater #(
		.NUM_ENTRIES(NUM_ENTRIES),
		.LOG_NUM_ENTRIES(LOG_NUM_ENTRIES)
	) DUT (
		.plru_in(tb_plru_in),

		.new_valid(tb_new_valid),
		.new_way(DUT_new_way),

		.touch_valid(tb_touch_valid),
		.touch_way(tb_touch_way),

		.plru_out(DUT_plru_out)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_new_way !== DUT_new_way) begin
			$display("TB ERROR: expected_new_way (%h) != DUT_new_way (%h)",
				expected_new_way, DUT_new_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_plru_out !== DUT_plru_out) begin
			$display("TB ERROR: expected_plru_out (%h) != DUT_plru_out (%h)",
				expected_plru_out, DUT_plru_out);
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
		tb_plru_in = {4'b0000, 2'b00, 1'b0};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b0000, 2'b00, 1'b0};

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0000, 2'b00, 1'b0};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b0000, 2'b00, 1'b0};

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0000, 2'b00, 1'b0};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b0001, 2'b01, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0001, 2'b01, 1'b1};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b001;
		expected_plru_out = {4'b0011, 2'b11, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0011, 2'b11, 1'b0};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b010;
		expected_plru_out = {4'b0111, 2'b10, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 3 (stall)";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0111, 2'b10, 1'b1};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b011;
		expected_plru_out = {4'b0111, 2'b10, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0111, 2'b10, 1'b1};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b011;
		expected_plru_out = {4'b1111, 2'b00, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1111, 2'b00, 1'b0};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b100;
		expected_plru_out = {4'b1110, 2'b01, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1110, 2'b01, 1'b1};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b101;
		expected_plru_out = {4'b1100, 2'b11, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1100, 2'b11, 1'b0};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b110;
		expected_plru_out = {4'b1000, 2'b10, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "new cycle 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1000, 2'b10, 1'b1};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b111;
		expected_plru_out = {4'b0000, 2'b00, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 7";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0000, 2'b00, 1'b0};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b111;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b0000, 2'b00, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 5";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0000, 2'b00, 1'b0};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b101;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b0000, 2'b10, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0000, 2'b10, 1'b0};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b011;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b1000, 2'b00, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1000, 2'b00, 1'b0};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b001;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b1010, 2'b10, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 6";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1010, 2'b10, 1'b0};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b110;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b000;
		expected_plru_out = {4'b1010, 2'b10, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 4";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1010, 2'b10, 1'b1};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b100;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b111;
		expected_plru_out = {4'b1010, 2'b11, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1010, 2'b11, 1'b1};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b010;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b111;
		expected_plru_out = {4'b1110, 2'b10, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "touch 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1110, 2'b10, 1'b1};
		tb_new_valid = 1'b0;
		tb_touch_valid = 1'b1;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b111;
		expected_plru_out = {4'b1111, 2'b11, 1'b1};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "renew cycle 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b1111, 2'b11, 1'b1};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b111;
		expected_plru_out = {4'b0111, 2'b01, 1'b0};

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "renew cycle 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_plru_in = {4'b0111, 2'b01, 1'b0};
		tb_new_valid = 1'b1;
		tb_touch_valid = 1'b0;
		tb_touch_way = 3'b000;

		@(negedge CLK);

		// outputs:

		expected_new_way = 3'b110;
		expected_plru_out = {4'b0011, 2'b00, 1'b1};

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