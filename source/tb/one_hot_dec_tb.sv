/*
    Filename: one_hot_dec_tb.sv
    Author: zlagpacan
    Description: Testbench for one_hot_dec module. 
    Spec: LOROF/spec/design/one_hot_dec.md
*/

`timescale 1ns/100ps


module one_hot_dec_tb #(
	parameter WIDTH = 8
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
	logic tb_valid_in;
	logic [$clog2(WIDTH)-1:0] tb_index_in;

	logic [WIDTH-1:0] DUT_one_hot_out, expected_one_hot_out;

    // ----------------------------------------------------------------
    // DUT instantiation:

	one_hot_dec #(
		.WIDTH(WIDTH)
	) DUT (
		.valid_in(tb_valid_in),
		.index_in(tb_index_in),

		.one_hot_out(DUT_one_hot_out)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_one_hot_out !== DUT_one_hot_out) begin
			$display("TB ERROR: expected_one_hot_out (%h) != DUT_one_hot_out (%h)",
				expected_one_hot_out, DUT_one_hot_out);
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
		tb_valid_in = 1'b0;
		tb_index_in = 0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_one_hot_out = 8'b00000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_valid_in = 1'b0;
		tb_index_in = 3;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_one_hot_out = 8'b00000000;

		check_outputs();

        // ------------------------------------------------------------
        // enumerate:
        test_case = "enumerate";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 8; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("i = %0d", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_valid_in = 1'b1;
            tb_index_in = i;

            @(negedge CLK);

            // outputs:

            expected_one_hot_out = '0;
            expected_one_hot_out[i] = 1'b1;

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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule