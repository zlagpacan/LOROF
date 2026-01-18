/*
    Filename: one_hot_enc_tb.sv
    Author: zlagpacan
    Description: Testbench for one_hot_enc module. 
    Spec: LOROF/spec/design/one_hot_enc.md
*/

`timescale 1ns/100ps


module one_hot_enc_tb #(
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
	logic [WIDTH-1:0] tb_one_hot_in;

	logic DUT_valid_out, expected_valid_out;
	logic [$clog2(WIDTH)-1:0] DUT_index_out, expected_index_out;

    // ----------------------------------------------------------------
    // DUT instantiation:

	one_hot_enc #(
		.WIDTH(WIDTH)
	) DUT (
		.one_hot_in(tb_one_hot_in),

		.valid_out(DUT_valid_out),
		.index_out(DUT_index_out)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_valid_out !== DUT_valid_out) begin
			$display("TB ERROR: expected_valid_out (%h) != DUT_valid_out (%h)",
				expected_valid_out, DUT_valid_out);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_index_out !== DUT_index_out) begin
			$display("TB ERROR: expected_index_out (%h) != DUT_index_out (%h)",
				expected_index_out, DUT_index_out);
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
		tb_one_hot_in = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_valid_out = 1'b0;
		expected_index_out = 0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_one_hot_in = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_valid_out = 1'b0;
		expected_index_out = 0;

		check_outputs();

        // ------------------------------------------------------------
        // enumerate:
        test_case = "enumerate";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 8; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // reset
            nRST = 1'b1;
            tb_one_hot_in = '0;
            tb_one_hot_in[i] = 1'b1;

            // inputs
            sub_test_case = $sformatf("tb_one_hot_in = %8b", tb_one_hot_in);
            $display("\t- sub_test: %s", sub_test_case);

            @(negedge CLK);

            // outputs:

            expected_valid_out = 1'b1;
            expected_index_out = i;

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