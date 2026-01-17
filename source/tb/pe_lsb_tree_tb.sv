/*
    Filename: pe_lsb_tree_tb.sv
    Author: zlagpacan
    Description: Testbench for pe_lsb_tree module. 
    Spec: LOROF/spec/design/pe_lsb_tree.md
*/

`timescale 1ns/100ps


module pe_lsb_tree_tb #(
	parameter int unsigned WIDTH = 8,
	parameter int unsigned LEVELS = $clog2(WIDTH)
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
	logic [WIDTH-1:0] tb_req_vec;

	logic DUT_ack_valid, expected_ack_valid;
	logic [LEVELS-1:0] DUT_ack_index, expected_ack_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pe_lsb_tree #(
		.WIDTH(WIDTH),
		.LEVELS(LEVELS)
	) DUT (
		.req_vec(tb_req_vec),

		.ack_valid(DUT_ack_valid),
		.ack_index(DUT_ack_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ack_valid !== DUT_ack_valid) begin
			$display("TB ERROR: expected_ack_valid (%h) != DUT_ack_valid (%h)",
				expected_ack_valid, DUT_ack_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack_index !== DUT_ack_index) begin
			$display("TB ERROR: expected_ack_index (%h) != DUT_ack_index (%h)",
				expected_ack_index, DUT_ack_index);
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
		tb_req_vec = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_valid = 1'b0;
		expected_ack_index = 3'b111;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_valid = 1'b0;
		expected_ack_index = 3'b111;

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 2**WIDTH; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("i = %8b", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_req_vec = i;

            @(negedge CLK);

            // outputs:
            expected_ack_valid = 1'b1;
            expected_ack_index = 0;
            for (int j = 0; j < WIDTH; j++) begin
                if (i[j]) begin
                    expected_ack_valid = 1'b1;
                    expected_ack_index = j;
                    break;
                end
            end

            if (tb_req_vec == 0) begin
                expected_ack_valid = 1'b0;
                expected_ack_index = '1;
            end

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