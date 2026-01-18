/*
    Filename: pe_lsb_for_tb.sv
    Author: zlagpacan
    Description: Testbench for pe_lsb_for module. 
    Spec: LOROF/spec/design/pe_lsb_for.md
*/

`timescale 1ns/100ps


module pe_lsb_for_tb #(
	parameter int unsigned WIDTH = 8
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

	logic [WIDTH-1:0] DUT_ack_one_hot, expected_ack_one_hot;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pe_lsb_for #(
		.WIDTH(WIDTH)
	) DUT (
		.req_vec(tb_req_vec),

		.ack_one_hot(DUT_ack_one_hot)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ack_one_hot !== DUT_ack_one_hot) begin
			$display("TB ERROR: expected_ack_one_hot (%h) != DUT_ack_one_hot (%h)",
				expected_ack_one_hot, DUT_ack_one_hot);
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
		tb_req_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_one_hot = 8'b00000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_one_hot = 8'b00000000;

		check_outputs();

        // ------------------------------------------------------------
        // enumerate:
        test_case = "enumerate";
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
            expected_ack_one_hot = '0;
            for (int j = 0; j < WIDTH; j++) begin
                if (i[j]) begin
                    expected_ack_one_hot[j] = 1'b1;
                    break;
                end
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
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule