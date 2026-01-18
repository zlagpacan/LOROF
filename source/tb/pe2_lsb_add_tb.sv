/*
    Filename: pe2_lsb_add_tb.sv
    Author: zlagpacan
    Description: Testbench for pe2_lsb_add module. 
    Spec: LOROF/spec/design/pe2_lsb_add.md
*/

`timescale 1ns/100ps


module pe2_lsb_add_tb #(
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

	logic DUT_ack0_valid, expected_ack0_valid;
	logic [WIDTH-1:0] DUT_ack0_one_hot, expected_ack0_one_hot;

	logic DUT_ack1_valid, expected_ack1_valid;
	logic [WIDTH-1:0] DUT_ack1_one_hot, expected_ack1_one_hot;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pe2_lsb_add #(
		.WIDTH(WIDTH)
	) DUT (
		.req_vec(tb_req_vec),

		.ack0_valid(DUT_ack0_valid),
		.ack0_one_hot(DUT_ack0_one_hot),

		.ack1_valid(DUT_ack1_valid),
		.ack1_one_hot(DUT_ack1_one_hot)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ack0_valid !== DUT_ack0_valid) begin
			$display("TB ERROR: expected_ack0_valid (%h) != DUT_ack0_valid (%h)",
				expected_ack0_valid, DUT_ack0_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack0_one_hot !== DUT_ack0_one_hot) begin
			$display("TB ERROR: expected_ack0_one_hot (%h) != DUT_ack0_one_hot (%h)",
				expected_ack0_one_hot, DUT_ack0_one_hot);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack1_valid !== DUT_ack1_valid) begin
			$display("TB ERROR: expected_ack1_valid (%h) != DUT_ack1_valid (%h)",
				expected_ack1_valid, DUT_ack1_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack1_one_hot !== DUT_ack1_one_hot) begin
			$display("TB ERROR: expected_ack1_one_hot (%h) != DUT_ack1_one_hot (%h)",
				expected_ack1_one_hot, DUT_ack1_one_hot);
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

		expected_ack0_valid = 1'b0;
		expected_ack0_one_hot = 8'b00000000;
		expected_ack1_valid = 1'b0;
		expected_ack1_one_hot = 8'b00000000;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack0_valid = 1'b0;
		expected_ack0_one_hot = 8'b00000000;
		expected_ack1_valid = 1'b0;
		expected_ack1_one_hot = 8'b00000000;

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "one";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b00000100;

		@(negedge CLK);

		// outputs:

		expected_ack0_valid = 1'b1;
		expected_ack0_one_hot = 8'b00000100;
		expected_ack1_valid = 1'b0;
		expected_ack1_one_hot = 8'b00000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "two";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b01010000;

		@(negedge CLK);

		// outputs:

		expected_ack0_valid = 1'b1;
		expected_ack0_one_hot = 8'b00010000;
		expected_ack1_valid = 1'b1;
		expected_ack1_one_hot = 8'b01000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "three";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b10000011;

		@(negedge CLK);

		// outputs:

		expected_ack0_valid = 1'b1;
		expected_ack0_one_hot = 8'b00000001;
		expected_ack1_valid = 1'b1;
		expected_ack1_one_hot = 8'b00000010;

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
            expected_ack0_valid = $countones(tb_req_vec) >= 1;
            expected_ack1_valid = $countones(tb_req_vec) >= 2;

            expected_ack0_one_hot = 8'b00000000;
            for (int j = 0; j < WIDTH; j++) begin
                if (i[j]) begin
                    expected_ack0_one_hot[j] = 1'b1;
                    break;
                end
            end

            expected_ack1_one_hot = 8'b00000000;
            for (int j = 1; j < WIDTH; j++) begin
                for (int k = 0; k < j; k++) begin
                    if (i[k] & i[j]) begin
                        expected_ack1_one_hot[j] = 1'b1;
                        break;
                    end
                end
                if (expected_ack1_one_hot[j]) begin
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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule