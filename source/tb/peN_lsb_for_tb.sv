/*
    Filename: peN_lsb_for_tb.sv
    Author: zlagpacan
    Description: Testbench for peN_lsb_for module. 
    Spec: LOROF/spec/design/peN_lsb_for.md
*/

`timescale 1ns/100ps


module peN_lsb_for_tb #(
	parameter int unsigned WIDTH = 8,
	parameter int unsigned N = 3
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

	logic [N-1:0] DUT_ack_valid_by_n, expected_ack_valid_by_n;
	logic [N-1:0][WIDTH-1:0] DUT_ack_one_hot_by_n, expected_ack_one_hot_by_n;

    // ----------------------------------------------------------------
    // DUT instantiation:

	peN_lsb_for #(
		.WIDTH(WIDTH),
		.N(N)
	) DUT (
		.req_vec(tb_req_vec),

		.ack_valid_by_n(DUT_ack_valid_by_n),
		.ack_one_hot_by_n(DUT_ack_one_hot_by_n)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ack_valid_by_n !== DUT_ack_valid_by_n) begin
			$display("TB ERROR: expected_ack_valid_by_n (%h) != DUT_ack_valid_by_n (%h)",
				expected_ack_valid_by_n, DUT_ack_valid_by_n);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack_one_hot_by_n !== DUT_ack_one_hot_by_n) begin
			$display("TB ERROR: expected_ack_one_hot_by_n (%h) != DUT_ack_one_hot_by_n (%h)",
				expected_ack_one_hot_by_n, DUT_ack_one_hot_by_n);
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

		expected_ack_valid_by_n = 3'b000;
		expected_ack_one_hot_by_n = {
            8'b00000000,
            8'b00000000,
            8'b00000000
        };

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_valid_by_n = 3'b000;
		expected_ack_one_hot_by_n = {
            8'b00000000,
            8'b00000000,
            8'b00000000
        };

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

		expected_ack_valid_by_n = 3'b001;
		expected_ack_one_hot_by_n = {
            8'b00000000,
            8'b00000000,
            8'b00000100
        };

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

		expected_ack_valid_by_n = 3'b011;
		expected_ack_one_hot_by_n = {
            8'b00000000,
            8'b01000000,
            8'b00010000
        };

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

		expected_ack_valid_by_n = 3'b111;
		expected_ack_one_hot_by_n = {
            8'b10000000,
            8'b00000010,
            8'b00000001
        };

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "four";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 8'b01011010;

		@(negedge CLK);

		// outputs:

		expected_ack_valid_by_n = 3'b111;
		expected_ack_one_hot_by_n = {
            8'b00010000,
            8'b00001000,
            8'b00000010
        };

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
            expected_ack_valid_by_n[0] = $countones(tb_req_vec) >= 1;
            expected_ack_valid_by_n[1] = $countones(tb_req_vec) >= 2;
            expected_ack_valid_by_n[2] = $countones(tb_req_vec) >= 3;

            expected_ack_one_hot_by_n[0] = 8'b00000000;
            for (int j = 0; j < WIDTH; j++) begin
                if (i[j]) begin
                    expected_ack_one_hot_by_n[0][j] = 1'b1;
                    break;
                end
            end

            expected_ack_one_hot_by_n[1] = 8'b00000000;
            for (int j = 1; j < WIDTH; j++) begin
                for (int k = 0; k < j; k++) begin
                    if (i[k] & i[j]) begin
                        expected_ack_one_hot_by_n[1][j] = 1'b1;
                        break;
                    end
                end
                if (expected_ack_one_hot_by_n[1][j]) begin
                    break;
                end
            end

            expected_ack_one_hot_by_n[2] = 8'b00000000;
            for (int j = 2; j < WIDTH; j++) begin
                for (int k = 1; k < j; k++) begin
                    for (int l = 0; l < k; l++) begin
                        if (i[l] & i[k] & i[j]) begin
                            expected_ack_one_hot_by_n[2][j] = 1'b1;
                        end
                    end
                    if (expected_ack_one_hot_by_n[2][j]) begin
                        break;
                    end
                end
                if (expected_ack_one_hot_by_n[2][j]) begin
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