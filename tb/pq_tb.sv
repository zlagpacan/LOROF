/*
    Filename: pq_tb.sv
    Author: zlagpacan
    Description: Testbench for pq module. 
    Spec: LOROF/spec/design/pq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module pq_tb ();

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
	logic [14-1:0] tb_req_vec;
	logic [14-1:0] DUT_pq_vec, expected_pq_vec;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pq DUT (
		.req_vec(tb_req_vec),
		.pq_vec(DUT_pq_vec)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_pq_vec !== DUT_pq_vec) begin
			$display("TB ERROR: expected_pq_vec (%14b) != DUT_pq_vec (%14b)",
				expected_pq_vec, DUT_pq_vec);
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
		tb_req_vec = 14'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_pq_vec = 14'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_vec = 14'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_pq_vec = 14'h0;

		check_outputs();

        // ------------------------------------------------------------
        // loop:
        test_case = "loop";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 2**14; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("input = %14b", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_req_vec = i;

            @(negedge CLK);

            // outputs:

            expected_pq_vec = 14'h0;
            for (int j = 13; j >= 0; j--) begin
                if (i[j]) begin 
                    expected_pq_vec[j] = 1'b1;
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