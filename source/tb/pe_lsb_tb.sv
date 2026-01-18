/*
    Filename: pe_lsb_tb.sv
    Author: zlagpacan
    Description: Testbench for pe_lsb module. 
    Spec: LOROF/spec/design/pe_lsb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module pe_lsb_tb #(
	parameter WIDTH = 8,
	parameter USE_ONE_HOT = 1,
	parameter USE_COLD = 1,
	parameter USE_INDEX = 1
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
	logic [WIDTH-1:0] DUT_ack_mask, expected_ack_mask;
	logic [WIDTH-1:0] DUT_cold_ack_mask, expected_cold_ack_mask;
	logic [$clog2(WIDTH)-1:0] DUT_ack_index, expected_ack_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pe_lsb #(
		.WIDTH(WIDTH),
		.USE_ONE_HOT(USE_ONE_HOT),
		.USE_COLD(USE_COLD),
		.USE_INDEX(USE_INDEX)
	) DUT (
		.req_vec(tb_req_vec),

		.ack_one_hot(DUT_ack_one_hot),
		.ack_mask(DUT_ack_mask),
		.cold_ack_mask(DUT_cold_ack_mask),
		.ack_index(DUT_ack_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_ack_one_hot !== DUT_ack_one_hot) begin
			$display("TB ERROR: expected_ack_one_hot (%b) != DUT_ack_one_hot (%b)",
				expected_ack_one_hot, DUT_ack_one_hot);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack_mask !== DUT_ack_mask) begin
			$display("TB ERROR: expected_ack_mask (%b) != DUT_ack_mask (%b)",
				expected_ack_mask, DUT_ack_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_cold_ack_mask !== DUT_cold_ack_mask) begin
			$display("TB ERROR: expected_cold_ack_mask (%b) != DUT_cold_ack_mask (%b)",
				expected_cold_ack_mask, DUT_cold_ack_mask);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_ack_index !== DUT_ack_index) begin
			$display("TB ERROR: expected_ack_index (%b) != DUT_ack_index (%b)",
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
		tb_req_vec = 8'b00000000;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_ack_one_hot = 8'b00000000;
		expected_ack_mask = 8'b00000000;
		expected_cold_ack_mask = 8'b00000000;
		expected_ack_index = 3'h0;

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
		expected_ack_mask = 8'b00000000;
		expected_cold_ack_mask = 8'b00000000;
		expected_ack_index = 3'h0;

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
            expected_ack_one_hot = '0;
            expected_ack_mask = '0;
            expected_cold_ack_mask = '0;
            expected_ack_index = '0;
            for (int j = 0; j < WIDTH; j++) begin
                if (i[j]) begin
                    expected_ack_one_hot[j] = 1'b1;
                    expected_ack_index = j;
                    for (int k = j; k < WIDTH; k++) begin
                        expected_ack_mask[k] = 1'b1;
                    end
                    for (int l = j+1; l < WIDTH; l++) begin
                        expected_cold_ack_mask[l] = 1'b1;
                    end
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