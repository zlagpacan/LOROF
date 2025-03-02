/*
    Filename: upct_tb.sv
    Author: zlagpacan
    Description: Testbench for upct module. 
    Spec: LOROF/spec/design/upct.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module upct_tb ();

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


    // RESP stage
	logic tb_valid_RESP;
	logic [LOG_UPCT_ENTRIES-1:0] tb_upct_index_RESP;
	logic [UPPER_PC_WIDTH-1:0] DUT_upper_PC_RESP, expected_upper_PC_RESP;

    // Update 0
	logic tb_update0_valid;
	logic [31:0] tb_update0_start_full_PC;

    // Update 1
	logic [LOG_UPCT_ENTRIES-1:0] DUT_update1_upct_index, expected_update1_upct_index;

    // ----------------------------------------------------------------
    // DUT instantiation:

	upct DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // RESP stage
		.valid_RESP(tb_valid_RESP),
		.upct_index_RESP(tb_upct_index_RESP),
		.upper_PC_RESP(DUT_upper_PC_RESP),

	    // Update 0
		.update0_valid(tb_update0_valid),
		.update0_start_full_PC(tb_update0_start_full_PC),

	    // Update 1
		.update1_upct_index(DUT_update1_upct_index)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_upper_PC_RESP !== DUT_upper_PC_RESP) begin
			$display("TB ERROR: expected_upper_PC_RESP (%h) != DUT_upper_PC_RESP (%h)",
				expected_upper_PC_RESP, DUT_upper_PC_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_update1_upct_index !== DUT_update1_upct_index) begin
			$display("TB ERROR: expected_update1_upct_index (%h) != DUT_update1_upct_index (%h)",
				expected_update1_upct_index, DUT_update1_upct_index);
			num_errors++;
			tb_error = 1'b1;
		end

        #(PERIOD / 10);
        tb_error = 1'b0;
    end
    endtask

	logic [0:7][2:0] first_pass_plru_mapping = {3'h0, 3'h4, 3'h2, 3'h6, 3'h1, 3'h5, 3'h3, 3'h7};

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
	    // RESP stage
		tb_valid_RESP = 1'b0;
		tb_upct_index_RESP = 3'h0;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			21'h0,
			11'h0
		};
	    // Update 1

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // RESP stage
		expected_upper_PC_RESP = 21'h0;
	    // Update 0
	    // Update 1
		expected_update1_upct_index = 3'h0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // RESP stage
		tb_valid_RESP = 1'b0;
		tb_upct_index_RESP = 3'h0;
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			21'h0,
			11'h0
		};
	    // Update 1

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // RESP stage
		expected_upper_PC_RESP = 21'h0;
	    // Update 0
	    // Update 1
		expected_update1_upct_index = 3'h0;

		check_outputs();

        // ------------------------------------------------------------
        // update miss chain:
        test_case = "update miss chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: 0x0, update1: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// RESP stage
		tb_valid_RESP = 1'b0;
		tb_upct_index_RESP = 3'h0;
		// Update 0
		tb_update0_valid = 1'b1;
		tb_update0_start_full_PC = {
			3'h0, {3{3'h7, 3'h0}},
			11'h0
		};
		// Update 1

		@(negedge CLK);

		// outputs:

		// RESP stage
		expected_upper_PC_RESP = 21'h0;
		// Update 0
		// Update 1
		expected_update1_upct_index = 3'h0;

		check_outputs();

		for (int i = 1; i < 8; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("update0: 0x%1h, update1: 0x%1h", i, i - 1);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// RESP stage
			tb_valid_RESP = 1'b0;
			tb_upct_index_RESP = 3'h0;
			// Update 0
			tb_update0_valid = 1'b1;
			tb_update0_start_full_PC = {
				i[2:0], {3{~i[2:0], i[2:0]}},
				11'h0
			};
			// Update 1

			@(negedge CLK);

			// outputs:

			// RESP stage
			expected_upper_PC_RESP = i == 1 ? 21'h0 : {3'h0, {3{3'h7, 3'h0}}};
			// Update 0
			// Update 1
			expected_update1_upct_index = first_pass_plru_mapping[i-1];

			check_outputs();
		end

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: NOP, update1: 0x7");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// RESP stage
		tb_valid_RESP = 1'b0;
		tb_upct_index_RESP = 3'h0;
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			21'h0,
			11'h0
		};
		// Update 1

		@(negedge CLK);

		// outputs:

		// RESP stage
		expected_upper_PC_RESP = {3'h0, {3{3'h7, 3'h0}}};
		// Update 0
		// Update 1
		expected_update1_upct_index = first_pass_plru_mapping[7];

		check_outputs();

        // ------------------------------------------------------------
        // read chain:
        test_case = "read chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 7; i >= 0; i--) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("RESP: 0x%1h", i[2:0]);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// RESP stage
			tb_valid_RESP = 1'b1;
			tb_upct_index_RESP = i[2:0];
			// Update 0
			tb_update0_valid = 1'b0;
			tb_update0_start_full_PC = {
				21'h0,
				11'h0
			};
			// Update 1

			@(negedge CLK);

			// outputs:

			// RESP stage
			expected_upper_PC_RESP = {first_pass_plru_mapping[i][2:0], {3{~first_pass_plru_mapping[i][2:0], first_pass_plru_mapping[i][2:0]}}};
			// Update 0
			// Update 1
			expected_update1_upct_index = i > 2 ? 3'h0 : 3'h7;

			check_outputs();
		end

        // ------------------------------------------------------------
        // update hit chain:
        test_case = "update hit chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: 0x0, update1: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// RESP stage
		tb_valid_RESP = 1'b0;
		tb_upct_index_RESP = 3'h0;
		// Update 0
		tb_update0_valid = 1'b1;
		tb_update0_start_full_PC = {
			3'h0, {3{3'h7, 3'h0}},
			11'h0
		};
		// Update 1

		@(negedge CLK);

		// outputs:

		// RESP stage
		expected_upper_PC_RESP = {3'h0, {3{3'h7, 3'h0}}};
		// Update 0
		// Update 1
		expected_update1_upct_index = 3'h7;

		check_outputs();

		for (int i = 1; i < 8; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("update0: 0x%1h, update1: 0x%1h", i, i - 1);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// RESP stage
			tb_valid_RESP = 1'b0;
			tb_upct_index_RESP = 3'h0;
			// Update 0
			tb_update0_valid = 1'b1;
			tb_update0_start_full_PC = {
				i[2:0], {3{~i[2:0], i[2:0]}},
				11'h0
			};
			// Update 1

			@(negedge CLK);

			// outputs:

			// RESP stage
			expected_upper_PC_RESP = {3'h0, {3{3'h7, 3'h0}}};
			// Update 0
			// Update 1
			expected_update1_upct_index = first_pass_plru_mapping[i-1];

			check_outputs();
		end

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: NOP, update1: 0x7");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// RESP stage
		tb_valid_RESP = 1'b0;
		tb_upct_index_RESP = 3'h0;
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			21'h0,
			11'h0
		};
		// Update 1

		@(negedge CLK);

		// outputs:

		// RESP stage
		expected_upper_PC_RESP = {3'h0, {3{3'h7, 3'h0}}};
		// Update 0
		// Update 1
		expected_update1_upct_index = first_pass_plru_mapping[7];

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