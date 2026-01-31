/*
    Filename: bcb_tb.sv
    Author: zlagpacan
    Description: Testbench for bcb module. 
    Spec: LOROF/spec/design/bcb.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module bcb_tb #(
) ();

    // ----------------------------------------------------------------
    // TB setup:

    // parameters
    parameter int unsigned PERIOD = 10;

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


    // save control
	logic tb_save_valid;
	corep::bcb_info_t tb_save_bcb_info;

	corep::bcb_idx_t DUT_save_bcb_index, expected_save_bcb_index;

    // restore control
	corep::bcb_idx_t tb_restore_bcb_index;

	corep::bcb_info_t DUT_restore_bcb_info, expected_restore_bcb_info;

    // ----------------------------------------------------------------
    // DUT instantiation:

	bcb #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // save control
		.save_valid(tb_save_valid),
		.save_bcb_info(tb_save_bcb_info),

		.save_bcb_index(DUT_save_bcb_index),

	    // restore control
		.restore_bcb_index(tb_restore_bcb_index),

		.restore_bcb_info(DUT_restore_bcb_info)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_save_bcb_index !== DUT_save_bcb_index) begin
			$display("TB ERROR: expected_save_bcb_index (%h) != DUT_save_bcb_index (%h)",
				expected_save_bcb_index, DUT_save_bcb_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restore_bcb_info !== DUT_restore_bcb_info) begin
			$display("TB ERROR: expected_restore_bcb_info (%h) != DUT_restore_bcb_info (%h)",
				expected_restore_bcb_info, DUT_restore_bcb_info);
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
	    // save control
		tb_save_valid = 1'b0;
		tb_save_bcb_info = 0;
	    // restore control
		tb_restore_bcb_index = 4'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // save control
		expected_save_bcb_index = 4'h0;
	    // restore control
		expected_restore_bcb_info = 0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // save control
		tb_save_valid = 1'b0;
		tb_save_bcb_info = 0;
	    // restore control
		tb_restore_bcb_index = 4'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // save control
		expected_save_bcb_index = 4'h0;
	    // restore control
		expected_restore_bcb_info = 0;

		check_outputs();

        // ------------------------------------------------------------
        // save 0:15:
        test_case = "save 0:15";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 16; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("save %1h", i);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // save control
            tb_save_valid = 1'b1;
            tb_save_bcb_info = {8{~i[3:0], i[3:0]}};
            // restore control
            tb_restore_bcb_index = 4'h0;

            @(negedge CLK);

            // outputs:

            // save control
            expected_save_bcb_index = i[3:0];
            // restore control
            expected_restore_bcb_info = i > 0 ? 32'hf0f0f0f0 : 0;

            check_outputs();
        end

        for (int i = 0; i < 16; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("read %1h, save %2h", i, i+16);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // save control
            tb_save_valid = 1'b1;
            tb_save_bcb_info = {{2{~{i+16}[3:0], {i+16}[3:0]}}, ~{i+16}[3:0], {i+16}[3:0]};
            // restore control
            tb_restore_bcb_index = i[3:0];

            @(negedge CLK);

            // outputs:

            // save control
            expected_save_bcb_index = i[3:0];
            // restore control
            expected_restore_bcb_info = {{2{~i[3:0], i[3:0]}}, ~i[3:0], i[3:0]};

            check_outputs();
        end

        for (int i = 0; i < 16; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("read %1h", i+16);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            // save control
            tb_save_valid = 1'b1;
            tb_save_bcb_info = {13'h0000, 4'h0, 4'h0};
            // restore control
            tb_restore_bcb_index = i[3:0];

            @(negedge CLK);

            // outputs:

            // save control
            expected_save_bcb_index = i[3:0];
            // restore control
            expected_restore_bcb_info = {{2{~{i+16}[3:0], {i+16}[3:0]}}, ~{i+16}[3:0], {i+16}[3:0]};

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