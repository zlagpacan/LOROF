/*
    Filename: id_tracker_tb.sv
    Author: zlagpacan
    Description: Testbench for id_tracker module. 
    Spec: LOROF/spec/design/id_tracker.md
*/

`timescale 1ns/100ps


module id_tracker_tb #(
	parameter int unsigned ID_COUNT = 4,
	parameter int unsigned ID_WIDTH = $clog2(ID_COUNT)
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

    // new id dispatch
	logic tb_new_id_consume;
	logic DUT_new_id_ready, expected_new_id_ready;
	logic [ID_WIDTH-1:0] DUT_new_id, expected_new_id;

    // old id retirement
	logic tb_old_id_done;
	logic [ID_WIDTH-1:0] tb_old_id;

    // ----------------------------------------------------------------
    // DUT instantiation:

	id_tracker #(
		.ID_COUNT(ID_COUNT),
		.ID_WIDTH(ID_WIDTH)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // new id dispatch
		.new_id_consume(tb_new_id_consume),
		.new_id_ready(DUT_new_id_ready),
		.new_id(DUT_new_id),

	    // old id retirement
		.old_id_done(tb_old_id_done),
		.old_id(tb_old_id)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_new_id_ready !== DUT_new_id_ready) begin
			$display("TB ERROR: expected_new_id_ready (%h) != DUT_new_id_ready (%h)",
				expected_new_id_ready, DUT_new_id_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_new_id !== DUT_new_id) begin
			$display("TB ERROR: expected_new_id (%h) != DUT_new_id (%h)",
				expected_new_id, DUT_new_id);
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
	    // new id dispatch
		tb_new_id_consume = 1'b0;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 0;
	    // old id retirement

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b0;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 0;
	    // old id retirement

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, v, v, v}, consume 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 0;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, v, v, i}, consume 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 1;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, v, i, i}, consume 2, 1 done";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b1;
		tb_old_id = 1;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 2;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, i, v, i}, consume 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 1;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, i, i, i}, consume 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 3;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i}";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b0;
		expected_new_id = 3; // none present -> '1
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i}, 3 done";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b1;
		tb_old_id = 3;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b0;
		expected_new_id = 3; // none present -> '1
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, i, i, i}, 0 done";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b0;
	    // old id retirement
		tb_old_id_done = 1'b1;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 3;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, i, i, v}, 2 done, consume 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b1;
		tb_old_id = 2;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 0;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, v, i, i}, consume 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 2;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 2;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{v, i, i, i}, consume 3";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 2;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 3;
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, i}, fail consume 0, 0 done";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b1;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b0;
		expected_new_id = 3; // none present -> '1
	    // old id retirement

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "{i, i, i, v}, consume 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // new id dispatch
		tb_new_id_consume = 1'b1;
	    // old id retirement
		tb_old_id_done = 1'b0;
		tb_old_id = 0;

		@(negedge CLK);

		// outputs:

	    // new id dispatch
		expected_new_id_ready = 1'b1;
		expected_new_id = 0;
	    // old id retirement

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
            $display("FAIL: %0d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule