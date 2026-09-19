/*
    Filename: pmux_lsb_for_tb.sv
    Author: zlagpacan
    Description: Testbench for pmux_lsb_for module. 
    Spec: LOROF/spec/design/pmux_lsb_for.md
*/

`timescale 1ns/100ps


module pmux_lsb_for_tb #(
	parameter int unsigned SEL_WIDTH = 8,
	parameter int unsigned DATA_WIDTH = 8
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
	logic [SEL_WIDTH-1:0] tb_req_valid_vec;
	logic [SEL_WIDTH-1:0][DATA_WIDTH-1:0] tb_req_data_vec;

	logic [DATA_WIDTH-1:0] DUT_rsp_data, expected_rsp_data;

    // ----------------------------------------------------------------
    // DUT instantiation:

	pmux_lsb_for #(
		.SEL_WIDTH(SEL_WIDTH),
		.DATA_WIDTH(DATA_WIDTH)
	) DUT (
		.req_valid_vec(tb_req_valid_vec),
		.req_data_vec(tb_req_data_vec),

		.rsp_data(DUT_rsp_data)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_rsp_data !== DUT_rsp_data) begin
			$display("TB ERROR: expected_rsp_data (%0d'h%h) != DUT_rsp_data (%0d'h%h)",
				$bits(expected_rsp_data), expected_rsp_data,
				$bits(DUT_rsp_data), DUT_rsp_data);
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
		tb_req_valid_vec = 8'b00000000;
		tb_req_data_vec = {
            8'h87,
            8'h96,
            8'ha5,
            8'hb4,
            8'hc3,
            8'hd2,
            8'he1,
            8'hf0
        };

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_rsp_data = 8'h87;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_req_valid_vec = 8'b00000000;
		tb_req_data_vec = {
            8'h87,
            8'h96,
            8'ha5,
            8'hb4,
            8'hc3,
            8'hd2,
            8'he1,
            8'hf0
        };

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_rsp_data = 8'h87;

		check_outputs();

        // ------------------------------------------------------------
        // exhaustive sel:
        test_case = "exhaustive sel";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

        for (int i = 0; i < 2**SEL_WIDTH; i++) begin

            @(posedge CLK); #(PERIOD/10);

            // inputs
            sub_test_case = $sformatf("req_valid_vec = %0b", i[7:0]);
            $display("\t- sub_test: %s", sub_test_case);

            // reset
            nRST = 1'b1;
            tb_req_valid_vec = i[7:0];
            tb_req_data_vec = {
                8'h87,
                8'h96,
                8'ha5,
                8'hb4,
                8'hc3,
                8'hd2,
                8'he1,
                8'hf0
            };

            @(negedge CLK);

            // outputs:

            expected_rsp_data = 
                i[0] ? 8'hf0 :
                i[1] ? 8'he1 : 
                i[2] ? 8'hd2 : 
                i[3] ? 8'hc3 : 
                i[4] ? 8'hb4 : 
                i[5] ? 8'ha5 : 
                i[6] ? 8'h96 : 
                i[7] ? 8'h87 : 
                8'h87
            ;

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