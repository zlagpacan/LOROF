/*
    Filename: alu_tb.sv
    Author: zlagpacan
    Description: Testbench for alu module. 
    Spec: LOROF/spec/design/alu.md
*/

`timescale 1ns/100ps

`include "instrp.vh"

module alu_tb #(
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
	instrp::alu_op_t tb_op;
	logic [63:0] tb_A;
	logic [63:0] tb_B;

	logic [63:0] DUT_out, expected_out;

    // ----------------------------------------------------------------
    // DUT instantiation:

	alu #(
	) DUT (
		.op(tb_op),
		.A(tb_A),
		.B(tb_B),

		.out(DUT_out)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_out !== DUT_out) begin
			$display("TB ERROR: expected_out (%h) != DUT_out (%h)",
				expected_out, DUT_out);
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
		tb_op = '0;
		tb_A = '0;
		tb_B = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_out = '0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = '0;
		tb_A = '0;
		tb_B = '0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

		expected_out = '0;

		check_outputs();

        // ------------------------------------------------------------
        // manual ops:
        test_case = "manual ops";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ADD 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_ADD;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h123456789abcdef0;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h13579be02468acdf;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ADD 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_ADD;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'hffffffffffffffff;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0123456789abcdee;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLL 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLL;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h5;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h2468acf13579bde0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLL 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLL;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h3535353535353535;

		@(negedge CLK);

		// outputs:

		expected_out = 64'hbde0000000000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLT 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLT;
		tb_A = 64'hff000000000000ff;
		tb_B = 64'h00ffffffffffff00;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0000000000000001;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLT 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLT;
		tb_A = 64'h00ffffffffffff00;
		tb_B = 64'hff000000000000ff;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0000000000000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLTU 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLTU;
		tb_A = 64'hff000000000000ff;
		tb_B = 64'h00ffffffffffff00;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0000000000000000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLTU 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLTU;
		tb_A = 64'h00ffffffffffff00;
		tb_B = 64'hff000000000000ff;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0000000000000001;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "XOR 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_XOR;
		tb_A = 64'h3535353535353535;
		tb_B = 64'h5353535353535353;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h6666666666666666;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRL 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRL;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h5;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h00091a2b3c4d5e6f;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRL 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRL;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h3535353535353535;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0000000000000009;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "OR 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_OR;
		tb_A = 64'h3535353535353535;
		tb_B = 64'h5353535353535353;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h7777777777777777;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "AND 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_AND;
		tb_A = 64'h3535353535353535;
		tb_B = 64'h5353535353535353;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h1111111111111111;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SUB 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SUB;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h123456789abcdef0;

		@(negedge CLK);

		// outputs:

		expected_out = 64'heeeeeeeeeeeeeeff;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SUB 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SUB;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'hffffffffffffffff;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0123456789abcdf0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRA 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRA;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h5;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h00091a2b3c4d5e6f;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRA 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRA;
		tb_A = 64'h8123456789abcdef;
		tb_B = 64'h3535353535353535;

		@(negedge CLK);

		// outputs:

		expected_out = 64'hfffffffffffffc09;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ADDW 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_ADDW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h123456789abcdef0;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h000000002468acdf;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "ADDW 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_ADDW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'hffffffffffffffff;

		@(negedge CLK);

		// outputs:

		expected_out = 64'hffffffff89abcdee;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SUBW 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SUBW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h123456789abcdef0;

		@(negedge CLK);

		// outputs:

		expected_out = 64'hffffffffeeeeeeff;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SUBW 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SUBW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'hffffffff0fffffff;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0000000079abcdf0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLLW 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLLW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h5;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h000000003579bde0;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SLLW 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SLLW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h3535353535353535;

		@(negedge CLK);

		// outputs:

		expected_out = 64'hffffffffbde00000;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRLW 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRLW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h5;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h00000000044d5e6f;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRLW 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRLW;
		tb_A = 64'h0123456789abcdef;
		tb_B = 64'h3535353535353535;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h000000000000044d;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRAW 0";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRAW;
		tb_A = 64'h00123456789abcde;
		tb_B = 64'h5;

		@(negedge CLK);

		// outputs:

		expected_out = 64'h0000000003c4d5e6;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "SRAW 1";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		tb_op = instrp::ALU_SRAW;
		tb_A = 64'h8123456789abcdef;
		tb_B = 64'h3535353535353535;

		@(negedge CLK);

		// outputs:

		expected_out = 64'hfffffffffffffc4d;

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