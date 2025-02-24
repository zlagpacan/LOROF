/*
    Filename: lht_tb.sv
    Author: zlagpacan
    Description: Testbench for lht module. 
    Spec: LOROF/spec/design/lht.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lht_tb ();

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


    // REQ stage
	logic tb_valid_REQ;
	logic [31:0] tb_full_PC_REQ;
	logic [ASID_WIDTH-1:0] tb_ASID_REQ;

    // RESP stage
	logic [LHT_ENTRIES_PER_BLOCK-1:0][LH_LENGTH-1:0] DUT_LH_by_instr_RESP, expected_LH_by_instr_RESP;

    // Update 0
	logic tb_update0_valid;
	logic [31:0] tb_update0_start_full_PC;
	logic [31:0] tb_update0_ASID;
	logic [LH_LENGTH-1:0] tb_update0_LH;

    // ----------------------------------------------------------------
    // DUT instantiation:

	lht DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // REQ stage
		.valid_REQ(tb_valid_REQ),
		.full_PC_REQ(tb_full_PC_REQ),
		.ASID_REQ(tb_ASID_REQ),

	    // RESP stage
		.LH_by_instr_RESP(DUT_LH_by_instr_RESP),

	    // Update
		.update0_valid(tb_update0_valid),
		.update0_start_full_PC(tb_update0_start_full_PC),
		.update0_ASID(tb_update0_ASID),
		.update0_LH(tb_update0_LH)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_LH_by_instr_RESP !== DUT_LH_by_instr_RESP) begin
			$display("TB ERROR: expected_LH_by_instr_RESP (%h) != DUT_LH_by_instr_RESP (%h)",
				expected_LH_by_instr_RESP, DUT_LH_by_instr_RESP);
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
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = 32'h0;
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Update
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
		tb_update0_ASID = 9'h0;
		tb_update0_LH = 8'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_LH_by_instr_RESP = '0;
	    // Update

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = 32'h0;
		tb_ASID_REQ = 9'h0;
	    // RESP stage
	    // Update
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
		tb_update0_ASID = 9'h0;
		tb_update0_LH = 8'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_LH_by_instr_RESP = '0;
	    // Update

		check_outputs();

        // ------------------------------------------------------------
        // update chain:
        test_case = "update chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		for (int i = 0; i < 256; i++) begin

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("update0: 0x%2h", i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b0;
			tb_full_PC_REQ = 32'h0;
			tb_ASID_REQ = 9'h0;
			// RESP stage
			// Update
			tb_update0_valid = 1'b1;
			tb_update0_start_full_PC = {
				24'h0, // lower tag bits
				i[7:3], // set index
				i[2:0], // within-block index
				1'b0 // 2B offset
			};
			tb_update0_ASID = {
				4'h0, // untouched bit
				i % 2 ? 5'b11111 : 5'b00000 // tag bits
			};
			tb_update0_LH = i[7:0];

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_LH_by_instr_RESP = '0;
			// Update

			check_outputs();
		end

        // ------------------------------------------------------------
        // read chain ASID 0 (evens):
        test_case = "read chain ASID 0 (evens)";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// fill cycle:
			// REQ: 0
			// RESP: NOP

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: 0x00, RESP: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b1;
		tb_full_PC_REQ = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			4'h0, // untouched bit
			5'b00000 // tag bits
		};
		// RESP stage
		// Update
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			4'h0, // untouched bit
			5'b00000 // tag bits
		};
		tb_update0_LH = 8'h0;

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_LH_by_instr_RESP = '0;
		// Update

		check_outputs();

		// main loop:
			// REQ: i
			// RESP: i - 1

		for (int i = 8; i < 256; i += 8) begin
			automatic int last_i = i - 8;

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("REQ: 0x%2h, RESP: 0x%2h", i, last_i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b1;
			tb_full_PC_REQ = {
				24'h0, // lower tag bits
				i[7:3], // set index
				i[2:0], // within-block index
				1'b0 // 2B offset
			};
			tb_ASID_REQ = {
				4'h0, // untouched bit
				5'b00000 // tag bits
			};
			// RESP stage
			// Update
			tb_update0_valid = 1'b0;
			tb_update0_start_full_PC = {
				24'h0, // lower tag bits
				5'b00000, // set index
				3'h0, // within-block index
				1'b0 // 2B offset
			};
			tb_update0_ASID = {
				4'h0, // untouched bit
				5'b00000 // tag bits
			};
			tb_update0_LH = 8'h0;

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_LH_by_instr_RESP = {
				~{last_i + 0}[7:0],
				{last_i + 6}[7:0],
				~{last_i + 2}[7:0],
				{last_i + 4}[7:0],
				~{last_i + 4}[7:0],
				{last_i + 2}[7:0],
				~{last_i + 6}[7:0],
				{last_i + 0}[7:0]
			};
			// Update

			check_outputs();
		end

		// drain cycle:
			// REQ: NOP
			// RESP: ff

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: NOP, RESP: 0xf8");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			4'h0, // untouched bit
			5'b11111 // tag bits
		};
		// RESP stage
		// Update
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			4'h0, // untouched bit
			5'b00000 // tag bits
		};
		tb_update0_LH = 8'h0;

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_LH_by_instr_RESP = {
			8'h07,
			8'hfe,
			8'h05,
			8'hfc,
			8'h03,
			8'hfa,
			8'h01,
			8'hf8
		};
		// Update

		check_outputs();

        // ------------------------------------------------------------
        // read chain ASID 1 (odds):
        test_case = "read chain ASID 1 (odds)";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// fill cycle:
			// REQ: 0
			// RESP: NOP

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: 0x00, RESP: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b1;
		tb_full_PC_REQ = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			4'h0, // untouched bit
			5'b11111 // tag bits
		};
		// RESP stage
		// Update
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			4'h0, // untouched bit
			5'b00000 // tag bits
		};
		tb_update0_LH = 8'h0;

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_LH_by_instr_RESP = {
			8'h07,
			8'hfe,
			8'h05,
			8'hfc,
			8'h03,
			8'hfa,
			8'h01,
			8'hf8
		};
		// Update

		check_outputs();

		// main loop:
			// REQ: i
			// RESP: i - 1

		for (int i = 8; i < 256; i += 8) begin
			automatic int last_i = i - 8;

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf("REQ: 0x%2h, RESP: 0x%2h", i, last_i);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b1;
			tb_full_PC_REQ = {
				24'h0, // lower tag bits
				i[7:3], // set index
				i[2:0], // within-block index
				1'b0 // 2B offset
			};
			tb_ASID_REQ = {
				4'h0, // untouched bit
				5'b11111 // tag bits
			};
			// RESP stage
			// Update
			tb_update0_valid = 1'b0;
			tb_update0_start_full_PC = {
				24'h0, // lower tag bits
				5'b00000, // set index
				3'h0, // within-block index
				1'b0 // 2B offset
			};
			tb_update0_ASID = {
				4'h0, // untouched bit
				5'b00000 // tag bits
			};
			tb_update0_LH = 8'h0;

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_LH_by_instr_RESP = {
				{last_i + 7}[7:0],
				~{last_i + 1}[7:0],
				{last_i + 5}[7:0],
				~{last_i + 3}[7:0],
				{last_i + 3}[7:0],
				~{last_i + 5}[7:0],
				{last_i + 1}[7:0],
				~{last_i + 7}[7:0]
			};
			// Update

			check_outputs();
		end

		// drain cycle:
			// REQ: NOP
			// RESP: ff

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: NOP, RESP: 0xf8");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b1;
		tb_full_PC_REQ = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			4'h0, // untouched bit
			5'b11111 // tag bits
		};
		// RESP stage
		// Update
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			24'h0, // lower tag bits
			5'b00000, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			4'h0, // untouched bit
			5'b00000 // tag bits
		};
		tb_update0_LH = 8'h0;

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_LH_by_instr_RESP = {
			8'hff,
			8'h06,
			8'hfd,
			8'h04,
			8'hfb,
			8'h02,
			8'hf9,
			8'h00
		};
		// Update

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