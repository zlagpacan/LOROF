/*
    Filename: btb_tb.sv
    Author: zlagpacan
    Description: Testbench for btb module. 
    Spec: LOROF/spec/design/btb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb_tb ();

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
	logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_PRED_INFO_WIDTH-1:0] DUT_pred_info_by_instr_RESP, expected_pred_info_by_instr_RESP;
	logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0] DUT_pred_lru_by_instr_RESP, expected_pred_lru_by_instr_RESP;
	logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_TARGET_WIDTH-1:0] DUT_target_by_instr_RESP, expected_target_by_instr_RESP;

    // Update 0
	logic tb_update0_valid;
	logic [31:0] tb_update0_start_full_PC;
	logic [ASID_WIDTH-1:0] tb_update0_ASID;

    // Update 1
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_update1_pred_info;
	logic tb_update1_pred_lru;
	logic [31:0] tb_update1_target_full_PC;

    // ----------------------------------------------------------------
    // DUT instantiation:

	btb DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // REQ stage
		.valid_REQ(tb_valid_REQ),
		.full_PC_REQ(tb_full_PC_REQ),
		.ASID_REQ(tb_ASID_REQ),

	    // RESP stage
		.pred_info_by_instr_RESP(DUT_pred_info_by_instr_RESP),
		.pred_lru_by_instr_RESP(DUT_pred_lru_by_instr_RESP),
		.target_by_instr_RESP(DUT_target_by_instr_RESP),

	    // Update 0
		.update0_valid(tb_update0_valid),
		.update0_start_full_PC(tb_update0_start_full_PC),
		.update0_ASID(tb_update0_ASID),

	    // Update 1
		.update1_pred_info(tb_update1_pred_info),
		.update1_pred_lru(tb_update1_pred_lru),
		.update1_target_full_PC(tb_update1_target_full_PC)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin

		if (expected_pred_info_by_instr_RESP !== DUT_pred_info_by_instr_RESP) begin
			$display("TB ERROR: expected_pred_info_by_instr_RESP (%h) != DUT_pred_info_by_instr_RESP (%h)",
				expected_pred_info_by_instr_RESP, DUT_pred_info_by_instr_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pred_lru_by_instr_RESP !== DUT_pred_lru_by_instr_RESP) begin
			$display("TB ERROR: expected_pred_lru_by_instr_RESP (%h) != DUT_pred_lru_by_instr_RESP (%h)",
				expected_pred_lru_by_instr_RESP, DUT_pred_lru_by_instr_RESP);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_target_by_instr_RESP !== DUT_target_by_instr_RESP) begin
			$display("TB ERROR: expected_target_by_instr_RESP (%h) != DUT_target_by_instr_RESP (%h)",
				expected_target_by_instr_RESP, DUT_target_by_instr_RESP);
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
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
		tb_update0_ASID = 9'h0;
	    // Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {8{10'h0}};
	    // Update 0
	    // Update 1

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
	    // Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = 32'h0;
		tb_update0_ASID = 9'h0;
	    // Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = 32'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // REQ stage
	    // RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {8{10'h0}};
	    // Update 0
	    // Update 1

		check_outputs();

        // ------------------------------------------------------------
        // update chain way 0:
        test_case = "update chain way 0";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// fill pipe:
			// update0: 0
			// update1: NOP

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: 0x000, update1: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b1;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b010000, // upper tag bits
			6'b000001, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000100 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {8{10'h0}};
		// Update 0
		// Update 1

		check_outputs();

		// main loop:
			// update0: i
			// update1: i-1

		for (int i = 1; i <= 2047; i++) begin
			automatic int last_i = i-1;

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf(
				"update0: 0x%3h, update1: 0x%3h",
				i, last_i
			);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b0;
			tb_full_PC_REQ = {
				8'h0, // untouched bits
				6'b000000, // upper tag bits
				6'b000000, // lower tag bits
				8'h0, // set index
				3'h0, // within-block index
				1'b0 // 2B offset
			};
			tb_ASID_REQ = {
				3'h0, // untouched bits
				6'b000000 // tag bits
			};
			// RESP stage
			// Update 0
			tb_update0_valid = 1'b1;
			tb_update0_start_full_PC = {
				i[7:0], // untouched bits
				6'b010000, // upper tag bits
				6'b000001, // lower tag bits
				i[10:3], // set index
				i[2:0], // within-block index
				i[0] // 2B offset
			};
			tb_update0_ASID = {
				i[2:0], // untouched bits
				6'b000100 // tag bits
			};
			// Update 1
			tb_update1_pred_info = last_i[7:0];
			tb_update1_pred_lru = 1'b0;
			tb_update1_target_full_PC = {
				last_i[20:0], // untouched bits
				last_i[9:0], // target bits
				last_i[0] // 2B offset
			};

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_pred_info_by_instr_RESP = {8{8'h0}};
			expected_pred_lru_by_instr_RESP = {8{1'b0}};
			expected_target_by_instr_RESP = {8{10'h0}};
			// Update 0
			// Update 1

			check_outputs();
		end

		// drain pipe:
			// update0: NOP
			// update1: 2047

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: NOP, update1: 0x7ff");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'b11111111;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h3ff, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {8{10'h0}};
		// Update 0
		// Update 1

		check_outputs();

        // ------------------------------------------------------------
        // read chain way 0:
        test_case = "read chain way 0";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// fill pipe:
			// REQ: 0
			// RESP: NOP

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: 0x000, RESP: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b1;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b010000, // upper tag bits
			6'b000001, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000100 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {8{10'h0}};
		// Update 0
		// Update 1

		check_outputs();

		// main loop:
			// REQ: i
			// RESP: i-1

		for (int i = 8; i <= 2047; i += 8) begin
			automatic int last_i = i-8;

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf(
				"REQ: 0x%3h, RESP: 0x%3h",
				i, last_i
			);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b1;
			tb_full_PC_REQ = {
				i[7:0], // untouched bits
				6'b010000, // upper tag bits
				6'b000001, // lower tag bits
				i[10:3], // set index
				i[2:0], // within-block index
				i[0] // 2B offset
			};
			tb_ASID_REQ = {
				i[2:0], // untouched bits
				6'b000100 // tag bits
			};
			// RESP stage
			// Update 0
			tb_update0_valid = 1'b0;
			tb_update0_start_full_PC = {
				8'h0, // untouched bits
				6'b000000, // upper tag bits
				6'b000000, // lower tag bits
				8'h0, // set index
				3'h0, // within-block index
				1'b0 // 2B offset
			};
			tb_update0_ASID = {
				3'h0, // untouched bits
				6'b000000 // tag bits
			};
			// Update 1
			tb_update1_pred_info = 8'h0;
			tb_update1_pred_lru = 1'b0;
			tb_update1_target_full_PC = {
				21'h0, // untouched bits
				10'h0, // target bits
				1'b0 // 2B offset
			};

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_pred_info_by_instr_RESP = {
				{last_i + 7}[7:0],
				{last_i + 6}[7:0],
				{last_i + 5}[7:0],
				{last_i + 4}[7:0],
				{last_i + 3}[7:0],
				{last_i + 2}[7:0],
				{last_i + 1}[7:0],
				{last_i + 0}[7:0]
			};
			expected_pred_lru_by_instr_RESP = {8{1'b0}};
			expected_target_by_instr_RESP = {
				{last_i + 7}[9:0],
				{last_i + 6}[9:0],
				{last_i + 5}[9:0],
				{last_i + 4}[9:0],
				{last_i + 3}[9:0],
				{last_i + 2}[9:0],
				{last_i + 1}[9:0],
				{last_i + 0}[9:0]
			};

			if (i == 8) begin
				expected_pred_info_by_instr_RESP = {
					8'h7,
					8'h6,
					8'h5,
					8'h4,
					8'h3,
					8'h2,
					8'h1,
					8'h0
				};
				expected_pred_lru_by_instr_RESP = {8{1'b0}};
				expected_target_by_instr_RESP = {
					10'h7,
					10'h6,
					10'h5,
					10'h4,
					10'h3,
					10'h2,
					10'h1,
					10'h0
				};
			end
			// Update 0
			// Update 1

			check_outputs();
		end

		// drain pipe:
			// REQ: NOP
			// RESP: 2047

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: NOP, RESP: 0x7f8");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {
			8'hff,
			8'hfe,
			8'hfd,
			8'hfc,
			8'hfb,
			8'hfa,
			8'hf9,
			8'hf8
		};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {
			10'h3ff,
			10'h3fe,
			10'h3fd,
			10'h3fc,
			10'h3fb,
			10'h3fa,
			10'h3f9,
			10'h3f8
		};
		// Update 0
		// Update 1

		check_outputs();

        // ------------------------------------------------------------
        // update chain way 1:
        test_case = "update chain way 1";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// fill pipe:
			// update0: 0
			// update1: NOP

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: 0x000, update1: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b1;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b100000, // upper tag bits
			6'b000010, // lower tag bits
			8'h0, // set index
			3'h7, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b001000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b1}};
		expected_target_by_instr_RESP = {8{10'h0}};
		// Update 0
		// Update 1

		check_outputs();

		// main loop:
			// update0: i
			// update1: i-1

		for (int i = 1; i <= 2047; i++) begin
			automatic int last_i = i-1;

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf(
				"update0: 0x%3h, update1: 0x%3h",
				i, last_i
			);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b0;
			tb_full_PC_REQ = {
				8'h0, // untouched bits
				6'b000000, // upper tag bits
				6'b000000, // lower tag bits
				8'h0, // set index
				3'h0, // within-block index
				1'b0 // 2B offset
			};
			tb_ASID_REQ = {
				3'h0, // untouched bits
				6'b000000 // tag bits
			};
			// RESP stage
			// Update 0
			tb_update0_valid = 1'b1;
			tb_update0_start_full_PC = {
				i[7:0], // untouched bits
				6'b100000, // upper tag bits
				6'b000010, // lower tag bits
				i[10:3], // set index
				~i[2:0], // within-block index
				i[0] // 2B offset
			};
			tb_update0_ASID = {
				i[2:0], // untouched bits
				6'b001000 // tag bits
			};
			// Update 1
			tb_update1_pred_info = ~last_i[7:0];
			tb_update1_pred_lru = 1'b1;
			tb_update1_target_full_PC = {
				last_i[20:0], // untouched bits
				~last_i[9:0], // target bits
				last_i[0] // 2B offset
			};

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_pred_info_by_instr_RESP = {8{8'h0}};
			expected_pred_lru_by_instr_RESP = {8{1'b1}};
			expected_target_by_instr_RESP = {8{10'h0}};
			// Update 0
			// Update 1

			check_outputs();
		end

		// drain pipe:
			// update0: NOP
			// update1: 2047

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("update0: NOP, update1: 0x7ff");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b100000, // upper tag bits
			6'b000010, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b001000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'b00000000;
		tb_update1_pred_lru = 1'b1;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h000, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b1}};
		expected_target_by_instr_RESP = {8{10'h0}};
		// Update 0
		// Update 1

		check_outputs();

        // ------------------------------------------------------------
        // read chain way 1:
        test_case = "read chain way 1";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// fill pipe:
			// REQ: 0
			// RESP: NOP

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: 0x000, RESP: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b1;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b100000, // upper tag bits
			6'b000010, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b001000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {8{8'h0}};
		expected_pred_lru_by_instr_RESP = {8{1'b1}};
		expected_target_by_instr_RESP = {8{10'h0}};
		// Update 0
		// Update 1

		check_outputs();

		// main loop:
			// REQ: i
			// RESP: i-1

		for (int i = 8; i <= 2047; i += 8) begin
			automatic int last_i = i-8;

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf(
				"REQ: 0x%3h, RESP: 0x%3h",
				i, last_i
			);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b1;
			tb_full_PC_REQ = {
				i[7:0], // untouched bits
				6'b100000, // upper tag bits
				6'b000010, // lower tag bits
				i[10:3], // set index
				~i[2:0], // within-block index
				i[0] // 2B offset
			};
			tb_ASID_REQ = {
				i[2:0], // untouched bits
				6'b001000 // tag bits
			};
			// RESP stage
			// Update 0
			tb_update0_valid = 1'b0;
			tb_update0_start_full_PC = {
				8'h0, // untouched bits
				6'b000000, // upper tag bits
				6'b000000, // lower tag bits
				8'h0, // set index
				3'h0, // within-block index
				1'b0 // 2B offset
			};
			tb_update0_ASID = {
				3'h0, // untouched bits
				6'b000000 // tag bits
			};
			// Update 1
			tb_update1_pred_info = 8'h0;
			tb_update1_pred_lru = 1'b0;
			tb_update1_target_full_PC = {
				21'h0, // untouched bits
				10'h0, // target bits
				1'b0 // 2B offset
			};

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_pred_info_by_instr_RESP = {
				~{last_i + 0}[7:0],
				~{last_i + 1}[7:0],
				~{last_i + 2}[7:0],
				~{last_i + 3}[7:0],
				~{last_i + 4}[7:0],
				~{last_i + 5}[7:0],
				~{last_i + 6}[7:0],
				~{last_i + 7}[7:0]
			};
			expected_pred_lru_by_instr_RESP = {8{1'b1}};
			expected_target_by_instr_RESP = {
				~{last_i + 0}[9:0],
				~{last_i + 1}[9:0],
				~{last_i + 2}[9:0],
				~{last_i + 3}[9:0],
				~{last_i + 4}[9:0],
				~{last_i + 5}[9:0],
				~{last_i + 6}[9:0],
				~{last_i + 7}[9:0]
			};

			// Update 0
			// Update 1

			check_outputs();
		end

		// drain pipe:
			// REQ: NOP
			// RESP: 2047

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: NOP, RESP: 0x7f8");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = ~8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			~10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {
			~8'hf8,
			~8'hf9,
			~8'hfa,
			~8'hfb,
			~8'hfc,
			~8'hfd,
			~8'hfe,
			~8'hff
		};
		expected_pred_lru_by_instr_RESP = {8{1'b1}};
		expected_target_by_instr_RESP = {
			~10'h3f8,
			~10'h3f9,
			~10'h3fa,
			~10'h3fb,
			~10'h3fc,
			~10'h3fd,
			~10'h3fe,
			~10'h3ff
		};
		// Update 0
		// Update 1

		check_outputs();

        // ------------------------------------------------------------
        // read chain nonexistent way:
        test_case = "read chain nonexistent way";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// fill pipe:
			// REQ: 0
			// RESP: NOP

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: 0x000, RESP: NOP");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b1;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b110000, // upper tag bits
			6'b000011, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b001100 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = 8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {
			8'h3f,
			8'h3e,
			8'h3d,
			8'h3c,
			8'h3b,
			8'h3a,
			8'h39,
			8'h38
		};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {
			10'h3ff,
			10'h3fe,
			10'h3fd,
			10'h3fc,
			10'h3fb,
			10'h3fa,
			10'h3f9,
			10'h3f8
		};
		// Update 0
		// Update 1

		check_outputs();

		// main loop:
			// REQ: i
			// RESP: i-1

		for (int i = 8; i <= 2047; i += 8) begin
			automatic int last_i = i-8;

			@(posedge CLK); #(PERIOD/10);

			// inputs
			sub_test_case = $sformatf(
				"REQ: 0x%3h, RESP: 0x%3h",
				i, last_i
			);
			$display("\t- sub_test: %s", sub_test_case);

			// reset
			nRST = 1'b1;
			// REQ stage
			tb_valid_REQ = 1'b1;
			tb_full_PC_REQ = {
				i[7:0], // untouched bits
				6'b110000, // upper tag bits
				6'b000011, // lower tag bits
				i[10:3], // set index
				i[2:0], // within-block index
				i[0] // 2B offset
			};
			tb_ASID_REQ = {
				i[2:0], // untouched bits
				6'b001100 // tag bits
			};
			// RESP stage
			// Update 0
			tb_update0_valid = 1'b0;
			tb_update0_start_full_PC = {
				8'h0, // untouched bits
				6'b000000, // upper tag bits
				6'b000000, // lower tag bits
				8'h0, // set index
				3'h0, // within-block index
				1'b0 // 2B offset
			};
			tb_update0_ASID = {
				3'h0, // untouched bits
				6'b000000 // tag bits
			};
			// Update 1
			tb_update1_pred_info = 8'h0;
			tb_update1_pred_lru = 1'b0;
			tb_update1_target_full_PC = {
				21'h0, // untouched bits
				10'h0, // target bits
				1'b0 // 2B offset
			};

			@(negedge CLK);

			// outputs:

			// REQ stage
			// RESP stage
			expected_pred_info_by_instr_RESP = {
				2'b00, {last_i + 7}[5:0],
				2'b00, {last_i + 6}[5:0],
				2'b00, {last_i + 5}[5:0],
				2'b00, {last_i + 4}[5:0],
				2'b00, {last_i + 3}[5:0],
				2'b00, {last_i + 2}[5:0],
				2'b00, {last_i + 1}[5:0],
				2'b00, {last_i + 0}[5:0]
			};
			expected_pred_lru_by_instr_RESP = {8{1'b0}};
			expected_target_by_instr_RESP = {
				{last_i + 7}[9:0],
				{last_i + 6}[9:0],
				{last_i + 5}[9:0],
				{last_i + 4}[9:0],
				{last_i + 3}[9:0],
				{last_i + 2}[9:0],
				{last_i + 1}[9:0],
				{last_i + 0}[9:0]
			};

			// Update 0
			// Update 1

			check_outputs();
		end

		// drain pipe:
			// REQ: NOP
			// RESP: 2047

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = $sformatf("REQ: NOP, RESP: 0x7f8");
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
		// REQ stage
		tb_valid_REQ = 1'b0;
		tb_full_PC_REQ = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_ASID_REQ = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// RESP stage
		// Update 0
		tb_update0_valid = 1'b0;
		tb_update0_start_full_PC = {
			8'h0, // untouched bits
			6'b000000, // upper tag bits
			6'b000000, // lower tag bits
			8'h0, // set index
			3'h0, // within-block index
			1'b0 // 2B offset
		};
		tb_update0_ASID = {
			3'h0, // untouched bits
			6'b000000 // tag bits
		};
		// Update 1
		tb_update1_pred_info = ~8'h0;
		tb_update1_pred_lru = 1'b0;
		tb_update1_target_full_PC = {
			21'h0, // untouched bits
			~10'h0, // target bits
			1'b0 // 2B offset
		};

		@(negedge CLK);

		// outputs:

		// REQ stage
		// RESP stage
		expected_pred_info_by_instr_RESP = {
			8'h3f,
			8'h3e,
			8'h3d,
			8'h3c,
			8'h3b,
			8'h3a,
			8'h39,
			8'h38
		};
		expected_pred_lru_by_instr_RESP = {8{1'b0}};
		expected_target_by_instr_RESP = {
			10'h3ff,
			10'h3fe,
			10'h3fd,
			10'h3fc,
			10'h3fb,
			10'h3fa,
			10'h3f9,
			10'h3f8
		};
		// Update 0
		// Update 1

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