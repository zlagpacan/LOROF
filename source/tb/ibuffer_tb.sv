/*
    Filename: ibuffer_tb.sv
    Author: zlagpacan
    Description: Testbench for ibuffer module. 
    Spec: LOROF/spec/design/ibuffer.md
*/

`timescale 1ns/100ps

`include "corep.vh"

module ibuffer_tb #(
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


    // enq
	logic tb_enq_valid;
	corep::ibuffer_enq_info_t tb_enq_info;
	logic tb_enq_fetch_hit_valid;
	corep::fetch16B_t tb_enq_fetch_hit_fetch16B;

    // enq feedback
	logic DUT_enq_ready, expected_enq_ready;
	corep::fmid_t DUT_enq_fmid, expected_enq_fmid;

    // fetch miss return
	logic tb_fetch_miss_return_valid;
	corep::fmid_t tb_fetch_miss_return_fmid;
	corep::fetch16B_t tb_fetch_miss_return_fetch16B;

    // instr yield
	logic DUT_instr_yield_valid, expected_instr_yield_valid;
	corep::instr_yield_t [3:0] DUT_instr_yield_by_way, expected_instr_yield_by_way;

    // instr yield feedback
	logic tb_instr_yield_ready;

    // restart
	logic tb_restart_valid;

    // ----------------------------------------------------------------
    // DUT instantiation:

	ibuffer #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // enq
		.enq_valid(tb_enq_valid),
		.enq_info(tb_enq_info),
		.enq_fetch_hit_valid(tb_enq_fetch_hit_valid),
		.enq_fetch_hit_fetch16B(tb_enq_fetch_hit_fetch16B),

	    // enq feedback
		.enq_ready(DUT_enq_ready),
		.enq_fmid(DUT_enq_fmid),

	    // fetch miss return
		.fetch_miss_return_valid(tb_fetch_miss_return_valid),
		.fetch_miss_return_fmid(tb_fetch_miss_return_fmid),
		.fetch_miss_return_fetch16B(tb_fetch_miss_return_fetch16B),

	    // instr yield
		.instr_yield_valid(DUT_instr_yield_valid),
		.instr_yield_by_way(DUT_instr_yield_by_way),

	    // instr yield feedback
		.instr_yield_ready(tb_instr_yield_ready),

	    // restart
		.restart_valid(tb_restart_valid)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_enq_ready !== DUT_enq_ready) begin
			$display("TB ERROR: expected_enq_ready (%h) != DUT_enq_ready (%h)",
				expected_enq_ready, DUT_enq_ready);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_enq_fmid !== DUT_enq_fmid) begin
			$display("TB ERROR: expected_enq_fmid (%h) != DUT_enq_fmid (%h)",
				expected_enq_fmid, DUT_enq_fmid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_instr_yield_valid !== DUT_instr_yield_valid) begin
			$display("TB ERROR: expected_instr_yield_valid (%h) != DUT_instr_yield_valid (%h)",
				expected_instr_yield_valid, DUT_instr_yield_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_instr_yield_by_way !== DUT_instr_yield_by_way) begin
			$display("TB ERROR: expected_instr_yield_by_way != DUT_instr_yield_by_way");
			$display("\t\t[0].valid (%0h)              \t%s\t [0].valid (%0h)",
				expected_instr_yield_by_way[0].valid, expected_instr_yield_by_way[0].valid == DUT_instr_yield_by_way[0].valid ? "==" : "!=", DUT_instr_yield_by_way[0].valid);
			$display("\t\t[0].btb_hit (%0h)            \t%s\t [0].btb_hit (%0h)",
				expected_instr_yield_by_way[0].btb_hit, expected_instr_yield_by_way[0].btb_hit == DUT_instr_yield_by_way[0].btb_hit ? "==" : "!=", DUT_instr_yield_by_way[0].btb_hit);
			$display("\t\t[0].redirect_taken (%0h)     \t%s\t [0].redirect_taken (%0h)",
				expected_instr_yield_by_way[0].redirect_taken, expected_instr_yield_by_way[0].redirect_taken == DUT_instr_yield_by_way[0].redirect_taken ? "==" : "!=", DUT_instr_yield_by_way[0].redirect_taken);
			$display("\t\t[0].mid_instr_redirect (%0h) \t%s\t [0].mid_instr_redirect (%0h)",
				expected_instr_yield_by_way[0].mid_instr_redirect, expected_instr_yield_by_way[0].mid_instr_redirect == DUT_instr_yield_by_way[0].mid_instr_redirect ? "==" : "!=", DUT_instr_yield_by_way[0].mid_instr_redirect);
			$display("\t\t[0].bcb_idx (%0h)            \t%s\t [0].bcb_idx (%0h)",
				expected_instr_yield_by_way[0].bcb_idx, expected_instr_yield_by_way[0].bcb_idx == DUT_instr_yield_by_way[0].bcb_idx ? "==" : "!=", DUT_instr_yield_by_way[0].bcb_idx);
			$display("\t\t[0].src_pc38 (%09h,%01h)   \t%s\t [0].src_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[0].src_pc38[37:3], expected_instr_yield_by_way[0].src_pc38[2:0], expected_instr_yield_by_way[0].src_pc38 == DUT_instr_yield_by_way[0].src_pc38 ? "==" : "!=", DUT_instr_yield_by_way[0].src_pc38[37:3], DUT_instr_yield_by_way[0].src_pc38[2:0]);
			$display("\t\t[0].tgt_pc38 (%09h,%01h)   \t%s\t [0].tgt_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[0].tgt_pc38[37:3], expected_instr_yield_by_way[0].tgt_pc38[2:0], expected_instr_yield_by_way[0].tgt_pc38 == DUT_instr_yield_by_way[0].tgt_pc38 ? "==" : "!=", DUT_instr_yield_by_way[0].tgt_pc38[37:3], DUT_instr_yield_by_way[0].tgt_pc38[2:0]);
			$display("\t\t[0].page_fault (%0h)         \t%s\t [0].page_fault (%0h)",
				expected_instr_yield_by_way[0].page_fault, expected_instr_yield_by_way[0].page_fault == DUT_instr_yield_by_way[0].page_fault ? "==" : "!=", DUT_instr_yield_by_way[0].page_fault);
			$display("\t\t[0].access_fault (%0h)       \t%s\t [0].access_fault (%0h)",
				expected_instr_yield_by_way[0].access_fault, expected_instr_yield_by_way[0].access_fault == DUT_instr_yield_by_way[0].access_fault ? "==" : "!=", DUT_instr_yield_by_way[0].access_fault);
			$display("\t\t[0].mdp (%02h)                \t%s\t [0].mdp (%02h)",
				expected_instr_yield_by_way[0].mdp, expected_instr_yield_by_way[0].mdp == DUT_instr_yield_by_way[0].mdp ? "==" : "!=", DUT_instr_yield_by_way[0].mdp);
			$display("\t\t[0].fetch4B (%08h)       \t%s\t [0].fetch4B (%08h)",
				expected_instr_yield_by_way[0].fetch4B, expected_instr_yield_by_way[0].fetch4B == DUT_instr_yield_by_way[0].fetch4B ? "==" : "!=", DUT_instr_yield_by_way[0].fetch4B);
            $display();
			$display("\t\t[1].valid (%0h)              \t%s\t [1].valid (%0h)",
				expected_instr_yield_by_way[1].valid, expected_instr_yield_by_way[1].valid == DUT_instr_yield_by_way[1].valid ? "==" : "!=", DUT_instr_yield_by_way[1].valid);
			$display("\t\t[1].btb_hit (%0h)            \t%s\t [1].btb_hit (%0h)",
				expected_instr_yield_by_way[1].btb_hit, expected_instr_yield_by_way[1].btb_hit == DUT_instr_yield_by_way[1].btb_hit ? "==" : "!=", DUT_instr_yield_by_way[1].btb_hit);
			$display("\t\t[1].redirect_taken (%0h)     \t%s\t [1].redirect_taken (%0h)",
				expected_instr_yield_by_way[1].redirect_taken, expected_instr_yield_by_way[1].redirect_taken == DUT_instr_yield_by_way[1].redirect_taken ? "==" : "!=", DUT_instr_yield_by_way[1].redirect_taken);
			$display("\t\t[1].mid_instr_redirect (%0h) \t%s\t [1].mid_instr_redirect (%0h)",
				expected_instr_yield_by_way[1].mid_instr_redirect, expected_instr_yield_by_way[1].mid_instr_redirect == DUT_instr_yield_by_way[1].mid_instr_redirect ? "==" : "!=", DUT_instr_yield_by_way[1].mid_instr_redirect);
			$display("\t\t[1].bcb_idx (%0h)            \t%s\t [1].bcb_idx (%0h)",
				expected_instr_yield_by_way[1].bcb_idx, expected_instr_yield_by_way[1].bcb_idx == DUT_instr_yield_by_way[1].bcb_idx ? "==" : "!=", DUT_instr_yield_by_way[1].bcb_idx);
			$display("\t\t[1].src_pc38 (%09h,%01h)   \t%s\t [1].src_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[1].src_pc38[37:3], expected_instr_yield_by_way[1].src_pc38[2:0], expected_instr_yield_by_way[1].src_pc38 == DUT_instr_yield_by_way[1].src_pc38 ? "==" : "!=", DUT_instr_yield_by_way[1].src_pc38[37:3], DUT_instr_yield_by_way[1].src_pc38[2:0]);
			$display("\t\t[1].tgt_pc38 (%09h,%01h)   \t%s\t [1].tgt_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[1].tgt_pc38[37:3], expected_instr_yield_by_way[1].tgt_pc38[2:0], expected_instr_yield_by_way[1].tgt_pc38 == DUT_instr_yield_by_way[1].tgt_pc38 ? "==" : "!=", DUT_instr_yield_by_way[1].tgt_pc38[37:3], DUT_instr_yield_by_way[1].tgt_pc38[2:0]);
			$display("\t\t[1].page_fault (%0h)         \t%s\t [1].page_fault (%0h)",
				expected_instr_yield_by_way[1].page_fault, expected_instr_yield_by_way[1].page_fault == DUT_instr_yield_by_way[1].page_fault ? "==" : "!=", DUT_instr_yield_by_way[1].page_fault);
			$display("\t\t[1].access_fault (%0h)       \t%s\t [1].access_fault (%0h)",
				expected_instr_yield_by_way[1].access_fault, expected_instr_yield_by_way[1].access_fault == DUT_instr_yield_by_way[1].access_fault ? "==" : "!=", DUT_instr_yield_by_way[1].access_fault);
			$display("\t\t[1].mdp (%02h)                \t%s\t [1].mdp (%02h)",
				expected_instr_yield_by_way[1].mdp, expected_instr_yield_by_way[1].mdp == DUT_instr_yield_by_way[1].mdp ? "==" : "!=", DUT_instr_yield_by_way[1].mdp);
			$display("\t\t[1].fetch4B (%08h)    \t%s\t [1].fetch4B (%08h)",
				expected_instr_yield_by_way[1].fetch4B, expected_instr_yield_by_way[1].fetch4B == DUT_instr_yield_by_way[1].fetch4B ? "==" : "!=", DUT_instr_yield_by_way[1].fetch4B);
            $display();
			$display("\t\t[2].valid (%0h)              \t%s\t [2].valid (%0h)",
				expected_instr_yield_by_way[2].valid, expected_instr_yield_by_way[2].valid == DUT_instr_yield_by_way[2].valid ? "==" : "!=", DUT_instr_yield_by_way[2].valid);
			$display("\t\t[2].btb_hit (%0h)            \t%s\t [2].btb_hit (%0h)",
				expected_instr_yield_by_way[2].btb_hit, expected_instr_yield_by_way[2].btb_hit == DUT_instr_yield_by_way[2].btb_hit ? "==" : "!=", DUT_instr_yield_by_way[2].btb_hit);
			$display("\t\t[2].redirect_taken (%0h)     \t%s\t [2].redirect_taken (%0h)",
				expected_instr_yield_by_way[2].redirect_taken, expected_instr_yield_by_way[2].redirect_taken == DUT_instr_yield_by_way[2].redirect_taken ? "==" : "!=", DUT_instr_yield_by_way[2].redirect_taken);
			$display("\t\t[2].mid_instr_redirect (%0h) \t%s\t [2].mid_instr_redirect (%0h)",
				expected_instr_yield_by_way[2].mid_instr_redirect, expected_instr_yield_by_way[2].mid_instr_redirect == DUT_instr_yield_by_way[2].mid_instr_redirect ? "==" : "!=", DUT_instr_yield_by_way[2].mid_instr_redirect);
			$display("\t\t[2].bcb_idx (%0h)            \t%s\t [2].bcb_idx (%0h)",
				expected_instr_yield_by_way[2].bcb_idx, expected_instr_yield_by_way[2].bcb_idx == DUT_instr_yield_by_way[2].bcb_idx ? "==" : "!=", DUT_instr_yield_by_way[2].bcb_idx);
			$display("\t\t[2].src_pc38 (%09h,%01h)   \t%s\t [2].src_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[2].src_pc38[37:3], expected_instr_yield_by_way[2].src_pc38[2:0], expected_instr_yield_by_way[2].src_pc38 == DUT_instr_yield_by_way[2].src_pc38 ? "==" : "!=", DUT_instr_yield_by_way[2].src_pc38[37:3], DUT_instr_yield_by_way[2].src_pc38[2:0]);
			$display("\t\t[2].tgt_pc38 (%09h,%01h)   \t%s\t [2].tgt_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[2].tgt_pc38[37:3], expected_instr_yield_by_way[2].tgt_pc38[2:0], expected_instr_yield_by_way[2].tgt_pc38 == DUT_instr_yield_by_way[2].tgt_pc38 ? "==" : "!=", DUT_instr_yield_by_way[2].tgt_pc38[37:3], DUT_instr_yield_by_way[2].tgt_pc38[2:0]);
			$display("\t\t[2].page_fault (%0h)         \t%s\t [2].page_fault (%0h)",
				expected_instr_yield_by_way[2].page_fault, expected_instr_yield_by_way[2].page_fault == DUT_instr_yield_by_way[2].page_fault ? "==" : "!=", DUT_instr_yield_by_way[2].page_fault);
			$display("\t\t[2].access_fault (%0h)       \t%s\t [2].access_fault (%0h)",
				expected_instr_yield_by_way[2].access_fault, expected_instr_yield_by_way[2].access_fault == DUT_instr_yield_by_way[2].access_fault ? "==" : "!=", DUT_instr_yield_by_way[2].access_fault);
			$display("\t\t[2].mdp (%02h)                \t%s\t [2].mdp (%02h)",
				expected_instr_yield_by_way[2].mdp, expected_instr_yield_by_way[2].mdp == DUT_instr_yield_by_way[2].mdp ? "==" : "!=", DUT_instr_yield_by_way[2].mdp);
			$display("\t\t[2].fetch4B (%08h)    \t%s\t [2].fetch4B (%08h)",
				expected_instr_yield_by_way[2].fetch4B, expected_instr_yield_by_way[2].fetch4B == DUT_instr_yield_by_way[2].fetch4B ? "==" : "!=", DUT_instr_yield_by_way[2].fetch4B);
            $display();
			$display("\t\t[3].valid (%0h)              \t%s\t [3].valid (%0h)",
				expected_instr_yield_by_way[3].valid, expected_instr_yield_by_way[3].valid == DUT_instr_yield_by_way[3].valid ? "==" : "!=", DUT_instr_yield_by_way[3].valid);
			$display("\t\t[3].btb_hit (%0h)            \t%s\t [3].btb_hit (%0h)",
				expected_instr_yield_by_way[3].btb_hit, expected_instr_yield_by_way[3].btb_hit == DUT_instr_yield_by_way[3].btb_hit ? "==" : "!=", DUT_instr_yield_by_way[3].btb_hit);
			$display("\t\t[3].redirect_taken (%0h)     \t%s\t [3].redirect_taken (%0h)",
				expected_instr_yield_by_way[3].redirect_taken, expected_instr_yield_by_way[3].redirect_taken == DUT_instr_yield_by_way[3].redirect_taken ? "==" : "!=", DUT_instr_yield_by_way[3].redirect_taken);
			$display("\t\t[3].mid_instr_redirect (%0h) \t%s\t [3].mid_instr_redirect (%0h)",
				expected_instr_yield_by_way[3].mid_instr_redirect, expected_instr_yield_by_way[3].mid_instr_redirect == DUT_instr_yield_by_way[3].mid_instr_redirect ? "==" : "!=", DUT_instr_yield_by_way[3].mid_instr_redirect);
			$display("\t\t[3].bcb_idx (%0h)            \t%s\t [3].bcb_idx (%0h)",
				expected_instr_yield_by_way[3].bcb_idx, expected_instr_yield_by_way[3].bcb_idx == DUT_instr_yield_by_way[3].bcb_idx ? "==" : "!=", DUT_instr_yield_by_way[3].bcb_idx);
			$display("\t\t[3].src_pc38 (%09h,%01h)   \t%s\t [3].src_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[3].src_pc38[37:3], expected_instr_yield_by_way[3].src_pc38[2:0], expected_instr_yield_by_way[3].src_pc38 == DUT_instr_yield_by_way[3].src_pc38 ? "==" : "!=", DUT_instr_yield_by_way[3].src_pc38[37:3], DUT_instr_yield_by_way[3].src_pc38[2:0]);
			$display("\t\t[3].tgt_pc38 (%09h,%01h)   \t%s\t [3].tgt_pc38 (%09h,%01h)",
				expected_instr_yield_by_way[3].tgt_pc38[37:3], expected_instr_yield_by_way[3].tgt_pc38[2:0], expected_instr_yield_by_way[3].tgt_pc38 == DUT_instr_yield_by_way[3].tgt_pc38 ? "==" : "!=", DUT_instr_yield_by_way[3].tgt_pc38[37:3], DUT_instr_yield_by_way[3].tgt_pc38[2:0]);
			$display("\t\t[3].page_fault (%0h)         \t%s\t [3].page_fault (%0h)",
				expected_instr_yield_by_way[3].page_fault, expected_instr_yield_by_way[3].page_fault == DUT_instr_yield_by_way[3].page_fault ? "==" : "!=", DUT_instr_yield_by_way[3].page_fault);
			$display("\t\t[3].access_fault (%0h)       \t%s\t [3].access_fault (%0h)",
				expected_instr_yield_by_way[3].access_fault, expected_instr_yield_by_way[3].access_fault == DUT_instr_yield_by_way[3].access_fault ? "==" : "!=", DUT_instr_yield_by_way[3].access_fault);
			$display("\t\t[3].mdp (%02h)                \t%s\t [3].mdp (%02h)",
				expected_instr_yield_by_way[3].mdp, expected_instr_yield_by_way[3].mdp == DUT_instr_yield_by_way[3].mdp ? "==" : "!=", DUT_instr_yield_by_way[3].mdp);
			$display("\t\t[3].fetch4B (%08h)    \t%s\t [3].fetch4B (%08h)",
				expected_instr_yield_by_way[3].fetch4B, expected_instr_yield_by_way[3].fetch4B == DUT_instr_yield_by_way[3].fetch4B ? "==" : "!=", DUT_instr_yield_by_way[3].fetch4B);

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
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h00;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h00;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h00;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h00;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;
        
		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h00;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h00;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h00;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h00;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

        // ------------------------------------------------------------
        // chain:
        test_case = "chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         F0 hit",
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: i",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h0F0F0F0F0};
		tb_enq_info.tgt_pc38 = {35'h0F0F0F0F1, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hF7,
            8'hF6,
            8'hF5,
            8'hF4,
            8'hF3,
            8'hF2,
            8'hF1,
            8'hF0
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'hF077,
            16'hF066,
            16'hF055,
            16'hF044,
            16'hF033,
            16'hF022,
            16'hF011,
            16'hF000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h00;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h00;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h00;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h00;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         E1 miss",
            "\n\t\tbuffer:      {F0h}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: i",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000001;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h0F0F0F0F1};
		tb_enq_info.tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hE7,
            8'hE6,
            8'hE5,
            8'hE4,
            8'hE3,
            8'hE2,
            8'hE1,
            8'hE0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h00;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h00;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h00;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h000000000, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h00;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         D2 hit",
            "\n\t\tbuffer:      {E1m0}",
            "\n\t\tshift reg 1: F0 {0,1,2,3,4,5,6,7}",
            "\n\t\tshift reg 0: i",
            "\n\t\tdeq:         {F000,F011,F022,F033}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h1;
		tb_enq_info.src_pc35 = {35'h2D2D2D2D2};
		tb_enq_info.tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hD7,
            8'hD6,
            8'hD5,
            8'hD4,
            8'hD3,
            8'hD2,
            8'hD1,
            8'hD0
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'hD278,
            16'hD269,
            16'hD25A,
            16'hD24B,
            16'hD23C,
            16'hD22D,
            16'hD21E,
            16'hD20F
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F0, 3'h0};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0F0F0F0F0, 3'h1};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hF0;
		expected_instr_yield_by_way[0].fetch4B = {16'hF011, 16'hF000};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F0, 3'h1};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0F0F0F0F0, 3'h2};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hF1;
		expected_instr_yield_by_way[1].fetch4B = {16'hF022, 16'hF011};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F0, 3'h2};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0F0F0F0F0, 3'h3};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hF2;
		expected_instr_yield_by_way[2].fetch4B = {16'hF033, 16'hF022};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F0, 3'h3};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0F0F0F0F0, 3'h5};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hF3;
		expected_instr_yield_by_way[3].fetch4B = {16'hF044, 16'hF033};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         C3 miss",
            "\n\t\tbuffer:      {E1m0,D2h}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,5,6,7}",
            "\n\t\tdeq:         {F055,F066,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b00111111;
		tb_enq_info.btb_hit_by_lane = 8'b00100000;
		tb_enq_info.redirect_taken_by_lane = 8'b00100000;
		tb_enq_info.bcb_idx = 4'h1;
		tb_enq_info.src_pc35 = {35'h2D2D2D2D3};
		tb_enq_info.tgt_pc38 = {35'h3C3C3C3C3, 3'h3};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hC7,
            8'hC6,
            8'hC5,
            8'hC4,
            8'hC3,
            8'hC2,
            8'hC1,
            8'hC0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F0, 3'h5};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0F0F0F0F0, 3'h6};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hF5;
		expected_instr_yield_by_way[0].fetch4B = {16'hF066, 16'hF055};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F0, 3'h6};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0F0F0F0F0, 3'h7};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hF6;
		expected_instr_yield_by_way[1].fetch4B = {16'hF077, 16'hF066};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         B4 hit",
            "\n\t\tbuffer:      {E1m0,D2h,C3m1}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h3C3C3C3C3};
		tb_enq_info.tgt_pc38 = {35'h4B4B4B4B4, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hB7,
            8'hB6,
            8'hB5,
            8'hB4,
            8'hB3,
            8'hB2,
            8'hB1,
            8'hB0
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'hB477,
            16'hB466,
            16'hB455,
            16'hB444,
            16'hB433,
            16'hB422,
            16'hB411,
            16'hB400
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h2;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         A5 miss",
            "\n\t\tbuffer:      {E1m0,D2h,C3m1,B4h}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h4B4B4B4B4};
		tb_enq_info.tgt_pc38 = {35'h5A5A5A5A5, 3'h0};
		tb_enq_info.page_fault = 1'b1;
		tb_enq_info.access_fault = 1'b1;
		tb_enq_info.mdp_by_lane = {
            8'hA7,
            8'hA6,
            8'hA5,
            8'hA4,
            8'hA3,
            8'hA2,
            8'hA1,
            8'hA0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h2;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         96 hit",
            "\n\t\tbuffer:      {E1m0,D2h,C3m1,B4h,A5m2}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h5A5A5A5A5};
		tb_enq_info.tgt_pc38 = {35'h696969696, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h97,
            8'h96,
            8'h95,
            8'h94,
            8'h93,
            8'h92,
            8'h91,
            8'h90
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'h9670,
            16'h9661,
            16'h9652,
            16'h9643,
            16'h9634,
            16'h9625,
            16'h9616,
            16'h9607
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h3;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         87 miss",
            "\n\t\tbuffer:      {E1m0,D2h,C3m1,B4h,A5m2,96h}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h696969696};
		tb_enq_info.tgt_pc38 = {35'h787878787, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h87,
            8'h86,
            8'h85,
            8'h84,
            8'h83,
            8'h82,
            8'h81,
            8'h80
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h3;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         78 hit",
            "\n\t\tbuffer:      {E1m0,D2h,C3m1,B4h,A5m2,96h,87m3}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i} (stall)"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h787878787};
		tb_enq_info.tgt_pc38 = {35'h878787878, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h77,
            8'h76,
            8'h75,
            8'h74,
            8'h73,
            8'h72,
            8'h71,
            8'h70
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'h787F,
            16'h786E,
            16'h785D,
            16'h784C,
            16'h783B,
            16'h782A,
            16'h7819,
            16'h7808
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b0;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h4;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         69 miss (stall)",
            "\n\t\tbuffer:      {E1m0,D2h,C3m1,B4h,A5m2,96h,87m3,78h}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b00000111;
		tb_enq_info.btb_hit_by_lane = 8'b00000100;
		tb_enq_info.redirect_taken_by_lane = 8'b00000100;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h878787878};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h67,
            8'h66,
            8'h65,
            8'h64,
            8'h63,
            8'h62,
            8'h61,
            8'h60
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'h4;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         69 miss (stall)",
            "\n\t\tmiss ret:    E1m0",
            "\n\t\tbuffer:      {E1m0->h,D2h,C3m1,B4h,A5m2,96h,87m3,78h}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b00000111;
		tb_enq_info.btb_hit_by_lane = 8'b00000100;
		tb_enq_info.redirect_taken_by_lane = 8'b00000100;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h878787878};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h67,
            8'h66,
            8'h65,
            8'h64,
            8'h63,
            8'h62,
            8'h61,
            8'h60
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'hE173,
            16'hE163,
            16'hE153,
            16'hE143,
            16'hE133,
            16'hE123,
            16'hE113,
            16'hE103
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'h4;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         69 miss (stall)",
            "\n\t\tmiss ret:    A5m2",
            "\n\t\tbuffer:      {E1h,D2h,C3m1,B4h,A5m2->h,96h,87m3,78h}",
            "\n\t\tshift reg 1: i",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b00000111;
		tb_enq_info.btb_hit_by_lane = 8'b00000100;
		tb_enq_info.redirect_taken_by_lane = 8'b00000100;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h878787878};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h67,
            8'h66,
            8'h65,
            8'h64,
            8'h63,
            8'h62,
            8'h61,
            8'h60
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h2;
		tb_fetch_miss_return_fetch16B = {
            16'hA573,
            16'hA560,
            16'hA553,
            16'hA543,
            16'hA530,
            16'hA523,
            16'hA513,
            16'hA500
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE7;
		expected_instr_yield_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE7;
		expected_instr_yield_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h1E1E1E1E1, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE7;
		expected_instr_yield_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         69 miss",
            "\n\t\tmiss ret:    C3m1",
            "\n\t\tbuffer:      {D2h,C3m1->h,B4h,A5h,96h,87m3,78h}",
            "\n\t\tshift reg 1: E1 {3,3,3,3,3,3,3,3}",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {F077,E113,E133,E135} (stall)"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b00000111;
		tb_enq_info.btb_hit_by_lane = 8'b00000100;
		tb_enq_info.redirect_taken_by_lane = 8'b00000100;
		tb_enq_info.bcb_idx = 4'h2;
		tb_enq_info.src_pc35 = {35'h878787878};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h67,
            8'h66,
            8'h65,
            8'h64,
            8'h63,
            8'h62,
            8'h61,
            8'h60
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h1;
		tb_fetch_miss_return_fetch16B = {
            16'hC37F,
            16'hC36B,
            16'hC357,
            16'hC343,
            16'hC330,
            16'hC320,
            16'hC310,
            16'hC300
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b0;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b1;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F0, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0F0F0F0F1, 3'h1};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hF7;
		expected_instr_yield_by_way[0].fetch4B = {16'hE103, 16'hF077};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h1};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0F0F0F0F1, 3'h3};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE1;
		expected_instr_yield_by_way[1].fetch4B = {16'hE123, 16'hE113};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h3};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0F0F0F0F1, 3'h5};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE3;
		expected_instr_yield_by_way[2].fetch4B = {16'hE143, 16'hE133};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h5};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE5;
		expected_instr_yield_by_way[3].fetch4B = {16'hE163, 16'hE153};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    87m3",
            "\n\t\tbuffer:      {D2h,C3h,B4h,A5h,96h,87m3->h,78h,69m0}",
            "\n\t\tshift reg 1: E1 {3,3,3,3,3,3,3,3}",
            "\n\t\tshift reg 0: F0 {i,i,i,i,i,i,i,7}",
            "\n\t\tdeq:         {F077,E113,E133,E135}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h3;
		tb_fetch_miss_return_fetch16B = {
            16'h877C,
            16'h876D,
            16'h875E,
            16'h874F,
            16'h8737,
            16'h8726,
            16'h8715,
            16'h8704
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b1;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F0, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0F0F0F0F1, 3'h1};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hF7;
		expected_instr_yield_by_way[0].fetch4B = {16'hE103, 16'hF077};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0F0F0F0F1, 3'h1};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0F0F0F0F1, 3'h3};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hE1;
		expected_instr_yield_by_way[1].fetch4B = {16'hE123, 16'hE113};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0F0F0F0F1, 3'h3};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0F0F0F0F1, 3'h5};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hE3;
		expected_instr_yield_by_way[2].fetch4B = {16'hE143, 16'hE133};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0F0F0F0F1, 3'h5};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hE5;
		expected_instr_yield_by_way[3].fetch4B = {16'hE163, 16'hE153};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    69m0",
            "\n\t\tbuffer:      {C3h,B4h,A5h,96h,87h,78h,69m0->h}",
            "\n\t\tshift reg 1: D2 {F,E,D,C,B,A,9,8}",
            "\n\t\tshift reg 0: E1 {i,i,i,i,i,i,i,3}",
            "\n\t\tdeq:         {E173,D21E,D22D,D23C}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h6970,
            16'h6960,
            16'h6950,
            16'h6940,
            16'h6930,
            16'h6923,
            16'h6911,
            16'h6901
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h1;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0F0F0F0F1, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h2D2D2D2D2, 3'h1};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hE7;
		expected_instr_yield_by_way[0].fetch4B = {16'hD20F, 16'hE173};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h1;
		expected_instr_yield_by_way[1].src_pc38 = {35'h2D2D2D2D2, 3'h1};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h2D2D2D2D2, 3'h2};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hD1;
		expected_instr_yield_by_way[1].fetch4B = {16'hD22D, 16'hD21E};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h1;
		expected_instr_yield_by_way[2].src_pc38 = {35'h2D2D2D2D2, 3'h2};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h2D2D2D2D2, 3'h3};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hD2;
		expected_instr_yield_by_way[2].fetch4B = {16'hD23C, 16'hD22D};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h1;
		expected_instr_yield_by_way[3].src_pc38 = {35'h2D2D2D2D2, 3'h3};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h2D2D2D2D2, 3'h4};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hD3;
		expected_instr_yield_by_way[3].fetch4B = {16'hD24B, 16'hD23C};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {B4h,A5h,96h,87h,78h,69h}",
            "\n\t\tshift reg 1: C3 {0,0,0,0,3,7,i,i}",
            "\n\t\tshift reg 0: D2 {i,i,i,i,B,A,9,8}",
            "\n\t\tdeq:         {D24B,D269,D278,C300}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h1;
		expected_instr_yield_by_way[0].src_pc38 = {35'h2D2D2D2D2, 3'h4};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h2D2D2D2D2, 3'h6};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hD4;
		expected_instr_yield_by_way[0].fetch4B = {16'hD25A, 16'hD24B};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h1;
		expected_instr_yield_by_way[1].src_pc38 = {35'h2D2D2D2D2, 3'h6};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hD6;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD269};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h1;
		expected_instr_yield_by_way[2].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hD7;
		expected_instr_yield_by_way[2].fetch4B = {16'hC300, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h1;
		expected_instr_yield_by_way[3].src_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h2D2D2D2D3, 3'h1};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hC0;
		expected_instr_yield_by_way[3].fetch4B = {16'hC310, 16'hC300};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {A5h,96h,87h,78h,69h}",
            "\n\t\tshift reg 1: B4 {i,i,i,3,4,5,6,7}",
            "\n\t\tshift reg 0: C3 {i,0,0,0,3,7,i,i}",
            "\n\t\tdeq:         {C310,C320,C330,C340}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h1;
		expected_instr_yield_by_way[0].src_pc38 = {35'h2D2D2D2D3, 3'h1};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h2D2D2D2D3, 3'h2};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hC1;
		expected_instr_yield_by_way[0].fetch4B = {16'hC320, 16'hC310};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h1;
		expected_instr_yield_by_way[1].src_pc38 = {35'h2D2D2D2D3, 3'h2};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h2D2D2D2D3, 3'h3};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hC2;
		expected_instr_yield_by_way[1].fetch4B = {16'hC330, 16'hC320};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h1;
		expected_instr_yield_by_way[2].src_pc38 = {35'h2D2D2D2D3, 3'h3};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h2D2D2D2D3, 3'h4};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hC3;
		expected_instr_yield_by_way[2].fetch4B = {16'hC343, 16'hC330};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b1;
		expected_instr_yield_by_way[3].redirect_taken = 1'b1;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h1;
		expected_instr_yield_by_way[3].src_pc38 = {35'h2D2D2D2D3, 3'h4};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h3C3C3C3C3, 3'h3};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hC4;
		expected_instr_yield_by_way[3].fetch4B = {16'hC357, 16'hC343};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {96h,87h,78h,69h}",
            "\n\t\tshift reg 1: A5 {0,3,3,0,3,3,0,3}",
            "\n\t\tshift reg 0: B4 {i,i,i,3,4,5,6,7}",
            "\n\t\tdeq:         {B433,B455,B466,B477}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h3C3C3C3C3, 3'h3};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h3C3C3C3C3, 3'h5};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hB3;
		expected_instr_yield_by_way[0].fetch4B = {16'hB444, 16'hB433};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h3C3C3C3C3, 3'h5};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h3C3C3C3C3, 3'h6};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hB5;
		expected_instr_yield_by_way[1].fetch4B = {16'hB466, 16'hB455};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h3C3C3C3C3, 3'h6};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h3C3C3C3C3, 3'h7};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hB6;
		expected_instr_yield_by_way[2].fetch4B = {16'hB477, 16'hB466};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h3C3C3C3C3, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h4B4B4B4B4, 3'h1};
		expected_instr_yield_by_way[3].page_fault = 1'b1;
		expected_instr_yield_by_way[3].access_fault = 1'b1;
		expected_instr_yield_by_way[3].mdp = 8'hB7;
		expected_instr_yield_by_way[3].fetch4B = {16'hA500, 16'hB477};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {87h,78h,69h}",
            "\n\t\tshift reg 1: 96 {7,6,5,4,3,2,1,0}",
            "\n\t\tshift reg 0: A5 {i,3,3,0,3,3,0,3}",
            "\n\t\tdeq:         {A513,A530,A543,A560}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h4B4B4B4B4, 3'h1};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h4B4B4B4B4, 3'h3};
		expected_instr_yield_by_way[0].page_fault = 1'b1;
		expected_instr_yield_by_way[0].access_fault = 1'b1;
		expected_instr_yield_by_way[0].mdp = 8'hA1;
		expected_instr_yield_by_way[0].fetch4B = {16'hA523, 16'hA513};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h4B4B4B4B4, 3'h3};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h4B4B4B4B4, 3'h4};
		expected_instr_yield_by_way[1].page_fault = 1'b1;
		expected_instr_yield_by_way[1].access_fault = 1'b1;
		expected_instr_yield_by_way[1].mdp = 8'hA3;
		expected_instr_yield_by_way[1].fetch4B = {16'hA543, 16'hA530};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h4B4B4B4B4, 3'h4};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h4B4B4B4B4, 3'h6};
		expected_instr_yield_by_way[2].page_fault = 1'b1;
		expected_instr_yield_by_way[2].access_fault = 1'b1;
		expected_instr_yield_by_way[2].mdp = 8'hA4;
		expected_instr_yield_by_way[2].fetch4B = {16'hA553, 16'hA543};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h4B4B4B4B4, 3'h6};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h4B4B4B4B4, 3'h7};
		expected_instr_yield_by_way[3].page_fault = 1'b1;
		expected_instr_yield_by_way[3].access_fault = 1'b1;
		expected_instr_yield_by_way[3].mdp = 8'hA6;
		expected_instr_yield_by_way[3].fetch4B = {16'hA573, 16'hA560};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {87h,78h,69h}",
            "\n\t\tshift reg 1: 96 {7,6,5,4,3,2,1,0}",
            "\n\t\tshift reg 0: A5 {i,i,i,i,i,i,i,3}",
            "\n\t\tdeq:         {A573,9616,9625,9634} (stall)"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b0;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h4B4B4B4B4, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h5A5A5A5A5, 3'h1};
		expected_instr_yield_by_way[0].page_fault = 1'b1;
		expected_instr_yield_by_way[0].access_fault = 1'b1;
		expected_instr_yield_by_way[0].mdp = 8'hA7;
		expected_instr_yield_by_way[0].fetch4B = {16'h9607, 16'hA573};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h5A5A5A5A5, 3'h1};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h5A5A5A5A5, 3'h2};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h91;
		expected_instr_yield_by_way[1].fetch4B = {16'h9625, 16'h9616};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h5A5A5A5A5, 3'h2};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h5A5A5A5A5, 3'h3};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h92;
		expected_instr_yield_by_way[2].fetch4B = {16'h9634, 16'h9625};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h5A5A5A5A5, 3'h3};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h5A5A5A5A5, 3'h4};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h93;
		expected_instr_yield_by_way[3].fetch4B = {16'h9643, 16'h9634};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {87h,78h,69h}",
            "\n\t\tshift reg 1: 96 {7,6,5,4,3,2,1,0}",
            "\n\t\tshift reg 0: A5 {i,i,i,i,i,i,i,3}",
            "\n\t\tdeq:         {A573,9616,9625,9634}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h4B4B4B4B4, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h5A5A5A5A5, 3'h1};
		expected_instr_yield_by_way[0].page_fault = 1'b1;
		expected_instr_yield_by_way[0].access_fault = 1'b1;
		expected_instr_yield_by_way[0].mdp = 8'hA7;
		expected_instr_yield_by_way[0].fetch4B = {16'h9607, 16'hA573};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h5A5A5A5A5, 3'h1};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h5A5A5A5A5, 3'h2};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h91;
		expected_instr_yield_by_way[1].fetch4B = {16'h9625, 16'h9616};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h5A5A5A5A5, 3'h2};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h5A5A5A5A5, 3'h3};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h92;
		expected_instr_yield_by_way[2].fetch4B = {16'h9634, 16'h9625};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h5A5A5A5A5, 3'h3};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h5A5A5A5A5, 3'h4};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h93;
		expected_instr_yield_by_way[3].fetch4B = {16'h9643, 16'h9634};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {78h,69h}",
            "\n\t\tshift reg 1: 87 {4,5,6,7,F,E,D,C}",
            "\n\t\tshift reg 0: 96 {i,i,i,i,3,2,1,0}",
            "\n\t\tdeq:         {9643,9661,9670,8704}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h5A5A5A5A5, 3'h4};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h5A5A5A5A5, 3'h6};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h94;
		expected_instr_yield_by_way[0].fetch4B = {16'h9652, 16'h9643};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h5A5A5A5A5, 3'h6};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h5A5A5A5A5, 3'h7};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h96;
		expected_instr_yield_by_way[1].fetch4B = {16'h9670, 16'h9661};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h5A5A5A5A5, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h696969696, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h97;
		expected_instr_yield_by_way[2].fetch4B = {16'h8704, 16'h9670};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h696969696, 3'h0};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h696969696, 3'h1};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h80;
		expected_instr_yield_by_way[3].fetch4B = {16'h8715, 16'h8704};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {69h}",
            "\n\t\tshift reg 1: 78 {8,9,A,B,C,D,E,F}",
            "\n\t\tshift reg 0: 87 {i,5,6,7,F,E,D,C}",
            "\n\t\tdeq:         {8715,8726,8737,875E}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h696969696, 3'h1};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h696969696, 3'h2};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h81;
		expected_instr_yield_by_way[0].fetch4B = {16'h8726, 16'h8715};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h696969696, 3'h2};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h696969696, 3'h3};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h82;
		expected_instr_yield_by_way[1].fetch4B = {16'h8737, 16'h8726};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h696969696, 3'h3};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h696969696, 3'h5};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h83;
		expected_instr_yield_by_way[2].fetch4B = {16'h874F, 16'h8737};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h696969696, 3'h5};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h696969696, 3'h6};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h85;
		expected_instr_yield_by_way[3].fetch4B = {16'h876D, 16'h875E};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {69h}",
            "\n\t\tshift reg 1: 78 {8,9,A,B,C,D,E,F}",
            "\n\t\tshift reg 0: 87 {i,i,i,i,i,i,D,C}",
            "\n\t\tdeq:         {876D,877C,7808,7819}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h696969696, 3'h6};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h696969696, 3'h7};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h86;
		expected_instr_yield_by_way[0].fetch4B = {16'h877C, 16'h876D};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h696969696, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h787878787, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h7808, 16'h877C};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h787878787, 3'h0};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h787878787, 3'h1};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h70;
		expected_instr_yield_by_way[2].fetch4B = {16'h7819, 16'h7808};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h787878787, 3'h1};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h787878787, 3'h2};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h71;
		expected_instr_yield_by_way[3].fetch4B = {16'h782A, 16'h7819};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: 69 {1,1,3,i,i,i,i,i}",
            "\n\t\tshift reg 0: 78 {i,i,A,B,C,D,E,F}",
            "\n\t\tdeq:         {782A,783B,785D,786E}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h787878787, 3'h2};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h787878787, 3'h3};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h72;
		expected_instr_yield_by_way[0].fetch4B = {16'h783B, 16'h782A};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h787878787, 3'h3};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h787878787, 3'h5};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h73;
		expected_instr_yield_by_way[1].fetch4B = {16'h784C, 16'h783B};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h787878787, 3'h5};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h787878787, 3'h6};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h75;
		expected_instr_yield_by_way[2].fetch4B = {16'h786E, 16'h785D};

		expected_instr_yield_by_way[3].valid = 1'b1;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h787878787, 3'h6};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h787878787, 3'h7};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h76;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h786E};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: 69 {1,1,3,i,i,i,i,i}",
            "\n\t\tshift reg 0: 78 {i,i,i,i,i,i,i,F}",
            "\n\t\tdeq:         {787F,6911,6922,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b1;

		expected_instr_yield_by_way[0].valid = 1'b1;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h2;
		expected_instr_yield_by_way[0].src_pc38 = {35'h787878787, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h878787878, 3'h1};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h77;
		expected_instr_yield_by_way[0].fetch4B = {16'h6901, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b1;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h2;
		expected_instr_yield_by_way[1].src_pc38 = {35'h878787878, 3'h1};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h878787878, 3'h2};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h61;
		expected_instr_yield_by_way[1].fetch4B = {16'h6923, 16'h6911};

		expected_instr_yield_by_way[2].valid = 1'b1;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b1;
		expected_instr_yield_by_way[2].bcb_idx = 4'h2;
		expected_instr_yield_by_way[2].src_pc38 = {35'h878787878, 3'h2};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h878787878, 3'h4}; // don't care on mid_instr_redirect
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h62;
		expected_instr_yield_by_way[2].fetch4B = {16'h6930, 16'h6923};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h2;
		expected_instr_yield_by_way[3].src_pc38 = {35'h878787878, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h67;
		expected_instr_yield_by_way[3].fetch4B = {16'h6970, 16'h6970};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         i",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h1;
		expected_instr_yield_by_way[0].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hD7;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h1;
		expected_instr_yield_by_way[1].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hD7;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h1;
		expected_instr_yield_by_way[2].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hD7;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h1;
		expected_instr_yield_by_way[3].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hD7;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

        // ------------------------------------------------------------
        // run out of fmid's, restart:
        test_case = "run out of fmid's, restart";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         0 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h0FF00FF00};
		tb_enq_info.tgt_pc38 = {35'h0FF00FF00, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h07,
            8'h06,
            8'h05,
            8'h04,
            8'h03,
            8'h02,
            8'h01,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h0;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h1;
		expected_instr_yield_by_way[0].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hD7;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h1;
		expected_instr_yield_by_way[1].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hD7;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h1;
		expected_instr_yield_by_way[2].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hD7;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h1;
		expected_instr_yield_by_way[3].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hD7;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         1 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0m0}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h1EE11EE11};
		tb_enq_info.tgt_pc38 = {35'h1EE11EE11, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h17,
            8'h16,
            8'h15,
            8'h14,
            8'h13,
            8'h12,
            8'h11,
            8'h10
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h1;
		expected_instr_yield_by_way[0].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'hD7;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h1;
		expected_instr_yield_by_way[1].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'hD7;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h1;
		expected_instr_yield_by_way[2].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'hD7;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h1;
		expected_instr_yield_by_way[3].src_pc38 = {35'h2D2D2D2D2, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h2D2D2D2D3, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'hD7;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         2 hit (stalled)",
            "\n\t\tmiss ret:    1m1",
            "\n\t\tbuffer:      {0m0,1m1->h}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h2DD22DD22};
		tb_enq_info.tgt_pc38 = {35'h2DD22DD22, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h27,
            8'h26,
            8'h25,
            8'h24,
            8'h23,
            8'h22,
            8'h21,
            8'h20
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h1;
		tb_fetch_miss_return_fetch16B = {
            16'h1177,
            16'h1166,
            16'h1155,
            16'h1144,
            16'h1133,
            16'h1122,
            16'h1111,
            16'h1100
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'h2;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         2 hit",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0m0,1h,}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h2DD22DD22};
		tb_enq_info.tgt_pc38 = {35'h2DD22DD22, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h27,
            8'h26,
            8'h25,
            8'h24,
            8'h23,
            8'h22,
            8'h21,
            8'h20
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD,
            16'hDEAD
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         3 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0m0,1h,2h}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h3CC33CC33};
		tb_enq_info.tgt_pc38 = {35'h3CC33CC33, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h37,
            8'h36,
            8'h35,
            8'h34,
            8'h33,
            8'h32,
            8'h31,
            8'h30
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         4 miss",
            "\n\t\tmiss ret:    3m1",
            "\n\t\tbuffer:      {0m0,1h,2h,3m1->h}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h4BB44BB44};
		tb_enq_info.tgt_pc38 = {35'h4BB44BB44, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h47,
            8'h46,
            8'h45,
            8'h44,
            8'h43,
            8'h42,
            8'h41,
            8'h40
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h1;
		tb_fetch_miss_return_fetch16B = {
            16'h3377,
            16'h3366,
            16'h3355,
            16'h3344,
            16'h3333,
            16'h3322,
            16'h3311,
            16'h3300
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h2;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         5 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0m0,1h,2h,3h,4m2}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h5AA55AA55};
		tb_enq_info.tgt_pc38 = {35'h5AA55AA55, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h57,
            8'h56,
            8'h55,
            8'h54,
            8'h53,
            8'h52,
            8'h51,
            8'h50
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h1;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         6 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0m0,1h,2h,3h,4m2,5m1}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h699669966};
		tb_enq_info.tgt_pc38 = {35'h699669966, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h67,
            8'h66,
            8'h65,
            8'h64,
            8'h63,
            8'h62,
            8'h61,
            8'h60
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h3;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         7 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0m0,1h,2h,3h,4m2,5m1,6m3}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h788778877};
		tb_enq_info.tgt_pc38 = {35'h788778877, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h77,
            8'h76,
            8'h75,
            8'h74,
            8'h73,
            8'h72,
            8'h71,
            8'h70
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h4;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         restart",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0m0,1h,2h,3h,4m2,5m1,6m3,7m4}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b00000000;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h000000000};
		tb_enq_info.tgt_pc38 = {35'h000000000, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'h5;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         8 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h877887788};
		tb_enq_info.tgt_pc38 = {35'h877887788, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h87,
            8'h86,
            8'h85,
            8'h84,
            8'h83,
            8'h82,
            8'h81,
            8'h80
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h5;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'hD278, 16'hD278};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'hD278, 16'hD278};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         9 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h966996699};
		tb_enq_info.tgt_pc38 = {35'h966996699, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h97,
            8'h96,
            8'h95,
            8'h94,
            8'h93,
            8'h92,
            8'h91,
            8'h90
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h6;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h699669966, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h699669966, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h67;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h699669966, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h699669966, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h67;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h699669966, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h699669966, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h67;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h699669966, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h699669966, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h67;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         A miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5,9m6}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'hA55AA55AA};
		tb_enq_info.tgt_pc38 = {35'hA55AA55AA, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hA7,
            8'hA6,
            8'hA5,
            8'hA4,
            8'hA3,
            8'hA2,
            8'hA1,
            8'hA0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h7;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         B miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5,9m6,Am7}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'hB44BB44BB};
		tb_enq_info.tgt_pc38 = {35'hB44BB44BB, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hB7,
            8'hB6,
            8'hB5,
            8'hB4,
            8'hB3,
            8'hB2,
            8'hB1,
            8'hB0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h8;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         C miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5,9m6,Am7,Bm8}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'hC33CC33CC};
		tb_enq_info.tgt_pc38 = {35'hC33CC33CC, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hC7,
            8'hC6,
            8'hC5,
            8'hC4,
            8'hC3,
            8'hC2,
            8'hC1,
            8'hC0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h9;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         D miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5,9m6,Am7,Bm8,Cm9}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'hD22DD22DD};
		tb_enq_info.tgt_pc38 = {35'hD22DD22DD, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hD7,
            8'hD6,
            8'hD5,
            8'hD4,
            8'hD3,
            8'hD2,
            8'hD1,
            8'hD0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'hA;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         E miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5,9m6,Am7,Bm8,Cm9,DmA}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'hE11EE11EE};
		tb_enq_info.tgt_pc38 = {35'hE11EE11EE, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hE7,
            8'hE6,
            8'hE5,
            8'hE4,
            8'hE3,
            8'hE2,
            8'hE1,
            8'hE0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'hB;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         F miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5,9m6,Am7,Bm8,Cm9,DmA,EmB}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'hF00FF00FF};
		tb_enq_info.tgt_pc38 = {35'hF00FF00FF, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hF7,
            8'hF6,
            8'hF5,
            8'hF4,
            8'hF3,
            8'hF2,
            8'hF1,
            8'hF0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'hC;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         restart",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {8m5,9m6,Am7,Bm8,Cm9,DmA,EmB,FmC}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b0;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'hF00FF00FF};
		tb_enq_info.tgt_pc38 = {35'hF00FF00FF, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'hF7,
            8'hF6,
            8'hF5,
            8'hF4,
            8'hF3,
            8'hF2,
            8'hF1,
            8'hF0
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b1;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'hD;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         0 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h0FF00FF00};
		tb_enq_info.tgt_pc38 = {35'h0FF00FF00, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h07,
            8'h06,
            8'h05,
            8'h04,
            8'h03,
            8'h02,
            8'h01,
            8'h00
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'hD;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         1 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0mD}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h1EE11EE11};
		tb_enq_info.tgt_pc38 = {35'h1EE11EE11, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h17,
            8'h16,
            8'h15,
            8'h14,
            8'h13,
            8'h12,
            8'h11,
            8'h10
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'hE;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h87;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h87;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h87;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h877887788, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h877887788, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h87;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         2 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0mD,1mE}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h2DD22DD22};
		tb_enq_info.tgt_pc38 = {35'h2DD22DD22, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h27,
            8'h26,
            8'h25,
            8'h24,
            8'h23,
            8'h22,
            8'h21,
            8'h20
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'hF;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         3 hit",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0mD,1mE,2mF}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h3CC33CC33};
		tb_enq_info.tgt_pc38 = {35'h3CC33CC33, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h37,
            8'h36,
            8'h35,
            8'h34,
            8'h33,
            8'h32,
            8'h31,
            8'h30
        };
		tb_enq_fetch_hit_valid = 1'b1;
		tb_enq_fetch_hit_fetch16B = {
            16'h3377,
            16'h3366,
            16'h3355,
            16'h3344,
            16'h3333,
            16'h3322,
            16'h3311,
            16'h3300
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'hF; // default
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         4 miss (stall)",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0mD,1mE,2mF,3h}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h4BB44BB44};
		tb_enq_info.tgt_pc38 = {35'h4BB44BB44, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h47,
            8'h46,
            8'h45,
            8'h44,
            8'h43,
            8'h42,
            8'h41,
            8'h40
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'hF; // default
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         4 miss (stall)",
            "\n\t\tmiss ret:    m6",
            "\n\t\tbuffer:      {0mD,1mE,2mF,3h}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h4BB44BB44};
		tb_enq_info.tgt_pc38 = {35'h4BB44BB44, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h47,
            8'h46,
            8'h45,
            8'h44,
            8'h43,
            8'h42,
            8'h41,
            8'h40
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h6;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'hF; // default
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         4 miss",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0mD,1mE,2mF,3h}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h4BB44BB44};
		tb_enq_info.tgt_pc38 = {35'h4BB44BB44, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h47,
            8'h46,
            8'h45,
            8'h44,
            8'h43,
            8'h42,
            8'h41,
            8'h40
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b0;
		tb_fetch_miss_return_fmid = 4'h0;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b1;
		expected_enq_fmid = 4'h6;
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tenq:         5 miss (stall)",
            "\n\t\tmiss ret:    i",
            "\n\t\tbuffer:      {0mD,1mE,2mF,3h,4m6}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // enq
		tb_enq_valid = 1'b1;
		tb_enq_info.valid_by_lane = 8'b11111111;
		tb_enq_info.btb_hit_by_lane = 8'b00000000;
		tb_enq_info.redirect_taken_by_lane = 8'b00000000;
		tb_enq_info.bcb_idx = 4'h0;
		tb_enq_info.src_pc35 = {35'h5AA55AA55};
		tb_enq_info.tgt_pc38 = {35'h5AA55AA55, 3'h0};
		tb_enq_info.page_fault = 1'b0;
		tb_enq_info.access_fault = 1'b0;
		tb_enq_info.mdp_by_lane = {
            8'h57,
            8'h56,
            8'h55,
            8'h54,
            8'h53,
            8'h52,
            8'h51,
            8'h50
        };
		tb_enq_fetch_hit_valid = 1'b0;
		tb_enq_fetch_hit_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // enq feedback
	    // fetch miss return
		tb_fetch_miss_return_valid = 1'b1;
		tb_fetch_miss_return_fmid = 4'h6;
		tb_fetch_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // deq
	    // def feedback
		tb_instr_yield_ready = 1'b1;
	    // restart
		tb_restart_valid = 1'b0;

		@(negedge CLK);

		// outputs:

	    // enq
	    // enq feedback
		expected_enq_ready = 1'b0;
		expected_enq_fmid = 4'hF; // default
	    // fetch miss return
	    // deq
            // default: shift reg 1, lane 7
		expected_instr_yield_valid = 1'b0;

		expected_instr_yield_by_way[0].valid = 1'b0;
		expected_instr_yield_by_way[0].btb_hit = 1'b0;
		expected_instr_yield_by_way[0].redirect_taken = 1'b0;
		expected_instr_yield_by_way[0].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[0].bcb_idx = 4'h0;
		expected_instr_yield_by_way[0].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[0].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[0].page_fault = 1'b0;
		expected_instr_yield_by_way[0].access_fault = 1'b0;
		expected_instr_yield_by_way[0].mdp = 8'h07;
		expected_instr_yield_by_way[0].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[1].valid = 1'b0;
		expected_instr_yield_by_way[1].btb_hit = 1'b0;
		expected_instr_yield_by_way[1].redirect_taken = 1'b0;
		expected_instr_yield_by_way[1].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[1].bcb_idx = 4'h0;
		expected_instr_yield_by_way[1].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[1].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[1].page_fault = 1'b0;
		expected_instr_yield_by_way[1].access_fault = 1'b0;
		expected_instr_yield_by_way[1].mdp = 8'h07;
		expected_instr_yield_by_way[1].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[2].valid = 1'b0;
		expected_instr_yield_by_way[2].btb_hit = 1'b0;
		expected_instr_yield_by_way[2].redirect_taken = 1'b0;
		expected_instr_yield_by_way[2].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[2].bcb_idx = 4'h0;
		expected_instr_yield_by_way[2].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[2].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[2].page_fault = 1'b0;
		expected_instr_yield_by_way[2].access_fault = 1'b0;
		expected_instr_yield_by_way[2].mdp = 8'h07;
		expected_instr_yield_by_way[2].fetch4B = {16'h787F, 16'h787F};

		expected_instr_yield_by_way[3].valid = 1'b0;
		expected_instr_yield_by_way[3].btb_hit = 1'b0;
		expected_instr_yield_by_way[3].redirect_taken = 1'b0;
		expected_instr_yield_by_way[3].mid_instr_redirect = 1'b0;
		expected_instr_yield_by_way[3].bcb_idx = 4'h0;
		expected_instr_yield_by_way[3].src_pc38 = {35'h0FF00FF00, 3'h7};
		expected_instr_yield_by_way[3].tgt_pc38 = {35'h0FF00FF00, 3'h0};
		expected_instr_yield_by_way[3].page_fault = 1'b0;
		expected_instr_yield_by_way[3].access_fault = 1'b0;
		expected_instr_yield_by_way[3].mdp = 8'h07;
		expected_instr_yield_by_way[3].fetch4B = {16'h787F, 16'h787F};
	    // def feedback
	    // restart

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