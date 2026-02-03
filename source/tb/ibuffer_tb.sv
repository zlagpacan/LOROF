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

    // deq
	logic DUT_deq_valid, expected_deq_valid;
	corep::ibuffer_deq_entry_t [3:0] DUT_deq_entry_by_way, expected_deq_entry_by_way;

    // def feedback
	logic tb_deq_ready;

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

	    // deq
		.deq_valid(DUT_deq_valid),
		.deq_entry_by_way(DUT_deq_entry_by_way),

	    // def feedback
		.deq_ready(tb_deq_ready),

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

		if (expected_deq_valid !== DUT_deq_valid) begin
			$display("TB ERROR: expected_deq_valid (%h) != DUT_deq_valid (%h)",
				expected_deq_valid, DUT_deq_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_deq_entry_by_way !== DUT_deq_entry_by_way) begin
			$display("TB ERROR: expected_deq_entry_by_way (%h) != DUT_deq_entry_by_way (%h)",
				expected_deq_entry_by_way, DUT_deq_entry_by_way);
            $display();
			$display("\t\texpected_deq_entry_by_way[0].valid (%0h) \t%s\t DUT_deq_entry_by_way[0].valid (%0h)",
				expected_deq_entry_by_way[0].valid, expected_deq_entry_by_way[0].valid == DUT_deq_entry_by_way[0].valid ? "==" : "!=", DUT_deq_entry_by_way[0].valid);
			$display("\t\texpected_deq_entry_by_way[0].btb_hit (%0h) \t%s\t DUT_deq_entry_by_way[0].btb_hit (%0h)",
				expected_deq_entry_by_way[0].btb_hit, expected_deq_entry_by_way[0].btb_hit == DUT_deq_entry_by_way[0].btb_hit ? "==" : "!=", DUT_deq_entry_by_way[0].btb_hit);
			$display("\t\texpected_deq_entry_by_way[0].redirect_taken (%0h) \t%s\t DUT_deq_entry_by_way[0].redirect_taken (%0h)",
				expected_deq_entry_by_way[0].redirect_taken, expected_deq_entry_by_way[0].redirect_taken == DUT_deq_entry_by_way[0].redirect_taken ? "==" : "!=", DUT_deq_entry_by_way[0].redirect_taken);
			$display("\t\texpected_deq_entry_by_way[0].mid_instr_redirect (%0h) \t%s\t DUT_deq_entry_by_way[0].mid_instr_redirect (%0h)",
				expected_deq_entry_by_way[0].mid_instr_redirect, expected_deq_entry_by_way[0].mid_instr_redirect == DUT_deq_entry_by_way[0].mid_instr_redirect ? "==" : "!=", DUT_deq_entry_by_way[0].mid_instr_redirect);
			$display("\t\texpected_deq_entry_by_way[0].bcb_idx (%0h) \t%s\t DUT_deq_entry_by_way[0].bcb_idx (%0h)",
				expected_deq_entry_by_way[0].bcb_idx, expected_deq_entry_by_way[0].bcb_idx == DUT_deq_entry_by_way[0].bcb_idx ? "==" : "!=", DUT_deq_entry_by_way[0].bcb_idx);
			$display("\t\texpected_deq_entry_by_way[0].src_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[0].src_pc38 (%0h)",
				expected_deq_entry_by_way[0].src_pc38, expected_deq_entry_by_way[0].src_pc38 == DUT_deq_entry_by_way[0].src_pc38 ? "==" : "!=", DUT_deq_entry_by_way[0].src_pc38);
			$display("\t\texpected_deq_entry_by_way[0].tgt_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[0].tgt_pc38 (%0h)",
				expected_deq_entry_by_way[0].tgt_pc38, expected_deq_entry_by_way[0].tgt_pc38 == DUT_deq_entry_by_way[0].tgt_pc38 ? "==" : "!=", DUT_deq_entry_by_way[0].tgt_pc38);
			$display("\t\texpected_deq_entry_by_way[0].page_fault (%0h) \t%s\t DUT_deq_entry_by_way[0].page_fault (%0h)",
				expected_deq_entry_by_way[0].page_fault, expected_deq_entry_by_way[0].page_fault == DUT_deq_entry_by_way[0].page_fault ? "==" : "!=", DUT_deq_entry_by_way[0].page_fault);
			$display("\t\texpected_deq_entry_by_way[0].access_fault (%0h) \t%s\t DUT_deq_entry_by_way[0].access_fault (%0h)",
				expected_deq_entry_by_way[0].access_fault, expected_deq_entry_by_way[0].access_fault == DUT_deq_entry_by_way[0].access_fault ? "==" : "!=", DUT_deq_entry_by_way[0].access_fault);
			$display("\t\texpected_deq_entry_by_way[0].mdp (%0h) \t%s\t DUT_deq_entry_by_way[0].mdp (%0h)",
				expected_deq_entry_by_way[0].mdp, expected_deq_entry_by_way[0].mdp == DUT_deq_entry_by_way[0].mdp ? "==" : "!=", DUT_deq_entry_by_way[0].mdp);
			$display("\t\texpected_deq_entry_by_way[0].fetch4B (%0h) \t%s\t DUT_deq_entry_by_way[0].fetch4B (%0h)",
				expected_deq_entry_by_way[0].fetch4B, expected_deq_entry_by_way[0].fetch4B == DUT_deq_entry_by_way[0].fetch4B ? "==" : "!=", DUT_deq_entry_by_way[0].fetch4B);
            $display();
			$display("\t\texpected_deq_entry_by_way[1].valid (%0h) \t%s\t DUT_deq_entry_by_way[1].valid (%0h)",
				expected_deq_entry_by_way[1].valid, expected_deq_entry_by_way[1].valid == DUT_deq_entry_by_way[1].valid ? "==" : "!=", DUT_deq_entry_by_way[1].valid);
			$display("\t\texpected_deq_entry_by_way[1].btb_hit (%0h) \t%s\t DUT_deq_entry_by_way[1].btb_hit (%0h)",
				expected_deq_entry_by_way[1].btb_hit, expected_deq_entry_by_way[1].btb_hit == DUT_deq_entry_by_way[1].btb_hit ? "==" : "!=", DUT_deq_entry_by_way[1].btb_hit);
			$display("\t\texpected_deq_entry_by_way[1].redirect_taken (%0h) \t%s\t DUT_deq_entry_by_way[1].redirect_taken (%0h)",
				expected_deq_entry_by_way[1].redirect_taken, expected_deq_entry_by_way[1].redirect_taken == DUT_deq_entry_by_way[1].redirect_taken ? "==" : "!=", DUT_deq_entry_by_way[1].redirect_taken);
			$display("\t\texpected_deq_entry_by_way[1].mid_instr_redirect (%0h) \t%s\t DUT_deq_entry_by_way[1].mid_instr_redirect (%0h)",
				expected_deq_entry_by_way[1].mid_instr_redirect, expected_deq_entry_by_way[1].mid_instr_redirect == DUT_deq_entry_by_way[1].mid_instr_redirect ? "==" : "!=", DUT_deq_entry_by_way[1].mid_instr_redirect);
			$display("\t\texpected_deq_entry_by_way[1].bcb_idx (%0h) \t%s\t DUT_deq_entry_by_way[1].bcb_idx (%0h)",
				expected_deq_entry_by_way[1].bcb_idx, expected_deq_entry_by_way[1].bcb_idx == DUT_deq_entry_by_way[1].bcb_idx ? "==" : "!=", DUT_deq_entry_by_way[1].bcb_idx);
			$display("\t\texpected_deq_entry_by_way[1].src_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[1].src_pc38 (%0h)",
				expected_deq_entry_by_way[1].src_pc38, expected_deq_entry_by_way[1].src_pc38 == DUT_deq_entry_by_way[1].src_pc38 ? "==" : "!=", DUT_deq_entry_by_way[1].src_pc38);
			$display("\t\texpected_deq_entry_by_way[1].tgt_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[1].tgt_pc38 (%0h)",
				expected_deq_entry_by_way[1].tgt_pc38, expected_deq_entry_by_way[1].tgt_pc38 == DUT_deq_entry_by_way[1].tgt_pc38 ? "==" : "!=", DUT_deq_entry_by_way[1].tgt_pc38);
			$display("\t\texpected_deq_entry_by_way[1].page_fault (%0h) \t%s\t DUT_deq_entry_by_way[1].page_fault (%0h)",
				expected_deq_entry_by_way[1].page_fault, expected_deq_entry_by_way[1].page_fault == DUT_deq_entry_by_way[1].page_fault ? "==" : "!=", DUT_deq_entry_by_way[1].page_fault);
			$display("\t\texpected_deq_entry_by_way[1].access_fault (%0h) \t%s\t DUT_deq_entry_by_way[1].access_fault (%0h)",
				expected_deq_entry_by_way[1].access_fault, expected_deq_entry_by_way[1].access_fault == DUT_deq_entry_by_way[1].access_fault ? "==" : "!=", DUT_deq_entry_by_way[1].access_fault);
			$display("\t\texpected_deq_entry_by_way[1].mdp (%0h) \t%s\t DUT_deq_entry_by_way[1].mdp (%0h)",
				expected_deq_entry_by_way[1].mdp, expected_deq_entry_by_way[1].mdp == DUT_deq_entry_by_way[1].mdp ? "==" : "!=", DUT_deq_entry_by_way[1].mdp);
			$display("\t\texpected_deq_entry_by_way[1].fetch4B (%0h) \t%s\t DUT_deq_entry_by_way[1].fetch4B (%0h)",
				expected_deq_entry_by_way[1].fetch4B, expected_deq_entry_by_way[1].fetch4B == DUT_deq_entry_by_way[1].fetch4B ? "==" : "!=", DUT_deq_entry_by_way[1].fetch4B);
            $display();
			$display("\t\texpected_deq_entry_by_way[2].valid (%0h) \t%s\t DUT_deq_entry_by_way[2].valid (%0h)",
				expected_deq_entry_by_way[2].valid, expected_deq_entry_by_way[2].valid == DUT_deq_entry_by_way[2].valid ? "==" : "!=", DUT_deq_entry_by_way[2].valid);
			$display("\t\texpected_deq_entry_by_way[2].btb_hit (%0h) \t%s\t DUT_deq_entry_by_way[2].btb_hit (%0h)",
				expected_deq_entry_by_way[2].btb_hit, expected_deq_entry_by_way[2].btb_hit == DUT_deq_entry_by_way[2].btb_hit ? "==" : "!=", DUT_deq_entry_by_way[2].btb_hit);
			$display("\t\texpected_deq_entry_by_way[2].redirect_taken (%0h) \t%s\t DUT_deq_entry_by_way[2].redirect_taken (%0h)",
				expected_deq_entry_by_way[2].redirect_taken, expected_deq_entry_by_way[2].redirect_taken == DUT_deq_entry_by_way[2].redirect_taken ? "==" : "!=", DUT_deq_entry_by_way[2].redirect_taken);
			$display("\t\texpected_deq_entry_by_way[2].mid_instr_redirect (%0h) \t%s\t DUT_deq_entry_by_way[2].mid_instr_redirect (%0h)",
				expected_deq_entry_by_way[2].mid_instr_redirect, expected_deq_entry_by_way[2].mid_instr_redirect == DUT_deq_entry_by_way[2].mid_instr_redirect ? "==" : "!=", DUT_deq_entry_by_way[2].mid_instr_redirect);
			$display("\t\texpected_deq_entry_by_way[2].bcb_idx (%0h) \t%s\t DUT_deq_entry_by_way[2].bcb_idx (%0h)",
				expected_deq_entry_by_way[2].bcb_idx, expected_deq_entry_by_way[2].bcb_idx == DUT_deq_entry_by_way[2].bcb_idx ? "==" : "!=", DUT_deq_entry_by_way[2].bcb_idx);
			$display("\t\texpected_deq_entry_by_way[2].src_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[2].src_pc38 (%0h)",
				expected_deq_entry_by_way[2].src_pc38, expected_deq_entry_by_way[2].src_pc38 == DUT_deq_entry_by_way[2].src_pc38 ? "==" : "!=", DUT_deq_entry_by_way[2].src_pc38);
			$display("\t\texpected_deq_entry_by_way[2].tgt_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[2].tgt_pc38 (%0h)",
				expected_deq_entry_by_way[2].tgt_pc38, expected_deq_entry_by_way[2].tgt_pc38 == DUT_deq_entry_by_way[2].tgt_pc38 ? "==" : "!=", DUT_deq_entry_by_way[2].tgt_pc38);
			$display("\t\texpected_deq_entry_by_way[2].page_fault (%0h) \t%s\t DUT_deq_entry_by_way[2].page_fault (%0h)",
				expected_deq_entry_by_way[2].page_fault, expected_deq_entry_by_way[2].page_fault == DUT_deq_entry_by_way[2].page_fault ? "==" : "!=", DUT_deq_entry_by_way[2].page_fault);
			$display("\t\texpected_deq_entry_by_way[2].access_fault (%0h) \t%s\t DUT_deq_entry_by_way[2].access_fault (%0h)",
				expected_deq_entry_by_way[2].access_fault, expected_deq_entry_by_way[2].access_fault == DUT_deq_entry_by_way[2].access_fault ? "==" : "!=", DUT_deq_entry_by_way[2].access_fault);
			$display("\t\texpected_deq_entry_by_way[2].mdp (%0h) \t%s\t DUT_deq_entry_by_way[2].mdp (%0h)",
				expected_deq_entry_by_way[2].mdp, expected_deq_entry_by_way[2].mdp == DUT_deq_entry_by_way[2].mdp ? "==" : "!=", DUT_deq_entry_by_way[2].mdp);
			$display("\t\texpected_deq_entry_by_way[2].fetch4B (%0h) \t%s\t DUT_deq_entry_by_way[2].fetch4B (%0h)",
				expected_deq_entry_by_way[2].fetch4B, expected_deq_entry_by_way[2].fetch4B == DUT_deq_entry_by_way[2].fetch4B ? "==" : "!=", DUT_deq_entry_by_way[2].fetch4B);
            $display();
			$display("\t\texpected_deq_entry_by_way[3].valid (%0h) \t%s\t DUT_deq_entry_by_way[3].valid (%0h)",
				expected_deq_entry_by_way[3].valid, expected_deq_entry_by_way[3].valid == DUT_deq_entry_by_way[3].valid ? "==" : "!=", DUT_deq_entry_by_way[3].valid);
			$display("\t\texpected_deq_entry_by_way[3].btb_hit (%0h) \t%s\t DUT_deq_entry_by_way[3].btb_hit (%0h)",
				expected_deq_entry_by_way[3].btb_hit, expected_deq_entry_by_way[3].btb_hit == DUT_deq_entry_by_way[3].btb_hit ? "==" : "!=", DUT_deq_entry_by_way[3].btb_hit);
			$display("\t\texpected_deq_entry_by_way[3].redirect_taken (%0h) \t%s\t DUT_deq_entry_by_way[3].redirect_taken (%0h)",
				expected_deq_entry_by_way[3].redirect_taken, expected_deq_entry_by_way[3].redirect_taken == DUT_deq_entry_by_way[3].redirect_taken ? "==" : "!=", DUT_deq_entry_by_way[3].redirect_taken);
			$display("\t\texpected_deq_entry_by_way[3].mid_instr_redirect (%0h) \t%s\t DUT_deq_entry_by_way[3].mid_instr_redirect (%0h)",
				expected_deq_entry_by_way[3].mid_instr_redirect, expected_deq_entry_by_way[3].mid_instr_redirect == DUT_deq_entry_by_way[3].mid_instr_redirect ? "==" : "!=", DUT_deq_entry_by_way[3].mid_instr_redirect);
			$display("\t\texpected_deq_entry_by_way[3].bcb_idx (%0h) \t%s\t DUT_deq_entry_by_way[3].bcb_idx (%0h)",
				expected_deq_entry_by_way[3].bcb_idx, expected_deq_entry_by_way[3].bcb_idx == DUT_deq_entry_by_way[3].bcb_idx ? "==" : "!=", DUT_deq_entry_by_way[3].bcb_idx);
			$display("\t\texpected_deq_entry_by_way[3].src_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[3].src_pc38 (%0h)",
				expected_deq_entry_by_way[3].src_pc38, expected_deq_entry_by_way[3].src_pc38 == DUT_deq_entry_by_way[3].src_pc38 ? "==" : "!=", DUT_deq_entry_by_way[3].src_pc38);
			$display("\t\texpected_deq_entry_by_way[3].tgt_pc38 (%0h) \t%s\t DUT_deq_entry_by_way[3].tgt_pc38 (%0h)",
				expected_deq_entry_by_way[3].tgt_pc38, expected_deq_entry_by_way[3].tgt_pc38 == DUT_deq_entry_by_way[3].tgt_pc38 ? "==" : "!=", DUT_deq_entry_by_way[3].tgt_pc38);
			$display("\t\texpected_deq_entry_by_way[3].page_fault (%0h) \t%s\t DUT_deq_entry_by_way[3].page_fault (%0h)",
				expected_deq_entry_by_way[3].page_fault, expected_deq_entry_by_way[3].page_fault == DUT_deq_entry_by_way[3].page_fault ? "==" : "!=", DUT_deq_entry_by_way[3].page_fault);
			$display("\t\texpected_deq_entry_by_way[3].access_fault (%0h) \t%s\t DUT_deq_entry_by_way[3].access_fault (%0h)",
				expected_deq_entry_by_way[3].access_fault, expected_deq_entry_by_way[3].access_fault == DUT_deq_entry_by_way[3].access_fault ? "==" : "!=", DUT_deq_entry_by_way[3].access_fault);
			$display("\t\texpected_deq_entry_by_way[3].mdp (%0h) \t%s\t DUT_deq_entry_by_way[3].mdp (%0h)",
				expected_deq_entry_by_way[3].mdp, expected_deq_entry_by_way[3].mdp == DUT_deq_entry_by_way[3].mdp ? "==" : "!=", DUT_deq_entry_by_way[3].mdp);
			$display("\t\texpected_deq_entry_by_way[3].fetch4B (%0h) \t%s\t DUT_deq_entry_by_way[3].fetch4B (%0h)",
				expected_deq_entry_by_way[3].fetch4B, expected_deq_entry_by_way[3].fetch4B == DUT_deq_entry_by_way[3].fetch4B ? "==" : "!=", DUT_deq_entry_by_way[3].fetch4B);

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
		tb_deq_ready = 1'b0;
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

		expected_deq_valid = 1'b0;
		expected_deq_entry_by_way[0].valid = 1'b0;
		expected_deq_entry_by_way[0].btb_hit = 1'b0;
		expected_deq_entry_by_way[0].redirect_taken = 1'b0;
		expected_deq_entry_by_way[0].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[0].bcb_idx = 4'h0;
		expected_deq_entry_by_way[0].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[0].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[0].page_fault = 1'b0;
		expected_deq_entry_by_way[0].access_fault = 1'b0;
		expected_deq_entry_by_way[0].mdp = 8'h00;
		expected_deq_entry_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[1].valid = 1'b0;
		expected_deq_entry_by_way[1].btb_hit = 1'b0;
		expected_deq_entry_by_way[1].redirect_taken = 1'b0;
		expected_deq_entry_by_way[1].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[1].bcb_idx = 4'h0;
		expected_deq_entry_by_way[1].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[1].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[1].page_fault = 1'b0;
		expected_deq_entry_by_way[1].access_fault = 1'b0;
		expected_deq_entry_by_way[1].mdp = 8'h00;
		expected_deq_entry_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[2].valid = 1'b0;
		expected_deq_entry_by_way[2].btb_hit = 1'b0;
		expected_deq_entry_by_way[2].redirect_taken = 1'b0;
		expected_deq_entry_by_way[2].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[2].bcb_idx = 4'h0;
		expected_deq_entry_by_way[2].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[2].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[2].page_fault = 1'b0;
		expected_deq_entry_by_way[2].access_fault = 1'b0;
		expected_deq_entry_by_way[2].mdp = 8'h00;
		expected_deq_entry_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[3].valid = 1'b0;
		expected_deq_entry_by_way[3].btb_hit = 1'b0;
		expected_deq_entry_by_way[3].redirect_taken = 1'b0;
		expected_deq_entry_by_way[3].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[3].bcb_idx = 4'h0;
		expected_deq_entry_by_way[3].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[3].page_fault = 1'b0;
		expected_deq_entry_by_way[3].access_fault = 1'b0;
		expected_deq_entry_by_way[3].mdp = 8'h00;
		expected_deq_entry_by_way[3].fetch4B = {16'h0000, 16'h0000};
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
		tb_deq_ready = 1'b0;
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
		expected_deq_valid = 1'b0;
		expected_deq_entry_by_way[0].valid = 1'b0;
		expected_deq_entry_by_way[0].btb_hit = 1'b0;
		expected_deq_entry_by_way[0].redirect_taken = 1'b0;
		expected_deq_entry_by_way[0].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[0].bcb_idx = 4'h0;
		expected_deq_entry_by_way[0].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[0].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[0].page_fault = 1'b0;
		expected_deq_entry_by_way[0].access_fault = 1'b0;
		expected_deq_entry_by_way[0].mdp = 8'h00;
		expected_deq_entry_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[1].valid = 1'b0;
		expected_deq_entry_by_way[1].btb_hit = 1'b0;
		expected_deq_entry_by_way[1].redirect_taken = 1'b0;
		expected_deq_entry_by_way[1].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[1].bcb_idx = 4'h0;
		expected_deq_entry_by_way[1].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[1].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[1].page_fault = 1'b0;
		expected_deq_entry_by_way[1].access_fault = 1'b0;
		expected_deq_entry_by_way[1].mdp = 8'h00;
		expected_deq_entry_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[2].valid = 1'b0;
		expected_deq_entry_by_way[2].btb_hit = 1'b0;
		expected_deq_entry_by_way[2].redirect_taken = 1'b0;
		expected_deq_entry_by_way[2].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[2].bcb_idx = 4'h0;
		expected_deq_entry_by_way[2].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[2].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[2].page_fault = 1'b0;
		expected_deq_entry_by_way[2].access_fault = 1'b0;
		expected_deq_entry_by_way[2].mdp = 8'h00;
		expected_deq_entry_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[3].valid = 1'b0;
		expected_deq_entry_by_way[3].btb_hit = 1'b0;
		expected_deq_entry_by_way[3].redirect_taken = 1'b0;
		expected_deq_entry_by_way[3].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[3].bcb_idx = 4'h0;
		expected_deq_entry_by_way[3].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[3].page_fault = 1'b0;
		expected_deq_entry_by_way[3].access_fault = 1'b0;
		expected_deq_entry_by_way[3].mdp = 8'h00;
		expected_deq_entry_by_way[3].fetch4B = {16'h0000, 16'h0000};
	    // def feedback
	    // restart

		check_outputs();

        // ------------------------------------------------------------
        // default:
        test_case = "default";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "default";
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
		tb_deq_ready = 1'b0;
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
		expected_deq_valid = 1'b0;
		expected_deq_entry_by_way[0].valid = 1'b0;
		expected_deq_entry_by_way[0].btb_hit = 1'b0;
		expected_deq_entry_by_way[0].redirect_taken = 1'b0;
		expected_deq_entry_by_way[0].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[0].bcb_idx = 4'h0;
		expected_deq_entry_by_way[0].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[0].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[0].page_fault = 1'b0;
		expected_deq_entry_by_way[0].access_fault = 1'b0;
		expected_deq_entry_by_way[0].mdp = 8'h00;
		expected_deq_entry_by_way[0].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[1].valid = 1'b0;
		expected_deq_entry_by_way[1].btb_hit = 1'b0;
		expected_deq_entry_by_way[1].redirect_taken = 1'b0;
		expected_deq_entry_by_way[1].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[1].bcb_idx = 4'h0;
		expected_deq_entry_by_way[1].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[1].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[1].page_fault = 1'b0;
		expected_deq_entry_by_way[1].access_fault = 1'b0;
		expected_deq_entry_by_way[1].mdp = 8'h00;
		expected_deq_entry_by_way[1].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[2].valid = 1'b0;
		expected_deq_entry_by_way[2].btb_hit = 1'b0;
		expected_deq_entry_by_way[2].redirect_taken = 1'b0;
		expected_deq_entry_by_way[2].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[2].bcb_idx = 4'h0;
		expected_deq_entry_by_way[2].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[2].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[2].page_fault = 1'b0;
		expected_deq_entry_by_way[2].access_fault = 1'b0;
		expected_deq_entry_by_way[2].mdp = 8'h00;
		expected_deq_entry_by_way[2].fetch4B = {16'h0000, 16'h0000};

		expected_deq_entry_by_way[3].valid = 1'b0;
		expected_deq_entry_by_way[3].btb_hit = 1'b0;
		expected_deq_entry_by_way[3].redirect_taken = 1'b0;
		expected_deq_entry_by_way[3].mid_instr_redirect = 1'b0;
		expected_deq_entry_by_way[3].bcb_idx = 4'h0;
		expected_deq_entry_by_way[3].src_pc38 = {35'h000000000, 3'h7};
		expected_deq_entry_by_way[3].tgt_pc38 = {35'h000000000, 3'h0};
		expected_deq_entry_by_way[3].page_fault = 1'b0;
		expected_deq_entry_by_way[3].access_fault = 1'b0;
		expected_deq_entry_by_way[3].mdp = 8'h00;
		expected_deq_entry_by_way[3].fetch4B = {16'h0000, 16'h0000};
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