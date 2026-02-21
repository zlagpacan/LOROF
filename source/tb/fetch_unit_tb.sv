/*
    Filename: fetch_unit_tb.sv
    Author: zlagpacan
    Description: Testbench for fetch_unit module. 
    Spec: LOROF/spec/design/fetch_unit.md
*/

`timescale 1ns/100ps

`include "corep.vh"
`include "sysp.vh"

module fetch_unit_tb #(
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


    // itlb req
	logic DUT_itlb_req_valid, expected_itlb_req_valid;
	corep::asid_t DUT_itlb_req_asid, expected_itlb_req_asid;
	corep::exec_mode_t DUT_itlb_req_exec_mode, expected_itlb_req_exec_mode;
	logic DUT_itlb_req_virtual_mode, expected_itlb_req_virtual_mode;
	corep::fetch_idx_t DUT_itlb_req_fetch_idx, expected_itlb_req_fetch_idx;

    // itlb resp
	sysp::vpn_t DUT_itlb_resp_vpn, expected_itlb_resp_vpn;

	logic tb_itlb_resp_valid;
	sysp::ppn_t tb_itlb_resp_ppn;
	logic tb_itlb_resp_page_fault;
	logic tb_itlb_resp_access_fault;

    // icache req
	logic DUT_icache_req_valid, expected_icache_req_valid;
	corep::fetch_idx_t DUT_icache_req_fetch_idx, expected_icache_req_fetch_idx;

    // icache resp
	logic [sysp::ICACHE_ASSOC-1:0] tb_icache_resp_valid_by_way;
	sysp::icache_tag_t [sysp::ICACHE_ASSOC-1:0] tb_icache_resp_tag_by_way;
	corep::fetch16B_t [sysp::ICACHE_ASSOC-1:0] tb_icache_resp_fetch16B_by_way;

    // icache feedback hit
	logic DUT_icache_feedback_hit_valid, expected_icache_feedback_hit_valid;
	sysp::icache_way_t DUT_icache_feedback_hit_way, expected_icache_feedback_hit_way;

    // icache feedback miss
	logic DUT_icache_feedback_miss_valid, expected_icache_feedback_miss_valid;
	corep::fmid_t DUT_icache_feedback_miss_fmid, expected_icache_feedback_miss_fmid;
	sysp::pa39_t DUT_icache_feedback_miss_pa39, expected_icache_feedback_miss_pa39;

	logic tb_icache_feedback_miss_ready;

    // icache miss return
	logic tb_icache_miss_return_valid;
	corep::fmid_t tb_icache_miss_return_fmid;
	corep::fetch16B_t tb_icache_miss_return_fetch16B;

    // instr yield
	logic DUT_instr_yield_valid, expected_instr_yield_valid;
	corep::instr_yield_t [3:0] DUT_instr_yield_by_way, expected_instr_yield_by_way;

    // instr yield feedback
	logic tb_instr_yield_ready;

    // wfr trigger from rob
	logic tb_rob_trigger_wfr;

    // restart from ROB (non-branch restarts)
	logic tb_rob_restart_valid;
	corep::bcb_idx_t tb_rob_restart_bcb_idx;
	corep::pc38_t tb_rob_restart_pc38;
	corep::asid_t tb_rob_restart_asid;
	corep::exec_mode_t tb_rob_restart_exec_mode;
	logic tb_rob_restart_virtual_mode;

    // wfr trigger from decode_unit
	logic tb_decode_unit_trigger_wfr;

    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	logic tb_decode_unit_restart_valid;
	corep::bcb_idx_t tb_decode_unit_restart_bcb_idx;
	corep::pc38_t tb_decode_unit_restart_pc38;

    // branch update (and also restart if mispred)
	logic tb_branch_update_valid;
	logic tb_branch_update_mispred;
	corep::bcb_idx_t tb_branch_update_bcb_idx;
	corep::pc38_t tb_branch_update_src_pc38;
	corep::asid_t tb_branch_update_asid;
	corep::btb_info_t tb_branch_update_btb_info;
	corep::pc38_t tb_branch_update_tgt_pc38;
	logic tb_branch_update_taken;
	logic tb_branch_update_btb_hit;

	logic DUT_branch_update_ready, expected_branch_update_ready;

    // mdpt update
	logic tb_mdpt_update_valid;
	corep::pc38_t tb_mdpt_update_pc38;
	corep::asid_t tb_mdpt_update_asid;
	corep::mdp_t tb_mdpt_update_mdp;

    // ----------------------------------------------------------------
    // DUT instantiation:

	fetch_unit #(
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // itlb req
		.itlb_req_valid(DUT_itlb_req_valid),
		.itlb_req_asid(DUT_itlb_req_asid),
		.itlb_req_exec_mode(DUT_itlb_req_exec_mode),
		.itlb_req_virtual_mode(DUT_itlb_req_virtual_mode),
		.itlb_req_fetch_idx(DUT_itlb_req_fetch_idx),

	    // itlb resp
		.itlb_resp_vpn(DUT_itlb_resp_vpn),

		.itlb_resp_valid(tb_itlb_resp_valid),
		.itlb_resp_ppn(tb_itlb_resp_ppn),
		.itlb_resp_page_fault(tb_itlb_resp_page_fault),
		.itlb_resp_access_fault(tb_itlb_resp_access_fault),

	    // icache req
		.icache_req_valid(DUT_icache_req_valid),
		.icache_req_fetch_idx(DUT_icache_req_fetch_idx),

	    // icache resp
		.icache_resp_valid_by_way(tb_icache_resp_valid_by_way),
		.icache_resp_tag_by_way(tb_icache_resp_tag_by_way),
		.icache_resp_fetch16B_by_way(tb_icache_resp_fetch16B_by_way),

	    // icache feedback hit
		.icache_feedback_hit_valid(DUT_icache_feedback_hit_valid),
		.icache_feedback_hit_way(DUT_icache_feedback_hit_way),

	    // icache feedback miss
		.icache_feedback_miss_valid(DUT_icache_feedback_miss_valid),
		.icache_feedback_miss_fmid(DUT_icache_feedback_miss_fmid),
		.icache_feedback_miss_pa39(DUT_icache_feedback_miss_pa39),

		.icache_feedback_miss_ready(tb_icache_feedback_miss_ready),

	    // icache miss return
		.icache_miss_return_valid(tb_icache_miss_return_valid),
		.icache_miss_return_fmid(tb_icache_miss_return_fmid),
		.icache_miss_return_fetch16B(tb_icache_miss_return_fetch16B),

	    // instr yield
		.instr_yield_valid(DUT_instr_yield_valid),
		.instr_yield_by_way(DUT_instr_yield_by_way),

	    // instr yield feedback
		.instr_yield_ready(tb_instr_yield_ready),

	    // wfr trigger from rob
		.rob_trigger_wfr(tb_rob_trigger_wfr),

	    // restart from ROB (non-branch restarts)
		.rob_restart_valid(tb_rob_restart_valid),
		.rob_restart_bcb_idx(tb_rob_restart_bcb_idx),
		.rob_restart_pc38(tb_rob_restart_pc38),
		.rob_restart_asid(tb_rob_restart_asid),
		.rob_restart_exec_mode(tb_rob_restart_exec_mode),
		.rob_restart_virtual_mode(tb_rob_restart_virtual_mode),

	    // wfr trigger from decode_unit
		.decode_unit_trigger_wfr(tb_decode_unit_trigger_wfr),

	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
		.decode_unit_restart_valid(tb_decode_unit_restart_valid),
		.decode_unit_restart_bcb_idx(tb_decode_unit_restart_bcb_idx),
		.decode_unit_restart_pc38(tb_decode_unit_restart_pc38),

	    // branch update (and also restart if mispred)
		.branch_update_valid(tb_branch_update_valid),
		.branch_update_mispred(tb_branch_update_mispred),
		.branch_update_bcb_idx(tb_branch_update_bcb_idx),
		.branch_update_src_pc38(tb_branch_update_src_pc38),
		.branch_update_asid(tb_branch_update_asid),
		.branch_update_btb_info(tb_branch_update_btb_info),
		.branch_update_tgt_pc38(tb_branch_update_tgt_pc38),
		.branch_update_taken(tb_branch_update_taken),
		.branch_update_btb_hit(tb_branch_update_btb_hit),

		.branch_update_ready(DUT_branch_update_ready),

	    // mdpt update
		.mdpt_update_valid(tb_mdpt_update_valid),
		.mdpt_update_pc38(tb_mdpt_update_pc38),
		.mdpt_update_asid(tb_mdpt_update_asid),
		.mdpt_update_mdp(tb_mdpt_update_mdp)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_itlb_req_valid !== DUT_itlb_req_valid) begin
			$display("TB ERROR: expected_itlb_req_valid (%h) != DUT_itlb_req_valid (%h)",
				expected_itlb_req_valid, DUT_itlb_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_asid !== DUT_itlb_req_asid) begin
			$display("TB ERROR: expected_itlb_req_asid (%h) != DUT_itlb_req_asid (%h)",
				expected_itlb_req_asid, DUT_itlb_req_asid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_exec_mode !== DUT_itlb_req_exec_mode) begin
			$display("TB ERROR: expected_itlb_req_exec_mode (%h) != DUT_itlb_req_exec_mode (%h)",
				expected_itlb_req_exec_mode, DUT_itlb_req_exec_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_virtual_mode !== DUT_itlb_req_virtual_mode) begin
			$display("TB ERROR: expected_itlb_req_virtual_mode (%h) != DUT_itlb_req_virtual_mode (%h)",
				expected_itlb_req_virtual_mode, DUT_itlb_req_virtual_mode);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_fetch_idx !== DUT_itlb_req_fetch_idx) begin
			$display("TB ERROR: expected_itlb_req_fetch_idx (%h) != DUT_itlb_req_fetch_idx (%h)",
				expected_itlb_req_fetch_idx, DUT_itlb_req_fetch_idx);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_resp_vpn !== DUT_itlb_resp_vpn) begin
			$display("TB ERROR: expected_itlb_resp_vpn (%h) != DUT_itlb_resp_vpn (%h)",
				expected_itlb_resp_vpn, DUT_itlb_resp_vpn);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_valid !== DUT_icache_req_valid) begin
			$display("TB ERROR: expected_icache_req_valid (%h) != DUT_icache_req_valid (%h)",
				expected_icache_req_valid, DUT_icache_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_fetch_idx !== DUT_icache_req_fetch_idx) begin
			$display("TB ERROR: expected_icache_req_fetch_idx (%h) != DUT_icache_req_fetch_idx (%h)",
				expected_icache_req_fetch_idx, DUT_icache_req_fetch_idx);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_feedback_hit_valid !== DUT_icache_feedback_hit_valid) begin
			$display("TB ERROR: expected_icache_feedback_hit_valid (%h) != DUT_icache_feedback_hit_valid (%h)",
				expected_icache_feedback_hit_valid, DUT_icache_feedback_hit_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_feedback_hit_way !== DUT_icache_feedback_hit_way) begin
			$display("TB ERROR: expected_icache_feedback_hit_way (%h) != DUT_icache_feedback_hit_way (%h)",
				expected_icache_feedback_hit_way, DUT_icache_feedback_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_feedback_miss_valid !== DUT_icache_feedback_miss_valid) begin
			$display("TB ERROR: expected_icache_feedback_miss_valid (%h) != DUT_icache_feedback_miss_valid (%h)",
				expected_icache_feedback_miss_valid, DUT_icache_feedback_miss_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_feedback_miss_fmid !== DUT_icache_feedback_miss_fmid) begin
			$display("TB ERROR: expected_icache_feedback_miss_fmid (%h) != DUT_icache_feedback_miss_fmid (%h)",
				expected_icache_feedback_miss_fmid, DUT_icache_feedback_miss_fmid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_feedback_miss_pa39 !== DUT_icache_feedback_miss_pa39) begin
			$display("TB ERROR: expected_icache_feedback_miss_pa39 (%h) != DUT_icache_feedback_miss_pa39 (%h)",
				expected_icache_feedback_miss_pa39, DUT_icache_feedback_miss_pa39);
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

		if (expected_branch_update_ready !== DUT_branch_update_ready) begin
			$display("TB ERROR: expected_branch_update_ready (%h) != DUT_branch_update_ready (%h)",
				expected_branch_update_ready, DUT_branch_update_ready);
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
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_ppn = 27'h0000000;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {27'h0000000, 27'h0000000};
		tb_icache_resp_fetch16B_by_way = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,

            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // icache feedback hit
	    // icache feedback miss
		tb_icache_feedback_miss_ready = 1'b1;
	    // icache miss return
		tb_icache_miss_return_valid = 1'b0;
		tb_icache_miss_return_fmid = 4'h0;
		tb_icache_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // instr yield
	    // instr yield feedback
		tb_instr_yield_ready = 1'b1;
	    // wfr trigger from rob
		tb_rob_trigger_wfr = 1'b0;
	    // restart from ROB (non-branch restarts)
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_bcb_idx = 4'h0;
		tb_rob_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_rob_restart_asid = 16'h0000;
		tb_rob_restart_exec_mode = corep::EXEC_MODE_M;
		tb_rob_restart_virtual_mode = 1'b0;
	    // wfr trigger from decode_unit
		tb_decode_unit_trigger_wfr = 1'b0;
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
		tb_decode_unit_restart_valid = 1'b0;
		tb_decode_unit_restart_bcb_idx = 4'h0;
		tb_decode_unit_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
	    // branch update (and also restart if mispred)
		tb_branch_update_valid = 1'b0;
		tb_branch_update_mispred = 1'b0;
		tb_branch_update_bcb_idx = 4'h0;
		tb_branch_update_src_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_asid = 16'h0000;
		tb_branch_update_btb_info = {3'h0, 1'b0, 3'h0, 9'h000, 3'h0};
		tb_branch_update_tgt_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_taken = 1'b0;
		tb_branch_update_btb_hit = 1'b0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_mdpt_update_asid = 16'h0000;
		tb_mdpt_update_mdp = 8'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b0;
		expected_itlb_req_asid = 16'h0000;
		expected_itlb_req_exec_mode = corep::EXEC_MODE_M;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_fetch_idx = 9'h000;
	    // itlb resp
		expected_itlb_resp_vpn = {23'h000000, 3'h0};
	    // icache req
		expected_icache_req_valid = 1'b0;
		expected_icache_req_fetch_idx = 9'h000;
	    // icache resp
	    // icache feedback hit
		expected_icache_feedback_hit_valid = 1'b0;
		expected_icache_feedback_hit_way = 1'b0;
	    // icache feedback miss
		expected_icache_feedback_miss_valid = 1'b0;
		expected_icache_feedback_miss_fmid = 4'h0;
		expected_icache_feedback_miss_pa39 = {23'h000000, 3'h0, 9'h000, 3'h0, 1'b0};
	    // icache miss return
	    // instr yield
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
	    // instr yield feedback
	    // wfr trigger from rob
	    // restart from ROB (non-branch restarts)
	    // wfr trigger from decode_unit
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	    // branch update (and also restart if mispred)
		expected_branch_update_ready = 1'b1;
	    // mdpt update

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_ppn = 27'h0000000;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {27'h0000000, 27'h0000000};
		tb_icache_resp_fetch16B_by_way = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,

            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // icache feedback hit
	    // icache feedback miss
		tb_icache_feedback_miss_ready = 1'b1;
	    // icache miss return
		tb_icache_miss_return_valid = 1'b0;
		tb_icache_miss_return_fmid = 4'h0;
		tb_icache_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // instr yield
	    // instr yield feedback
		tb_instr_yield_ready = 1'b1;
	    // wfr trigger from rob
		tb_rob_trigger_wfr = 1'b0;
	    // restart from ROB (non-branch restarts)
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_bcb_idx = 4'h0;
		tb_rob_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_rob_restart_asid = 16'h0000;
		tb_rob_restart_exec_mode = corep::EXEC_MODE_M;
		tb_rob_restart_virtual_mode = 1'b0;
	    // wfr trigger from decode_unit
		tb_decode_unit_trigger_wfr = 1'b0;
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
		tb_decode_unit_restart_valid = 1'b0;
		tb_decode_unit_restart_bcb_idx = 4'h0;
		tb_decode_unit_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
	    // branch update (and also restart if mispred)
		tb_branch_update_valid = 1'b0;
		tb_branch_update_mispred = 1'b0;
		tb_branch_update_bcb_idx = 4'h0;
		tb_branch_update_src_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_asid = 16'h0000;
		tb_branch_update_btb_info = {3'h0, 1'b0, 3'h0, 9'h000, 3'h0};
		tb_branch_update_tgt_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_taken = 1'b0;
		tb_branch_update_btb_hit = 1'b0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_mdpt_update_asid = 16'h0000;
		tb_mdpt_update_mdp = 8'h00;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b0;
		expected_itlb_req_asid = 16'h0000;
		expected_itlb_req_exec_mode = corep::EXEC_MODE_M;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_fetch_idx = 9'h000;
	    // itlb resp
		expected_itlb_resp_vpn = {23'h000000, 3'h0};
	    // icache req
		expected_icache_req_valid = 1'b0;
		expected_icache_req_fetch_idx = 9'h000;
	    // icache resp
	    // icache feedback hit
		expected_icache_feedback_hit_valid = 1'b0;
		expected_icache_feedback_hit_way = 1'b0;
	    // icache feedback miss
		expected_icache_feedback_miss_valid = 1'b0;
		expected_icache_feedback_miss_fmid = 4'h0;
		expected_icache_feedback_miss_pa39 = {23'h000000, 3'h0, 9'h000, 3'h0, 1'b0};
	    // icache miss return
	    // instr yield
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
	    // instr yield feedback
	    // wfr trigger from rob
	    // restart from ROB (non-branch restarts)
	    // wfr trigger from decode_unit
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	    // branch update (and also restart if mispred)
		expected_branch_update_ready = 1'b1;
	    // mdpt update

		check_outputs();

        // ------------------------------------------------------------
        // simple chain:
        test_case = "simple chain";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "rob restart";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_ppn = 27'h0000000;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {27'h0000000, 27'h0000000};
		tb_icache_resp_fetch16B_by_way = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,

            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // icache feedback hit
	    // icache feedback miss
		tb_icache_feedback_miss_ready = 1'b1;
	    // icache miss return
		tb_icache_miss_return_valid = 1'b0;
		tb_icache_miss_return_fmid = 4'h0;
		tb_icache_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // instr yield
	    // instr yield feedback
		tb_instr_yield_ready = 1'b1;
	    // wfr trigger from rob
		tb_rob_trigger_wfr = 1'b0;
	    // restart from ROB (non-branch restarts)
		tb_rob_restart_valid = 1'b1;
		tb_rob_restart_bcb_idx = 4'h0;
		tb_rob_restart_pc38 = {23'h100000, 3'h0, 9'h000, 3'h0};
		tb_rob_restart_asid = 16'h0000;
		tb_rob_restart_exec_mode = corep::EXEC_MODE_M;
		tb_rob_restart_virtual_mode = 1'b0;
	    // wfr trigger from decode_unit
		tb_decode_unit_trigger_wfr = 1'b0;
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
		tb_decode_unit_restart_valid = 1'b0;
		tb_decode_unit_restart_bcb_idx = 4'h0;
		tb_decode_unit_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
	    // branch update (and also restart if mispred)
		tb_branch_update_valid = 1'b0;
		tb_branch_update_mispred = 1'b0;
		tb_branch_update_bcb_idx = 4'h0;
		tb_branch_update_src_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_asid = 16'h0000;
		tb_branch_update_btb_info = {3'h0, 1'b0, 3'h0, 9'h000, 3'h0};
		tb_branch_update_tgt_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_taken = 1'b0;
		tb_branch_update_btb_hit = 1'b0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_mdpt_update_asid = 16'h0000;
		tb_mdpt_update_mdp = 8'h00;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b0;
		expected_itlb_req_asid = 16'h0000;
		expected_itlb_req_exec_mode = corep::EXEC_MODE_M;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_fetch_idx = 9'h000;
	    // itlb resp
		expected_itlb_resp_vpn = {23'h000000, 3'h0};
	    // icache req
		expected_icache_req_valid = 1'b0;
		expected_icache_req_fetch_idx = 9'h000;
	    // icache resp
	    // icache feedback hit
		expected_icache_feedback_hit_valid = 1'b0;
		expected_icache_feedback_hit_way = 1'b0;
	    // icache feedback miss
		expected_icache_feedback_miss_valid = 1'b0;
		expected_icache_feedback_miss_fmid = 4'h0;
		expected_icache_feedback_miss_pa39 = {23'h000000, 3'h0, 9'h000, 3'h0, 1'b0};
	    // icache miss return
	    // instr yield
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
	    // instr yield feedback
	    // wfr trigger from rob
	    // restart from ROB (non-branch restarts)
	    // wfr trigger from decode_unit
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	    // branch update (and also restart if mispred)
		expected_branch_update_ready = 1'b1;
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tREQ:         0",
            "\n\t\tRESP:        i",
            "\n\t\tmiss ret:    i", 
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 27'h0f0f0f0;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {27'h0000000, 27'h0f0f0f0};
		tb_icache_resp_fetch16B_by_way = {
            16'h0070,
            16'h0060,
            16'h0050,
            16'h0040,
            16'h0030,
            16'h0020,
            16'h0010,
            16'h0000,

            16'hf070,
            16'hf060,
            16'hf050,
            16'hf040,
            16'hf030,
            16'hf020,
            16'hf010,
            16'hf000
        };
	    // icache feedback hit
	    // icache feedback miss
		tb_icache_feedback_miss_ready = 1'b1;
	    // icache miss return
		tb_icache_miss_return_valid = 1'b0;
		tb_icache_miss_return_fmid = 4'h0;
		tb_icache_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // instr yield
	    // instr yield feedback
		tb_instr_yield_ready = 1'b1;
	    // wfr trigger from rob
		tb_rob_trigger_wfr = 1'b0;
	    // restart from ROB (non-branch restarts)
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_bcb_idx = 4'h0;
		tb_rob_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_rob_restart_asid = 16'h0000;
		tb_rob_restart_exec_mode = corep::EXEC_MODE_M;
		tb_rob_restart_virtual_mode = 1'b0;
	    // wfr trigger from decode_unit
		tb_decode_unit_trigger_wfr = 1'b0;
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
		tb_decode_unit_restart_valid = 1'b0;
		tb_decode_unit_restart_bcb_idx = 4'h0;
		tb_decode_unit_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
	    // branch update (and also restart if mispred)
		tb_branch_update_valid = 1'b0;
		tb_branch_update_mispred = 1'b0;
		tb_branch_update_bcb_idx = 4'h0;
		tb_branch_update_src_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_asid = 16'h0000;
		tb_branch_update_btb_info = {3'h0, 1'b0, 3'h0, 9'h000, 3'h0};
		tb_branch_update_tgt_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_taken = 1'b0;
		tb_branch_update_btb_hit = 1'b0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_mdpt_update_asid = 16'h0000;
		tb_mdpt_update_mdp = 8'h00;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_asid = 16'h0000;
		expected_itlb_req_exec_mode = corep::EXEC_MODE_M;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_fetch_idx = 9'h000;
	    // itlb resp
		expected_itlb_resp_vpn = {23'h000000, 3'h0};
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_fetch_idx = 9'h000;
	    // icache resp
	    // icache feedback hit
		expected_icache_feedback_hit_valid = 1'b0;
		expected_icache_feedback_hit_way = 1'b0;
	    // icache feedback miss
		expected_icache_feedback_miss_valid = 1'b0;
		expected_icache_feedback_miss_fmid = 4'h0;
		expected_icache_feedback_miss_pa39 = {23'h000000, 3'h0, 9'h000, 3'h0, 1'b0};
	    // icache miss return
	    // instr yield
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
	    // instr yield feedback
	    // wfr trigger from rob
	    // restart from ROB (non-branch restarts)
	    // wfr trigger from decode_unit
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	    // branch update (and also restart if mispred)
		expected_branch_update_ready = 1'b1;
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
            "\n\t\tREQ:         1",
            "\n\t\tRESP:        0",
            "\n\t\tmiss ret:    i", 
            "\n\t\tbuffer:      {}",
            "\n\t\tshift reg 1: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tshift reg 0: _ {i,i,i,i,i,i,i,i}",
            "\n\t\tdeq:         {i,i,i,i}"
        };
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 27'h1e1e1e1;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b10;
		tb_icache_resp_tag_by_way = {27'h1e1e1e1, 27'h0000000};
		tb_icache_resp_fetch16B_by_way = {
            16'he171,
            16'he161,
            16'he151,
            16'he141,
            16'he131,
            16'he121,
            16'he111,
            16'he101,

            16'h0070,
            16'h0060,
            16'h0050,
            16'h0040,
            16'h0030,
            16'h0020,
            16'h0010,
            16'h0000
        };
	    // icache feedback hit
	    // icache feedback miss
		tb_icache_feedback_miss_ready = 1'b1;
	    // icache miss return
		tb_icache_miss_return_valid = 1'b0;
		tb_icache_miss_return_fmid = 4'h0;
		tb_icache_miss_return_fetch16B = {
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000,
            16'h0000
        };
	    // instr yield
	    // instr yield feedback
		tb_instr_yield_ready = 1'b1;
	    // wfr trigger from rob
		tb_rob_trigger_wfr = 1'b0;
	    // restart from ROB (non-branch restarts)
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_bcb_idx = 4'h0;
		tb_rob_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_rob_restart_asid = 16'h0000;
		tb_rob_restart_exec_mode = corep::EXEC_MODE_M;
		tb_rob_restart_virtual_mode = 1'b0;
	    // wfr trigger from decode_unit
		tb_decode_unit_trigger_wfr = 1'b0;
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
		tb_decode_unit_restart_valid = 1'b0;
		tb_decode_unit_restart_bcb_idx = 4'h0;
		tb_decode_unit_restart_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
	    // branch update (and also restart if mispred)
		tb_branch_update_valid = 1'b0;
		tb_branch_update_mispred = 1'b0;
		tb_branch_update_bcb_idx = 4'h0;
		tb_branch_update_src_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_asid = 16'h0000;
		tb_branch_update_btb_info = {3'h0, 1'b0, 3'h0, 9'h000, 3'h0};
		tb_branch_update_tgt_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_branch_update_taken = 1'b0;
		tb_branch_update_btb_hit = 1'b0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_pc38 = {23'h000000, 3'h0, 9'h000, 3'h0};
		tb_mdpt_update_asid = 16'h0000;
		tb_mdpt_update_mdp = 8'h00;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_asid = 16'h0000;
		expected_itlb_req_exec_mode = corep::EXEC_MODE_M;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_fetch_idx = 9'h000;
	    // itlb resp
		expected_itlb_resp_vpn = {23'h000000, 3'h0};
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_fetch_idx = 9'h000;
	    // icache resp
	    // icache feedback hit
		expected_icache_feedback_hit_valid = 1'b0;
		expected_icache_feedback_hit_way = 1'b0;
	    // icache feedback miss
		expected_icache_feedback_miss_valid = 1'b0;
		expected_icache_feedback_miss_fmid = 4'h0;
		expected_icache_feedback_miss_pa39 = {23'h000000, 3'h0, 9'h000, 3'h0, 1'b0};
	    // icache miss return
	    // instr yield
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
	    // instr yield feedback
	    // wfr trigger from rob
	    // restart from ROB (non-branch restarts)
	    // wfr trigger from decode_unit
	    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	    // branch update (and also restart if mispred)
		expected_branch_update_ready = 1'b1;
	    // mdpt update

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