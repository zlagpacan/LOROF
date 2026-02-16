/*
    Filename: fetch_unit_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fetch_unit module. 
    Spec: LOROF/spec/design/fetch_unit.md
*/

`timescale 1ns/100ps

`include "corep.vh"
`include "sysp.vh"

module fetch_unit_wrapper #(
) (

    // seq
    input logic CLK,
    input logic nRST,


    // itlb req
	output logic last_itlb_req_valid,
	output corep::asid_t last_itlb_req_asid,
	output corep::exec_mode_t last_itlb_req_exec_mode,
	output logic last_itlb_req_virtual_mode,
	output corep::fetch_idx_t last_itlb_req_fetch_idx,

    // itlb resp
	output sysp::vpn_t last_itlb_resp_vpn,

	input logic next_itlb_resp_valid,
	input sysp::ppn_t next_itlb_resp_ppn,
	input logic next_itlb_resp_page_fault,
	input logic next_itlb_resp_access_fault,

    // icache req
	output logic last_icache_req_valid,
	output corep::fetch_idx_t last_icache_req_fetch_idx,

    // icache resp
	input logic [sysp::ICACHE_ASSOC-1:0] next_icache_resp_valid_by_way,
	input sysp::icache_tag_t [sysp::ICACHE_ASSOC-1:0] next_icache_resp_tag_by_way,
	input corep::fetch16B_t [sysp::ICACHE_ASSOC-1:0] next_icache_resp_fetch16B_by_way,

    // icache feedback hit
	output logic last_icache_feedback_hit_valid,
	output sysp::icache_way_t last_icache_feedback_hit_way,

    // icache feedback miss
	output logic last_icache_feedback_miss_valid,
	output corep::fmid_t last_icache_feedback_miss_fmid,
	output sysp::pa39_t last_icache_feedback_miss_pa39,

	input logic next_icache_feedback_miss_ready,

    // icache miss return
	input logic next_icache_miss_return_valid,
	input corep::fmid_t next_icache_miss_return_fmid,
	input corep::fetch16B_t next_icache_miss_return_fetch16B,

    // instr yield
	output logic last_instr_yield_valid,
	output corep::instr_yield_t [3:0] last_instr_yield_by_way,

    // instr yield feedback
	input logic next_instr_yield_ready,

    // wfr trigger from rob
	input logic next_rob_trigger_wfr,

    // restart from ROB (non-branch restarts)
	input logic next_rob_restart_valid,
	input corep::bcb_idx_t next_rob_restart_bcb_idx,
	input corep::pc38_t next_rob_restart_pc38,
	input corep::asid_t next_rob_restart_asid,
	input corep::exec_mode_t next_rob_restart_exec_mode,
	input logic next_rob_restart_virtual_mode,

    // wfr trigger from decode_unit
	input logic next_decode_unit_trigger_wfr,

    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	input logic next_decode_unit_restart_valid,
	input corep::bcb_idx_t next_decode_unit_restart_bcb_idx,
	input corep::pc38_t next_decode_unit_restart_pc38,

    // branch update (and also restart if mispred)
	input logic next_branch_update_valid,
	input logic next_branch_update_mispred,
	input corep::bcb_idx_t next_branch_update_bcb_idx,
	input corep::pc38_t next_branch_update_src_pc38,
	input corep::asid_t next_branch_update_asid,
	input corep::btb_info_t next_branch_update_btb_info,
	input corep::pc38_t next_branch_update_tgt_pc38,
	input logic next_branch_update_taken,
	input logic next_branch_update_btb_hit,

	output logic last_branch_update_ready,

    // mdpt update
	input logic next_mdpt_update_valid,
	input corep::pc38_t next_mdpt_update_pc38,
	input corep::asid_t next_mdpt_update_asid,
	input corep::mdp_t next_mdpt_update_mdp
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // itlb req
	logic itlb_req_valid;
	corep::asid_t itlb_req_asid;
	corep::exec_mode_t itlb_req_exec_mode;
	logic itlb_req_virtual_mode;
	corep::fetch_idx_t itlb_req_fetch_idx;

    // itlb resp
	sysp::vpn_t itlb_resp_vpn;

	logic itlb_resp_valid;
	sysp::ppn_t itlb_resp_ppn;
	logic itlb_resp_page_fault;
	logic itlb_resp_access_fault;

    // icache req
	logic icache_req_valid;
	corep::fetch_idx_t icache_req_fetch_idx;

    // icache resp
	logic [sysp::ICACHE_ASSOC-1:0] icache_resp_valid_by_way;
	sysp::icache_tag_t [sysp::ICACHE_ASSOC-1:0] icache_resp_tag_by_way;
	corep::fetch16B_t [sysp::ICACHE_ASSOC-1:0] icache_resp_fetch16B_by_way;

    // icache feedback hit
	logic icache_feedback_hit_valid;
	sysp::icache_way_t icache_feedback_hit_way;

    // icache feedback miss
	logic icache_feedback_miss_valid;
	corep::fmid_t icache_feedback_miss_fmid;
	sysp::pa39_t icache_feedback_miss_pa39;

	logic icache_feedback_miss_ready;

    // icache miss return
	logic icache_miss_return_valid;
	corep::fmid_t icache_miss_return_fmid;
	corep::fetch16B_t icache_miss_return_fetch16B;

    // instr yield
	logic instr_yield_valid;
	corep::instr_yield_t [3:0] instr_yield_by_way;

    // instr yield feedback
	logic instr_yield_ready;

    // wfr trigger from rob
	logic rob_trigger_wfr;

    // restart from ROB (non-branch restarts)
	logic rob_restart_valid;
	corep::bcb_idx_t rob_restart_bcb_idx;
	corep::pc38_t rob_restart_pc38;
	corep::asid_t rob_restart_asid;
	corep::exec_mode_t rob_restart_exec_mode;
	logic rob_restart_virtual_mode;

    // wfr trigger from decode_unit
	logic decode_unit_trigger_wfr;

    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
	logic decode_unit_restart_valid;
	corep::bcb_idx_t decode_unit_restart_bcb_idx;
	corep::pc38_t decode_unit_restart_pc38;

    // branch update (and also restart if mispred)
	logic branch_update_valid;
	logic branch_update_mispred;
	corep::bcb_idx_t branch_update_bcb_idx;
	corep::pc38_t branch_update_src_pc38;
	corep::asid_t branch_update_asid;
	corep::btb_info_t branch_update_btb_info;
	corep::pc38_t branch_update_tgt_pc38;
	logic branch_update_taken;
	logic branch_update_btb_hit;

	logic branch_update_ready;

    // mdpt update
	logic mdpt_update_valid;
	corep::pc38_t mdpt_update_pc38;
	corep::asid_t mdpt_update_asid;
	corep::mdp_t mdpt_update_mdp;

    // ----------------------------------------------------------------
    // Module Instantiation:

	fetch_unit #(
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // itlb req
			last_itlb_req_valid <= '0;
			last_itlb_req_asid <= '0;
			last_itlb_req_exec_mode <= '0;
			last_itlb_req_virtual_mode <= '0;
			last_itlb_req_fetch_idx <= '0;

		    // itlb resp
			last_itlb_resp_vpn <= '0;

			itlb_resp_valid <= '0;
			itlb_resp_ppn <= '0;
			itlb_resp_page_fault <= '0;
			itlb_resp_access_fault <= '0;

		    // icache req
			last_icache_req_valid <= '0;
			last_icache_req_fetch_idx <= '0;

		    // icache resp
			icache_resp_valid_by_way <= '0;
			icache_resp_tag_by_way <= '0;
			icache_resp_fetch16B_by_way <= '0;

		    // icache feedback hit
			last_icache_feedback_hit_valid <= '0;
			last_icache_feedback_hit_way <= '0;

		    // icache feedback miss
			last_icache_feedback_miss_valid <= '0;
			last_icache_feedback_miss_fmid <= '0;
			last_icache_feedback_miss_pa39 <= '0;

			icache_feedback_miss_ready <= '0;

		    // icache miss return
			icache_miss_return_valid <= '0;
			icache_miss_return_fmid <= '0;
			icache_miss_return_fetch16B <= '0;

		    // instr yield
			last_instr_yield_valid <= '0;
			last_instr_yield_by_way <= '0;

		    // instr yield feedback
			instr_yield_ready <= '0;

		    // wfr trigger from rob
			rob_trigger_wfr <= '0;

		    // restart from ROB (non-branch restarts)
			rob_restart_valid <= '0;
			rob_restart_bcb_idx <= '0;
			rob_restart_pc38 <= '0;
			rob_restart_asid <= '0;
			rob_restart_exec_mode <= '0;
			rob_restart_virtual_mode <= '0;

		    // wfr trigger from decode_unit
			decode_unit_trigger_wfr <= '0;

		    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
			decode_unit_restart_valid <= '0;
			decode_unit_restart_bcb_idx <= '0;
			decode_unit_restart_pc38 <= '0;

		    // branch update (and also restart if mispred)
			branch_update_valid <= '0;
			branch_update_mispred <= '0;
			branch_update_bcb_idx <= '0;
			branch_update_src_pc38 <= '0;
			branch_update_asid <= '0;
			branch_update_btb_info <= '0;
			branch_update_tgt_pc38 <= '0;
			branch_update_taken <= '0;
			branch_update_btb_hit <= '0;

			last_branch_update_ready <= '0;

		    // mdpt update
			mdpt_update_valid <= '0;
			mdpt_update_pc38 <= '0;
			mdpt_update_asid <= '0;
			mdpt_update_mdp <= '0;
        end
        else begin


		    // itlb req
			last_itlb_req_valid <= itlb_req_valid;
			last_itlb_req_asid <= itlb_req_asid;
			last_itlb_req_exec_mode <= itlb_req_exec_mode;
			last_itlb_req_virtual_mode <= itlb_req_virtual_mode;
			last_itlb_req_fetch_idx <= itlb_req_fetch_idx;

		    // itlb resp
			last_itlb_resp_vpn <= itlb_resp_vpn;

			itlb_resp_valid <= next_itlb_resp_valid;
			itlb_resp_ppn <= next_itlb_resp_ppn;
			itlb_resp_page_fault <= next_itlb_resp_page_fault;
			itlb_resp_access_fault <= next_itlb_resp_access_fault;

		    // icache req
			last_icache_req_valid <= icache_req_valid;
			last_icache_req_fetch_idx <= icache_req_fetch_idx;

		    // icache resp
			icache_resp_valid_by_way <= next_icache_resp_valid_by_way;
			icache_resp_tag_by_way <= next_icache_resp_tag_by_way;
			icache_resp_fetch16B_by_way <= next_icache_resp_fetch16B_by_way;

		    // icache feedback hit
			last_icache_feedback_hit_valid <= icache_feedback_hit_valid;
			last_icache_feedback_hit_way <= icache_feedback_hit_way;

		    // icache feedback miss
			last_icache_feedback_miss_valid <= icache_feedback_miss_valid;
			last_icache_feedback_miss_fmid <= icache_feedback_miss_fmid;
			last_icache_feedback_miss_pa39 <= icache_feedback_miss_pa39;

			icache_feedback_miss_ready <= next_icache_feedback_miss_ready;

		    // icache miss return
			icache_miss_return_valid <= next_icache_miss_return_valid;
			icache_miss_return_fmid <= next_icache_miss_return_fmid;
			icache_miss_return_fetch16B <= next_icache_miss_return_fetch16B;

		    // instr yield
			last_instr_yield_valid <= instr_yield_valid;
			last_instr_yield_by_way <= instr_yield_by_way;

		    // instr yield feedback
			instr_yield_ready <= next_instr_yield_ready;

		    // wfr trigger from rob
			rob_trigger_wfr <= next_rob_trigger_wfr;

		    // restart from ROB (non-branch restarts)
			rob_restart_valid <= next_rob_restart_valid;
			rob_restart_bcb_idx <= next_rob_restart_bcb_idx;
			rob_restart_pc38 <= next_rob_restart_pc38;
			rob_restart_asid <= next_rob_restart_asid;
			rob_restart_exec_mode <= next_rob_restart_exec_mode;
			rob_restart_virtual_mode <= next_rob_restart_virtual_mode;

		    // wfr trigger from decode_unit
			decode_unit_trigger_wfr <= next_decode_unit_trigger_wfr;

		    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
			decode_unit_restart_valid <= next_decode_unit_restart_valid;
			decode_unit_restart_bcb_idx <= next_decode_unit_restart_bcb_idx;
			decode_unit_restart_pc38 <= next_decode_unit_restart_pc38;

		    // branch update (and also restart if mispred)
			branch_update_valid <= next_branch_update_valid;
			branch_update_mispred <= next_branch_update_mispred;
			branch_update_bcb_idx <= next_branch_update_bcb_idx;
			branch_update_src_pc38 <= next_branch_update_src_pc38;
			branch_update_asid <= next_branch_update_asid;
			branch_update_btb_info <= next_branch_update_btb_info;
			branch_update_tgt_pc38 <= next_branch_update_tgt_pc38;
			branch_update_taken <= next_branch_update_taken;
			branch_update_btb_hit <= next_branch_update_btb_hit;

			last_branch_update_ready <= branch_update_ready;

		    // mdpt update
			mdpt_update_valid <= next_mdpt_update_valid;
			mdpt_update_pc38 <= next_mdpt_update_pc38;
			mdpt_update_asid <= next_mdpt_update_asid;
			mdpt_update_mdp <= next_mdpt_update_mdp;
        end
    end

endmodule