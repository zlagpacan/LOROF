/*
    Filename: fetch_unit_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fetch_unit module. 
    Spec: LOROF/spec/design/fetch_unit.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module fetch_unit_wrapper #(
	parameter FETCH_UNIT_WAIT_FOR_RESTART_STATE = 1'b1,
	parameter INIT_PC = 32'h0,
	parameter INIT_ASID = 9'h0,
	parameter INIT_EXEC_MODE = M_MODE,
	parameter INIT_VIRTUAL_MODE = 1'b0
) (

    // seq
    input logic CLK,
    input logic nRST,


    // itlb req
	output logic last_itlb_req_valid,
	output logic [1:0] last_itlb_req_exec_mode,
	output logic last_itlb_req_virtual_mode,
	output logic [ASID_WIDTH-1:0] last_itlb_req_ASID,
	output logic [VPN_WIDTH-1:0] last_itlb_req_VPN,

    // itlb resp
	input logic next_itlb_resp_valid,
	input logic [PPN_WIDTH-1:0] next_itlb_resp_PPN,
	input logic next_itlb_resp_page_fault,
	input logic next_itlb_resp_access_fault,

    // icache req
	output logic last_icache_req_valid,
	output logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] last_icache_req_block_offset,
	output logic [ICACHE_INDEX_WIDTH-1:0] last_icache_req_index,

    // icache resp
	input logic [1:0] next_icache_resp_valid_by_way,
	input logic [1:0][ICACHE_TAG_WIDTH-1:0] next_icache_resp_tag_by_way,
	input logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0] next_icache_resp_instr_16B_by_way,

    // icache resp feedback
	output logic last_icache_resp_hit_valid,
	output logic last_icache_resp_hit_way,
	output logic last_icache_resp_miss_valid,
	output logic [ICACHE_TAG_WIDTH-1:0] last_icache_resp_miss_tag,

    // output to istream
	output logic last_istream_valid_SENQ,
	output logic [7:0] last_istream_valid_by_fetch_2B_SENQ,
	output logic [7:0] last_istream_one_hot_redirect_by_fetch_2B_SENQ,
	output logic [7:0][15:0] last_istream_instr_2B_by_fetch_2B_SENQ,
	output logic [7:0][BTB_PRED_INFO_WIDTH-1:0] last_istream_pred_info_by_fetch_2B_SENQ,
	output logic [7:0] last_istream_pred_lru_by_fetch_2B_SENQ,
	output logic [7:0][MDPT_INFO_WIDTH-1:0] last_istream_mdp_info_by_fetch_2B_SENQ,
	output logic [31:0] last_istream_after_PC_SENQ,
	output logic [LH_LENGTH-1:0] last_istream_LH_SENQ,
	output logic [GH_LENGTH-1:0] last_istream_GH_SENQ,
	output logic [RAS_INDEX_WIDTH-1:0] last_istream_ras_index_SENQ,
	output logic last_istream_page_fault_SENQ,
	output logic last_istream_access_fault_SENQ,

    // istream feedback
	input logic next_istream_stall_SENQ,

    // fetch + decode restart from ROB
	input logic next_rob_restart_valid,
	input logic [31:0] next_rob_restart_PC,
	input logic [ASID_WIDTH-1:0] next_rob_restart_ASID,
	input logic [1:0] next_rob_restart_exec_mode,
	input logic next_rob_restart_virtual_mode,

    // decode unit control
	input logic next_decode_unit_restart_valid,
	input logic [31:0] next_decode_unit_restart_PC,

	input logic next_decode_unit_trigger_wait_for_restart,

    // branch update from decode unit
	input logic next_decode_unit_branch_update_valid,
	input logic next_decode_unit_branch_update_has_checkpoint,
	input logic next_decode_unit_branch_update_is_mispredict,
	input logic next_decode_unit_branch_update_is_taken,
	input logic next_decode_unit_branch_update_is_complex,
	input logic next_decode_unit_branch_update_use_upct,
	input logic [BTB_PRED_INFO_WIDTH-1:0] next_decode_unit_branch_update_intermediate_pred_info,
	input logic next_decode_unit_branch_update_pred_lru,
	input logic [31:0] next_decode_unit_branch_update_start_PC,
	input logic [31:0] next_decode_unit_branch_update_target_PC,
	input logic [LH_LENGTH-1:0] next_decode_unit_branch_update_LH,
	input logic [GH_LENGTH-1:0] next_decode_unit_branch_update_GH,
	input logic [RAS_INDEX_WIDTH-1:0] next_decode_unit_branch_update_ras_index,

    // mdpt update
	input logic next_mdpt_update_valid,
	input logic [31:0] next_mdpt_update_start_full_PC,
	input logic [ASID_WIDTH-1:0] next_mdpt_update_ASID,
	input logic [MDPT_INFO_WIDTH-1:0] next_mdpt_update_mdp_info
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // itlb req
	logic itlb_req_valid;
	logic [1:0] itlb_req_exec_mode;
	logic itlb_req_virtual_mode;
	logic [ASID_WIDTH-1:0] itlb_req_ASID;
	logic [VPN_WIDTH-1:0] itlb_req_VPN;

    // itlb resp
	logic itlb_resp_valid;
	logic [PPN_WIDTH-1:0] itlb_resp_PPN;
	logic itlb_resp_page_fault;
	logic itlb_resp_access_fault;

    // icache req
	logic icache_req_valid;
	logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] icache_req_block_offset;
	logic [ICACHE_INDEX_WIDTH-1:0] icache_req_index;

    // icache resp
	logic [1:0] icache_resp_valid_by_way;
	logic [1:0][ICACHE_TAG_WIDTH-1:0] icache_resp_tag_by_way;
	logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0] icache_resp_instr_16B_by_way;

    // icache resp feedback
	logic icache_resp_hit_valid;
	logic icache_resp_hit_way;
	logic icache_resp_miss_valid;
	logic [ICACHE_TAG_WIDTH-1:0] icache_resp_miss_tag;

    // output to istream
	logic istream_valid_SENQ;
	logic [7:0] istream_valid_by_fetch_2B_SENQ;
	logic [7:0] istream_one_hot_redirect_by_fetch_2B_SENQ;
	logic [7:0][15:0] istream_instr_2B_by_fetch_2B_SENQ;
	logic [7:0][BTB_PRED_INFO_WIDTH-1:0] istream_pred_info_by_fetch_2B_SENQ;
	logic [7:0] istream_pred_lru_by_fetch_2B_SENQ;
	logic [7:0][MDPT_INFO_WIDTH-1:0] istream_mdp_info_by_fetch_2B_SENQ;
	logic [31:0] istream_after_PC_SENQ;
	logic [LH_LENGTH-1:0] istream_LH_SENQ;
	logic [GH_LENGTH-1:0] istream_GH_SENQ;
	logic [RAS_INDEX_WIDTH-1:0] istream_ras_index_SENQ;
	logic istream_page_fault_SENQ;
	logic istream_access_fault_SENQ;

    // istream feedback
	logic istream_stall_SENQ;

    // fetch + decode restart from ROB
	logic rob_restart_valid;
	logic [31:0] rob_restart_PC;
	logic [ASID_WIDTH-1:0] rob_restart_ASID;
	logic [1:0] rob_restart_exec_mode;
	logic rob_restart_virtual_mode;

    // decode unit control
	logic decode_unit_restart_valid;
	logic [31:0] decode_unit_restart_PC;

	logic decode_unit_trigger_wait_for_restart;

    // branch update from decode unit
	logic decode_unit_branch_update_valid;
	logic decode_unit_branch_update_has_checkpoint;
	logic decode_unit_branch_update_is_mispredict;
	logic decode_unit_branch_update_is_taken;
	logic decode_unit_branch_update_is_complex;
	logic decode_unit_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] decode_unit_branch_update_intermediate_pred_info;
	logic decode_unit_branch_update_pred_lru;
	logic [31:0] decode_unit_branch_update_start_PC;
	logic [31:0] decode_unit_branch_update_target_PC;
	logic [LH_LENGTH-1:0] decode_unit_branch_update_LH;
	logic [GH_LENGTH-1:0] decode_unit_branch_update_GH;
	logic [RAS_INDEX_WIDTH-1:0] decode_unit_branch_update_ras_index;

    // mdpt update
	logic mdpt_update_valid;
	logic [31:0] mdpt_update_start_full_PC;
	logic [ASID_WIDTH-1:0] mdpt_update_ASID;
	logic [MDPT_INFO_WIDTH-1:0] mdpt_update_mdp_info;

    // ----------------------------------------------------------------
    // Module Instantiation:

	fetch_unit #(
		.FETCH_UNIT_WAIT_FOR_RESTART_STATE(FETCH_UNIT_WAIT_FOR_RESTART_STATE),
		.INIT_PC(INIT_PC),
		.INIT_ASID(INIT_ASID),
		.INIT_EXEC_MODE(INIT_EXEC_MODE),
		.INIT_VIRTUAL_MODE(INIT_VIRTUAL_MODE)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // itlb req
			last_itlb_req_valid <= '0;
			last_itlb_req_exec_mode <= '0;
			last_itlb_req_virtual_mode <= '0;
			last_itlb_req_ASID <= '0;
			last_itlb_req_VPN <= '0;

		    // itlb resp
			itlb_resp_valid <= '0;
			itlb_resp_PPN <= '0;
			itlb_resp_page_fault <= '0;
			itlb_resp_access_fault <= '0;

		    // icache req
			last_icache_req_valid <= '0;
			last_icache_req_block_offset <= '0;
			last_icache_req_index <= '0;

		    // icache resp
			icache_resp_valid_by_way <= '0;
			icache_resp_tag_by_way <= '0;
			icache_resp_instr_16B_by_way <= '0;

		    // icache resp feedback
			last_icache_resp_hit_valid <= '0;
			last_icache_resp_hit_way <= '0;
			last_icache_resp_miss_valid <= '0;
			last_icache_resp_miss_tag <= '0;

		    // output to istream
			last_istream_valid_SENQ <= '0;
			last_istream_valid_by_fetch_2B_SENQ <= '0;
			last_istream_one_hot_redirect_by_fetch_2B_SENQ <= '0;
			last_istream_instr_2B_by_fetch_2B_SENQ <= '0;
			last_istream_pred_info_by_fetch_2B_SENQ <= '0;
			last_istream_pred_lru_by_fetch_2B_SENQ <= '0;
			last_istream_mdp_info_by_fetch_2B_SENQ <= '0;
			last_istream_after_PC_SENQ <= '0;
			last_istream_LH_SENQ <= '0;
			last_istream_GH_SENQ <= '0;
			last_istream_ras_index_SENQ <= '0;
			last_istream_page_fault_SENQ <= '0;
			last_istream_access_fault_SENQ <= '0;

		    // istream feedback
			istream_stall_SENQ <= '0;

		    // fetch + decode restart from ROB
			rob_restart_valid <= '0;
			rob_restart_PC <= '0;
			rob_restart_ASID <= '0;
			rob_restart_exec_mode <= '0;
			rob_restart_virtual_mode <= '0;

		    // decode unit control
			decode_unit_restart_valid <= '0;
			decode_unit_restart_PC <= '0;

			decode_unit_trigger_wait_for_restart <= '0;

		    // branch update from decode unit
			decode_unit_branch_update_valid <= '0;
			decode_unit_branch_update_has_checkpoint <= '0;
			decode_unit_branch_update_is_mispredict <= '0;
			decode_unit_branch_update_is_taken <= '0;
			decode_unit_branch_update_is_complex <= '0;
			decode_unit_branch_update_use_upct <= '0;
			decode_unit_branch_update_intermediate_pred_info <= '0;
			decode_unit_branch_update_pred_lru <= '0;
			decode_unit_branch_update_start_PC <= '0;
			decode_unit_branch_update_target_PC <= '0;
			decode_unit_branch_update_LH <= '0;
			decode_unit_branch_update_GH <= '0;
			decode_unit_branch_update_ras_index <= '0;

		    // mdpt update
			mdpt_update_valid <= '0;
			mdpt_update_start_full_PC <= '0;
			mdpt_update_ASID <= '0;
			mdpt_update_mdp_info <= '0;
        end
        else begin


		    // itlb req
			last_itlb_req_valid <= itlb_req_valid;
			last_itlb_req_exec_mode <= itlb_req_exec_mode;
			last_itlb_req_virtual_mode <= itlb_req_virtual_mode;
			last_itlb_req_ASID <= itlb_req_ASID;
			last_itlb_req_VPN <= itlb_req_VPN;

		    // itlb resp
			itlb_resp_valid <= next_itlb_resp_valid;
			itlb_resp_PPN <= next_itlb_resp_PPN;
			itlb_resp_page_fault <= next_itlb_resp_page_fault;
			itlb_resp_access_fault <= next_itlb_resp_access_fault;

		    // icache req
			last_icache_req_valid <= icache_req_valid;
			last_icache_req_block_offset <= icache_req_block_offset;
			last_icache_req_index <= icache_req_index;

		    // icache resp
			icache_resp_valid_by_way <= next_icache_resp_valid_by_way;
			icache_resp_tag_by_way <= next_icache_resp_tag_by_way;
			icache_resp_instr_16B_by_way <= next_icache_resp_instr_16B_by_way;

		    // icache resp feedback
			last_icache_resp_hit_valid <= icache_resp_hit_valid;
			last_icache_resp_hit_way <= icache_resp_hit_way;
			last_icache_resp_miss_valid <= icache_resp_miss_valid;
			last_icache_resp_miss_tag <= icache_resp_miss_tag;

		    // output to istream
			last_istream_valid_SENQ <= istream_valid_SENQ;
			last_istream_valid_by_fetch_2B_SENQ <= istream_valid_by_fetch_2B_SENQ;
			last_istream_one_hot_redirect_by_fetch_2B_SENQ <= istream_one_hot_redirect_by_fetch_2B_SENQ;
			last_istream_instr_2B_by_fetch_2B_SENQ <= istream_instr_2B_by_fetch_2B_SENQ;
			last_istream_pred_info_by_fetch_2B_SENQ <= istream_pred_info_by_fetch_2B_SENQ;
			last_istream_pred_lru_by_fetch_2B_SENQ <= istream_pred_lru_by_fetch_2B_SENQ;
			last_istream_mdp_info_by_fetch_2B_SENQ <= istream_mdp_info_by_fetch_2B_SENQ;
			last_istream_after_PC_SENQ <= istream_after_PC_SENQ;
			last_istream_LH_SENQ <= istream_LH_SENQ;
			last_istream_GH_SENQ <= istream_GH_SENQ;
			last_istream_ras_index_SENQ <= istream_ras_index_SENQ;
			last_istream_page_fault_SENQ <= istream_page_fault_SENQ;
			last_istream_access_fault_SENQ <= istream_access_fault_SENQ;

		    // istream feedback
			istream_stall_SENQ <= next_istream_stall_SENQ;

		    // fetch + decode restart from ROB
			rob_restart_valid <= next_rob_restart_valid;
			rob_restart_PC <= next_rob_restart_PC;
			rob_restart_ASID <= next_rob_restart_ASID;
			rob_restart_exec_mode <= next_rob_restart_exec_mode;
			rob_restart_virtual_mode <= next_rob_restart_virtual_mode;

		    // decode unit control
			decode_unit_restart_valid <= next_decode_unit_restart_valid;
			decode_unit_restart_PC <= next_decode_unit_restart_PC;

			decode_unit_trigger_wait_for_restart <= next_decode_unit_trigger_wait_for_restart;

		    // branch update from decode unit
			decode_unit_branch_update_valid <= next_decode_unit_branch_update_valid;
			decode_unit_branch_update_has_checkpoint <= next_decode_unit_branch_update_has_checkpoint;
			decode_unit_branch_update_is_mispredict <= next_decode_unit_branch_update_is_mispredict;
			decode_unit_branch_update_is_taken <= next_decode_unit_branch_update_is_taken;
			decode_unit_branch_update_is_complex <= next_decode_unit_branch_update_is_complex;
			decode_unit_branch_update_use_upct <= next_decode_unit_branch_update_use_upct;
			decode_unit_branch_update_intermediate_pred_info <= next_decode_unit_branch_update_intermediate_pred_info;
			decode_unit_branch_update_pred_lru <= next_decode_unit_branch_update_pred_lru;
			decode_unit_branch_update_start_PC <= next_decode_unit_branch_update_start_PC;
			decode_unit_branch_update_target_PC <= next_decode_unit_branch_update_target_PC;
			decode_unit_branch_update_LH <= next_decode_unit_branch_update_LH;
			decode_unit_branch_update_GH <= next_decode_unit_branch_update_GH;
			decode_unit_branch_update_ras_index <= next_decode_unit_branch_update_ras_index;

		    // mdpt update
			mdpt_update_valid <= next_mdpt_update_valid;
			mdpt_update_start_full_PC <= next_mdpt_update_start_full_PC;
			mdpt_update_ASID <= next_mdpt_update_ASID;
			mdpt_update_mdp_info <= next_mdpt_update_mdp_info;
        end
    end

endmodule