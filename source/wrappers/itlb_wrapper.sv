/*
    Filename: itlb_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around itlb module. 
    Spec: LOROF/spec/design/itlb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;
`include "system_types_pkg.vh"
import system_types_pkg::*;

module itlb_wrapper #(
	parameter ASID_WIDTH = 9,
	parameter VPN_WIDTH = 20,
	parameter PPN_WIDTH = 22,
	parameter ITLB_4KBPAGE_ENTRIES = 16, // 16-entry,
	parameter ITLB_4KBPAGE_ASSOC = 4, // 4x,
	parameter LOG_ITLB_4KBPAGE_ASSOC = $clog2(ITLB_4KBPAGE_ASSOC), // 2b,
	parameter ITLB_4KBPAGE_NUM_SETS = ITLB_4KBPAGE_ENTRIES / ITLB_4KBPAGE_ASSOC, // 4x,
	parameter ITLB_4KBPAGE_INDEX_WIDTH = $clog2(ITLB_4KBPAGE_NUM_SETS), // 2b,
	parameter ITLB_4KBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4KBPAGE_INDEX_WIDTH - PO_WIDTH, // 18b,
	parameter ITLB_4MBPAGE_ENTRIES = 4, // 4-entry,
	parameter ITLB_4MBPAGE_ASSOC = 2, // 2x,
	parameter LOG_ITLB_4MBPAGE_ASSOC = $clog2(ITLB_4MBPAGE_ASSOC), // 1b,
	parameter ITLB_4MBPAGE_NUM_SETS = ITLB_4MBPAGE_ENTRIES / ITLB_4MBPAGE_ASSOC, // 2x,
	parameter ITLB_4MBPAGE_INDEX_WIDTH = $clog2(ITLB_4MBPAGE_NUM_SETS), // 1b,
	parameter ITLB_4MBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4MBPAGE_INDEX_WIDTH - VPN0_WIDTH - PO_WIDTH, // 9b,
	parameter ITLB_L2_TLB_REQ_TAG_COUNT = 4,
	parameter ITLB_L2_TLB_REQ_TAG_WIDTH = $clog2(ITLB_L2_TLB_REQ_TAG_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // core req
	input logic next_core_req_valid,
	input logic [1:0] next_core_req_exec_mode,
	input logic next_core_req_virtual_mode,
	input logic [ASID_WIDTH-1:0] next_core_req_ASID,
	input logic [VPN_WIDTH-1:0] next_core_req_VPN,

    // core resp
	output logic last_core_resp_valid,
	output logic [PPN_WIDTH-1:0] last_core_resp_PPN,
	output logic last_core_resp_page_fault,
	output logic last_core_resp_access_fault,

    // req to L2 TLB
	output logic last_l2_tlb_req_valid,
	output logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0] last_l2_tlb_req_tag,
	output logic [ASID_WIDTH-1:0] last_l2_tlb_req_ASID,
	output logic [VPN_WIDTH-1:0] last_l2_tlb_req_VPN,

	input logic next_l2_tlb_req_ready,

    // resp from L2 TLB
	input logic next_l2_tlb_resp_valid,
	input logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0] next_l2_tlb_resp_tag,
	input pte_t next_l2_tlb_resp_pte,
	input logic next_l2_tlb_resp_is_superpage,
	input logic next_l2_tlb_resp_access_fault_pt_access,

    // evict to L2 TLB
	output logic last_l2_tlb_evict_valid,
	output logic [ASID_WIDTH-1:0] last_l2_tlb_evict_ASID,
	output logic [VPN_WIDTH-1:0] last_l2_tlb_evict_VPN,
	output pte_t last_l2_tlb_evict_pte,
	output logic last_l2_tlb_evict_is_superpage,

    // sfence invalidation
	input logic next_sfence_inv_valid,
	input logic [ASID_WIDTH-1:0] next_sfence_inv_ASID,
	input logic [VPN_WIDTH-1:0] next_sfence_inv_VPN,

    // sfence invalidation backpressure
	output logic last_sfence_inv_ready
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // core req
	logic core_req_valid;
	logic [1:0] core_req_exec_mode;
	logic core_req_virtual_mode;
	logic [ASID_WIDTH-1:0] core_req_ASID;
	logic [VPN_WIDTH-1:0] core_req_VPN;

    // core resp
	logic core_resp_valid;
	logic [PPN_WIDTH-1:0] core_resp_PPN;
	logic core_resp_page_fault;
	logic core_resp_access_fault;

    // req to L2 TLB
	logic l2_tlb_req_valid;
	logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0] l2_tlb_req_tag;
	logic [ASID_WIDTH-1:0] l2_tlb_req_ASID;
	logic [VPN_WIDTH-1:0] l2_tlb_req_VPN;

	logic l2_tlb_req_ready;

    // resp from L2 TLB
	logic l2_tlb_resp_valid;
	logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0] l2_tlb_resp_tag;
	pte_t l2_tlb_resp_pte;
	logic l2_tlb_resp_is_superpage;
	logic l2_tlb_resp_access_fault_pt_access;

    // evict to L2 TLB
	logic l2_tlb_evict_valid;
	logic [ASID_WIDTH-1:0] l2_tlb_evict_ASID;
	logic [VPN_WIDTH-1:0] l2_tlb_evict_VPN;
	pte_t l2_tlb_evict_pte;
	logic l2_tlb_evict_is_superpage;

    // sfence invalidation
	logic sfence_inv_valid;
	logic [ASID_WIDTH-1:0] sfence_inv_ASID;
	logic [VPN_WIDTH-1:0] sfence_inv_VPN;

    // sfence invalidation backpressure
	logic sfence_inv_ready;

    // ----------------------------------------------------------------
    // Module Instantiation:

	itlb #(
		.ASID_WIDTH(ASID_WIDTH),
		.VPN_WIDTH(VPN_WIDTH),
		.PPN_WIDTH(PPN_WIDTH),
		.ITLB_4KBPAGE_ENTRIES(ITLB_4KBPAGE_ENTRIES),
		.ITLB_4KBPAGE_ASSOC(ITLB_4KBPAGE_ASSOC),
		.LOG_ITLB_4KBPAGE_ASSOC(LOG_ITLB_4KBPAGE_ASSOC),
		.ITLB_4KBPAGE_NUM_SETS(ITLB_4KBPAGE_NUM_SETS),
		.ITLB_4KBPAGE_INDEX_WIDTH(ITLB_4KBPAGE_INDEX_WIDTH),
		.ITLB_4KBPAGE_TAG_WIDTH(ITLB_4KBPAGE_TAG_WIDTH),
		.ITLB_4MBPAGE_ENTRIES(ITLB_4MBPAGE_ENTRIES),
		.ITLB_4MBPAGE_ASSOC(ITLB_4MBPAGE_ASSOC),
		.LOG_ITLB_4MBPAGE_ASSOC(LOG_ITLB_4MBPAGE_ASSOC),
		.ITLB_4MBPAGE_NUM_SETS(ITLB_4MBPAGE_NUM_SETS),
		.ITLB_4MBPAGE_INDEX_WIDTH(ITLB_4MBPAGE_INDEX_WIDTH),
		.ITLB_4MBPAGE_TAG_WIDTH(ITLB_4MBPAGE_TAG_WIDTH),
		.ITLB_L2_TLB_REQ_TAG_COUNT(ITLB_L2_TLB_REQ_TAG_COUNT),
		.ITLB_L2_TLB_REQ_TAG_WIDTH(ITLB_L2_TLB_REQ_TAG_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // core req
			core_req_valid <= '0;
			core_req_exec_mode <= '0;
			core_req_virtual_mode <= '0;
			core_req_ASID <= '0;
			core_req_VPN <= '0;

		    // core resp
			last_core_resp_valid <= '0;
			last_core_resp_PPN <= '0;
			last_core_resp_page_fault <= '0;
			last_core_resp_access_fault <= '0;

		    // req to L2 TLB
			last_l2_tlb_req_valid <= '0;
			last_l2_tlb_req_tag <= '0;
			last_l2_tlb_req_ASID <= '0;
			last_l2_tlb_req_VPN <= '0;

			l2_tlb_req_ready <= '0;

		    // resp from L2 TLB
			l2_tlb_resp_valid <= '0;
			l2_tlb_resp_tag <= '0;
			l2_tlb_resp_pte <= '0;
			l2_tlb_resp_is_superpage <= '0;
			l2_tlb_resp_access_fault_pt_access <= '0;

		    // evict to L2 TLB
			last_l2_tlb_evict_valid <= '0;
			last_l2_tlb_evict_ASID <= '0;
			last_l2_tlb_evict_VPN <= '0;
			last_l2_tlb_evict_pte <= '0;
			last_l2_tlb_evict_is_superpage <= '0;

		    // sfence invalidation
			sfence_inv_valid <= '0;
			sfence_inv_ASID <= '0;
			sfence_inv_VPN <= '0;

		    // sfence invalidation backpressure
			last_sfence_inv_ready <= '0;
        end
        else begin

		    // core req
			core_req_valid <= next_core_req_valid;
			core_req_exec_mode <= next_core_req_exec_mode;
			core_req_virtual_mode <= next_core_req_virtual_mode;
			core_req_ASID <= next_core_req_ASID;
			core_req_VPN <= next_core_req_VPN;

		    // core resp
			last_core_resp_valid <= core_resp_valid;
			last_core_resp_PPN <= core_resp_PPN;
			last_core_resp_page_fault <= core_resp_page_fault;
			last_core_resp_access_fault <= core_resp_access_fault;

		    // req to L2 TLB
			last_l2_tlb_req_valid <= l2_tlb_req_valid;
			last_l2_tlb_req_tag <= l2_tlb_req_tag;
			last_l2_tlb_req_ASID <= l2_tlb_req_ASID;
			last_l2_tlb_req_VPN <= l2_tlb_req_VPN;

			l2_tlb_req_ready <= next_l2_tlb_req_ready;

		    // resp from L2 TLB
			l2_tlb_resp_valid <= next_l2_tlb_resp_valid;
			l2_tlb_resp_tag <= next_l2_tlb_resp_tag;
			l2_tlb_resp_pte <= next_l2_tlb_resp_pte;
			l2_tlb_resp_is_superpage <= next_l2_tlb_resp_is_superpage;
			l2_tlb_resp_access_fault_pt_access <= next_l2_tlb_resp_access_fault_pt_access;

		    // evict to L2 TLB
			last_l2_tlb_evict_valid <= l2_tlb_evict_valid;
			last_l2_tlb_evict_ASID <= l2_tlb_evict_ASID;
			last_l2_tlb_evict_VPN <= l2_tlb_evict_VPN;
			last_l2_tlb_evict_pte <= l2_tlb_evict_pte;
			last_l2_tlb_evict_is_superpage <= l2_tlb_evict_is_superpage;

		    // sfence invalidation
			sfence_inv_valid <= next_sfence_inv_valid;
			sfence_inv_ASID <= next_sfence_inv_ASID;
			sfence_inv_VPN <= next_sfence_inv_VPN;

		    // sfence invalidation backpressure
			last_sfence_inv_ready <= sfence_inv_ready;
        end
    end

endmodule