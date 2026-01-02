/*
    Filename: itlb_tb.sv
    Author: zlagpacan
    Description: Testbench for itlb module. 
    Spec: LOROF/spec/design/itlb.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;
`include "system_types_pkg.vh"
import system_types_pkg::*;

module itlb_tb #(
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
) ();

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

    // core req
	logic tb_core_req_valid;
	logic [1:0] tb_core_req_exec_mode;
	logic tb_core_req_virtual_mode;
	logic [ASID_WIDTH-1:0] tb_core_req_ASID;
	logic [VPN_WIDTH-1:0] tb_core_req_VPN;

    // core resp
	logic DUT_core_resp_valid, expected_core_resp_valid;
	logic [PPN_WIDTH-1:0] DUT_core_resp_PPN, expected_core_resp_PPN;
	logic DUT_core_resp_page_fault, expected_core_resp_page_fault;
	logic DUT_core_resp_access_fault, expected_core_resp_access_fault;

    // req to L2 TLB
	logic DUT_l2_tlb_req_valid, expected_l2_tlb_req_valid;
	logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0] DUT_l2_tlb_req_tag, expected_l2_tlb_req_tag;
	logic [ASID_WIDTH-1:0] DUT_l2_tlb_req_ASID, expected_l2_tlb_req_ASID;
	logic [VPN_WIDTH-1:0] DUT_l2_tlb_req_VPN, expected_l2_tlb_req_VPN;

	logic tb_l2_tlb_req_ready;

    // resp from L2 TLB
	logic tb_l2_tlb_resp_valid;
	logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0] tb_l2_tlb_resp_tag;
	pte_t tb_l2_tlb_resp_pte;
	logic tb_l2_tlb_resp_is_superpage;
	logic tb_l2_tlb_resp_access_fault_pt_access;

    // evict to L2 TLB
	logic DUT_l2_tlb_evict_valid, expected_l2_tlb_evict_valid;
	logic [ASID_WIDTH-1:0] DUT_l2_tlb_evict_ASID, expected_l2_tlb_evict_ASID;
	logic [VPN_WIDTH-1:0] DUT_l2_tlb_evict_VPN, expected_l2_tlb_evict_VPN;
	pte_t DUT_l2_tlb_evict_pte, expected_l2_tlb_evict_pte;
	logic DUT_l2_tlb_evict_is_superpage, expected_l2_tlb_evict_is_superpage;

    // sfence invalidation
	logic tb_sfence_inv_valid;
	logic [ASID_WIDTH-1:0] tb_sfence_inv_ASID;
	logic [VPN_WIDTH-1:0] tb_sfence_inv_VPN;

    // sfence invalidation backpressure
	logic DUT_sfence_inv_ready, expected_sfence_inv_ready;

    // ----------------------------------------------------------------
    // DUT instantiation:

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
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),

	    // core req
		.core_req_valid(tb_core_req_valid),
		.core_req_exec_mode(tb_core_req_exec_mode),
		.core_req_virtual_mode(tb_core_req_virtual_mode),
		.core_req_ASID(tb_core_req_ASID),
		.core_req_VPN(tb_core_req_VPN),

	    // core resp
		.core_resp_valid(DUT_core_resp_valid),
		.core_resp_PPN(DUT_core_resp_PPN),
		.core_resp_page_fault(DUT_core_resp_page_fault),
		.core_resp_access_fault(DUT_core_resp_access_fault),

	    // req to L2 TLB
		.l2_tlb_req_valid(DUT_l2_tlb_req_valid),
		.l2_tlb_req_tag(DUT_l2_tlb_req_tag),
		.l2_tlb_req_ASID(DUT_l2_tlb_req_ASID),
		.l2_tlb_req_VPN(DUT_l2_tlb_req_VPN),

		.l2_tlb_req_ready(tb_l2_tlb_req_ready),

	    // resp from L2 TLB
		.l2_tlb_resp_valid(tb_l2_tlb_resp_valid),
		.l2_tlb_resp_tag(tb_l2_tlb_resp_tag),
		.l2_tlb_resp_pte(tb_l2_tlb_resp_pte),
		.l2_tlb_resp_is_superpage(tb_l2_tlb_resp_is_superpage),
		.l2_tlb_resp_access_fault_pt_access(tb_l2_tlb_resp_access_fault_pt_access),

	    // evict to L2 TLB
		.l2_tlb_evict_valid(DUT_l2_tlb_evict_valid),
		.l2_tlb_evict_ASID(DUT_l2_tlb_evict_ASID),
		.l2_tlb_evict_VPN(DUT_l2_tlb_evict_VPN),
		.l2_tlb_evict_pte(DUT_l2_tlb_evict_pte),
		.l2_tlb_evict_is_superpage(DUT_l2_tlb_evict_is_superpage),

	    // sfence invalidation
		.sfence_inv_valid(tb_sfence_inv_valid),
		.sfence_inv_ASID(tb_sfence_inv_ASID),
		.sfence_inv_VPN(tb_sfence_inv_VPN),

	    // sfence invalidation backpressure
		.sfence_inv_ready(DUT_sfence_inv_ready)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_core_resp_valid !== DUT_core_resp_valid) begin
			$display("TB ERROR: expected_core_resp_valid (%h) != DUT_core_resp_valid (%h)",
				expected_core_resp_valid, DUT_core_resp_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_core_resp_PPN !== DUT_core_resp_PPN) begin
			$display("TB ERROR: expected_core_resp_PPN (%h) != DUT_core_resp_PPN (%h)",
				expected_core_resp_PPN, DUT_core_resp_PPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_core_resp_page_fault !== DUT_core_resp_page_fault) begin
			$display("TB ERROR: expected_core_resp_page_fault (%h) != DUT_core_resp_page_fault (%h)",
				expected_core_resp_page_fault, DUT_core_resp_page_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_core_resp_access_fault !== DUT_core_resp_access_fault) begin
			$display("TB ERROR: expected_core_resp_access_fault (%h) != DUT_core_resp_access_fault (%h)",
				expected_core_resp_access_fault, DUT_core_resp_access_fault);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_req_valid !== DUT_l2_tlb_req_valid) begin
			$display("TB ERROR: expected_l2_tlb_req_valid (%h) != DUT_l2_tlb_req_valid (%h)",
				expected_l2_tlb_req_valid, DUT_l2_tlb_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_req_tag !== DUT_l2_tlb_req_tag) begin
			$display("TB ERROR: expected_l2_tlb_req_tag (%h) != DUT_l2_tlb_req_tag (%h)",
				expected_l2_tlb_req_tag, DUT_l2_tlb_req_tag);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_req_ASID !== DUT_l2_tlb_req_ASID) begin
			$display("TB ERROR: expected_l2_tlb_req_ASID (%h) != DUT_l2_tlb_req_ASID (%h)",
				expected_l2_tlb_req_ASID, DUT_l2_tlb_req_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_req_VPN !== DUT_l2_tlb_req_VPN) begin
			$display("TB ERROR: expected_l2_tlb_req_VPN (%h) != DUT_l2_tlb_req_VPN (%h)",
				expected_l2_tlb_req_VPN, DUT_l2_tlb_req_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_evict_valid !== DUT_l2_tlb_evict_valid) begin
			$display("TB ERROR: expected_l2_tlb_evict_valid (%h) != DUT_l2_tlb_evict_valid (%h)",
				expected_l2_tlb_evict_valid, DUT_l2_tlb_evict_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_evict_ASID !== DUT_l2_tlb_evict_ASID) begin
			$display("TB ERROR: expected_l2_tlb_evict_ASID (%h) != DUT_l2_tlb_evict_ASID (%h)",
				expected_l2_tlb_evict_ASID, DUT_l2_tlb_evict_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_evict_VPN !== DUT_l2_tlb_evict_VPN) begin
			$display("TB ERROR: expected_l2_tlb_evict_VPN (%h) != DUT_l2_tlb_evict_VPN (%h)",
				expected_l2_tlb_evict_VPN, DUT_l2_tlb_evict_VPN);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_evict_pte !== DUT_l2_tlb_evict_pte) begin
			$display("TB ERROR: expected_l2_tlb_evict_pte (%h) != DUT_l2_tlb_evict_pte (%h)",
				expected_l2_tlb_evict_pte, DUT_l2_tlb_evict_pte);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_l2_tlb_evict_is_superpage !== DUT_l2_tlb_evict_is_superpage) begin
			$display("TB ERROR: expected_l2_tlb_evict_is_superpage (%h) != DUT_l2_tlb_evict_is_superpage (%h)",
				expected_l2_tlb_evict_is_superpage, DUT_l2_tlb_evict_is_superpage);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_sfence_inv_ready !== DUT_sfence_inv_ready) begin
			$display("TB ERROR: expected_sfence_inv_ready (%h) != DUT_sfence_inv_ready (%h)",
				expected_sfence_inv_ready, DUT_sfence_inv_ready);
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
	    // core req
		tb_core_req_valid = 1'b0;
		tb_core_req_exec_mode = M_MODE;
		tb_core_req_virtual_mode = 1'b0;
		tb_core_req_ASID = 9'h000;
		tb_core_req_VPN = 20'h00000;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b1;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h000;
		expected_l2_tlb_req_VPN = 20'h00000;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b0;
		tb_core_req_exec_mode = M_MODE;
		tb_core_req_virtual_mode = 1'b0;
		tb_core_req_ASID = 9'h000;
		tb_core_req_VPN = 20'h00000;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b1;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h000;
		expected_l2_tlb_req_VPN = 20'h00000;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

        // ------------------------------------------------------------
        // baremetal:
        test_case = "baremetal";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"baremetal",
			"\n\t\t", " first: 000,00000", 
			"\n\t\t", "second: ",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = M_MODE;
		tb_core_req_virtual_mode = 1'b0;
		tb_core_req_ASID = 9'h000;
		tb_core_req_VPN = 20'h00000;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b1;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h000;
		expected_l2_tlb_req_VPN = 20'h00000;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"baremetal",
			"\n\t\t", " first: 111,11111", 
			"\n\t\t", "second: 000,00000",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = M_MODE;
		tb_core_req_virtual_mode = 1'b0;
		tb_core_req_ASID = 9'h111;
		tb_core_req_VPN = 20'h11111;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b1;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b1;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h000;
		expected_l2_tlb_req_VPN = 20'h00000;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"baremetal",
			"\n\t\t", " first: 888,88888", 
			"\n\t\t", "second: 111,11111",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = M_MODE;
		tb_core_req_virtual_mode = 1'b0;
		tb_core_req_ASID = 9'h888;
		tb_core_req_VPN = 20'h88888;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b1;
		expected_core_resp_PPN = 22'h011111;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b1;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h111;
		expected_l2_tlb_req_VPN = 20'h11111;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"baremetal",
			"\n\t\t", " first: 001,00001", 
			"\n\t\t", "second: 888,88888",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = M_MODE;
		tb_core_req_virtual_mode = 1'b0;
		tb_core_req_ASID = 9'h001;
		tb_core_req_VPN = 20'h00010;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b1;
		expected_core_resp_PPN = 22'h388888;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h888;
		expected_l2_tlb_req_VPN = 20'h88888;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"baremetal",
			"\n\t\t", " first: ",
			"\n\t\t", "second: 001,00001",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b0;
		tb_core_req_exec_mode = M_MODE;
		tb_core_req_virtual_mode = 1'b0;
		tb_core_req_ASID = 9'h000;
		tb_core_req_VPN = 20'h00000;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b1;
		expected_core_resp_PPN = 22'h000010;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h001;
		expected_l2_tlb_req_VPN = 20'h00010;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

        // ------------------------------------------------------------
        // U mode:
        test_case = "U mode";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: 0f0,0f0f0", 
			"\n\t\t", "second: ",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'h0f0;
		tb_core_req_VPN = 20'h0f0f0;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b1;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h000;
		expected_l2_tlb_req_VPN = 20'h00000;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: 0f0,0f0f0", 
			"\n\t\t", "second: 0f0,0f0f0 (l2 req not ready)",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'h0f0;
		tb_core_req_VPN = 20'h0f0f0;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b0;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b1;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h0f0;
		expected_l2_tlb_req_VPN = 20'h0f0f0;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: 0f0,0f0f0", 
			"\n\t\t", "second: 0f0,0f0f0 (l2 req tag 0)",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'h0f0;
		tb_core_req_VPN = 20'h0f0f0;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b1;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'h0f0;
		expected_l2_tlb_req_VPN = 20'h0f0f0;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: f0f,f0f0f", 
			"\n\t\t", "second: 0f0,0f0f0",
			"\n\t\t", " other: tag 0 waiting"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'hf0f;
		tb_core_req_VPN = 20'hf0f0f;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h1;
		expected_l2_tlb_req_ASID = 9'h0f0;
		expected_l2_tlb_req_VPN = 20'h0f0f0;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: f0f,f0f0f", 
			"\n\t\t", "second: f0f,f0f0f (l2 req tag 1)",
			"\n\t\t", " other: tag 0 waiting"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'hf0f;
		tb_core_req_VPN = 20'hf0f0f;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b1;
		expected_l2_tlb_req_tag = 2'h1;
		expected_l2_tlb_req_ASID = 9'hf0f;
		expected_l2_tlb_req_VPN = 20'hf0f0f;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: f0f,f0f0f", 
			"\n\t\t", "second: f0f,f0f0f",
			"\n\t\t", " other: tag 0 waiting, tag 1 waiting"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'hf0f;
		tb_core_req_VPN = 20'hf0f0f;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h2;
		expected_l2_tlb_req_ASID = 9'hf0f;
		expected_l2_tlb_req_VPN = 20'hf0f0f;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: f0f,f0f0f", 
			"\n\t\t", "second: f0f,f0f0f",
			"\n\t\t", " other: tag 0 resp, tag 1 waiting"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'hf0f;
		tb_core_req_VPN = 20'hf0f0f;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b1;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			22'h30f30f,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1
		};
		tb_l2_tlb_resp_is_superpage = 1'b1;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h2;
		expected_l2_tlb_req_ASID = 9'hf0f;
		expected_l2_tlb_req_VPN = 20'hf0f0f;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			12'h000, 10'h000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: f0f,f0f0f", 
			"\n\t\t", "second: f0f,f0f0f",
			"\n\t\t", " other: tag 1 resp"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'hf0f;
		tb_core_req_VPN = 20'hf0f0f;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b1;
		tb_l2_tlb_resp_tag = 2'h1;
		tb_l2_tlb_resp_pte = {
			22'h3f03f0,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b1, 1'b1, 1'b0, 1'b0, 1'b1
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b0;
		expected_core_resp_PPN = 22'h000000;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'hf0f;
		expected_l2_tlb_req_VPN = 20'hf0f0f;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'h000;
		expected_l2_tlb_evict_VPN = 20'h00000;
		expected_l2_tlb_evict_pte = {
			22'h000000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {"U mode",
			"\n\t\t", " first: e1e,e1e1e", 
			"\n\t\t", "second: f0f,f0f0f (hit (forwarded))",
			"\n\t\t", " other: "
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // core req
		tb_core_req_valid = 1'b1;
		tb_core_req_exec_mode = U_MODE;
		tb_core_req_virtual_mode = 1'b1;
		tb_core_req_ASID = 9'he1e;
		tb_core_req_VPN = 20'he1e1e;
	    // core resp
	    // req to L2 TLB
		tb_l2_tlb_req_ready = 1'b1;
	    // resp from L2 TLB
		tb_l2_tlb_resp_valid = 1'b0;
		tb_l2_tlb_resp_tag = 2'h0;
		tb_l2_tlb_resp_pte = {
			22'h000000,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0
		};
		tb_l2_tlb_resp_is_superpage = 1'b0;
		tb_l2_tlb_resp_access_fault_pt_access = 1'b0;
	    // evict to L2 TLB
	    // sfence invalidation
		tb_sfence_inv_valid = 1'b0;
		tb_sfence_inv_ASID = 9'h000;
		tb_sfence_inv_VPN = 20'h00000;
	    // sfence invalidation backpressure

		@(negedge CLK);

		// outputs:

	    // core req
	    // core resp
		expected_core_resp_valid = 1'b1;
		expected_core_resp_PPN = 22'h3f03f0;
		expected_core_resp_page_fault = 1'b0;
		expected_core_resp_access_fault = 1'b0;
	    // req to L2 TLB
		expected_l2_tlb_req_valid = 1'b0;
		expected_l2_tlb_req_tag = 2'h0;
		expected_l2_tlb_req_ASID = 9'hf0f;
		expected_l2_tlb_req_VPN = 20'hf0f0f;
	    // resp from L2 TLB
	    // evict to L2 TLB
		expected_l2_tlb_evict_valid = 1'b0;
		expected_l2_tlb_evict_ASID = 9'hf0f;
		expected_l2_tlb_evict_VPN = 20'hf0f0f;
		expected_l2_tlb_evict_pte = {
			22'h3f03f0,
			2'b00,
			// D     A     G     U     X     W     R     V
			1'b0, 1'b1, 1'b0, 1'b1, 1'b1, 1'b0, 1'b0, 1'b1
		};
		expected_l2_tlb_evict_is_superpage = 1'b0;
	    // sfence invalidation
	    // sfence invalidation backpressure
		expected_sfence_inv_ready = 1'b1;

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