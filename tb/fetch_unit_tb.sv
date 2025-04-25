/*
    Filename: fetch_unit_tb.sv
    Author: zlagpacan
    Description: Testbench for fetch_unit module. 
    Spec: LOROF/spec/design/fetch_unit.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module fetch_unit_tb ();

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


    // itlb req
	logic DUT_itlb_req_valid, expected_itlb_req_valid;
	logic DUT_itlb_req_exec_mode, expected_itlb_req_exec_mode;
	logic DUT_itlb_req_virtual_mode, expected_itlb_req_virtual_mode;
	logic [VPN_WIDTH-1:0] DUT_itlb_req_vpn, expected_itlb_req_vpn;
	logic [ASID_WIDTH-1:0] DUT_itlb_req_ASID, expected_itlb_req_ASID;

    // itlb resp
	logic tb_itlb_resp_valid;
	logic [PPN_WIDTH-1:0] tb_itlb_resp_ppn;
	logic tb_itlb_resp_page_fault;
	logic tb_itlb_resp_access_fault;

    // icache req
	logic DUT_icache_req_valid, expected_icache_req_valid;
	logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] DUT_icache_req_block_offset, expected_icache_req_block_offset;
	logic [ICACHE_INDEX_WIDTH-1:0] DUT_icache_req_index, expected_icache_req_index;

    // icache resp
	logic [1:0] tb_icache_resp_valid_by_way;
	logic [1:0][ICACHE_TAG_WIDTH-1:0] tb_icache_resp_tag_by_way;
	logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0] tb_icache_resp_instr_16B_by_way;

    // icache resp feedback
	logic DUT_icache_resp_hit_valid, expected_icache_resp_hit_valid;
	logic DUT_icache_resp_hit_way, expected_icache_resp_hit_way;
	logic DUT_icache_resp_miss_valid, expected_icache_resp_miss_valid;
	logic [ICACHE_TAG_WIDTH-1:0] DUT_icache_resp_miss_tag, expected_icache_resp_miss_tag;

    // output to istream
	logic DUT_istream_valid_SENQ, expected_istream_valid_SENQ;
	logic [7:0] DUT_istream_valid_by_fetch_2B_SENQ, expected_istream_valid_by_fetch_2B_SENQ;
	logic [7:0] DUT_istream_one_hot_redirect_by_fetch_2B_SENQ, expected_istream_one_hot_redirect_by_fetch_2B_SENQ;
	logic [7:0][15:0] DUT_istream_instr_2B_by_fetch_2B_SENQ, expected_istream_instr_2B_by_fetch_2B_SENQ;
	logic [7:0][BTB_PRED_INFO_WIDTH-1:0] DUT_istream_pred_info_by_fetch_2B_SENQ, expected_istream_pred_info_by_fetch_2B_SENQ;
	logic [7:0] DUT_istream_pred_lru_by_fetch_2B_SENQ, expected_istream_pred_lru_by_fetch_2B_SENQ;
	logic [7:0][MDPT_INFO_WIDTH-1:0] DUT_istream_mdp_info_by_fetch_2B_SENQ, expected_istream_mdp_info_by_fetch_2B_SENQ;
	logic [31:0] DUT_istream_after_PC_SENQ, expected_istream_after_PC_SENQ;
	logic [LH_LENGTH-1:0] DUT_istream_LH_SENQ, expected_istream_LH_SENQ;
	logic [GH_LENGTH-1:0] DUT_istream_GH_SENQ, expected_istream_GH_SENQ;
	logic [RAS_INDEX_WIDTH-1:0] DUT_istream_ras_index_SENQ, expected_istream_ras_index_SENQ;
	logic DUT_istream_page_fault_SENQ, expected_istream_page_fault_SENQ;
	logic DUT_istream_access_fault_SENQ, expected_istream_access_fault_SENQ;

    // istream feedback
	logic tb_istream_stall_SENQ;

    // fetch + decode restart from ROB
	logic tb_rob_restart_valid;
	logic [31:0] tb_rob_restart_PC;
	logic [8:0] tb_rob_restart_ASID;
	logic [1:0] tb_rob_restart_exec_mode;
	logic tb_rob_restart_virtual_mode;

    // decode unit control
	logic tb_decode_restart_valid;
	logic [31:0] tb_decode_restart_PC;
	logic tb_decode_trigger_wait_for_restart;

    // branch update from decode unit
	logic tb_decode_unit_branch_update_valid;
	logic tb_decode_unit_branch_update_has_checkpoint;
	logic tb_decode_unit_branch_update_is_mispredict;
	logic tb_decode_unit_branch_update_is_taken;
	logic tb_decode_unit_branch_update_is_complex;
	logic tb_decode_unit_branch_update_use_upct;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_decode_unit_branch_update_intermediate_pred_info;
	logic tb_decode_unit_branch_update_pred_lru;
	logic [31:0] tb_decode_unit_branch_update_start_PC;
	logic [31:0] tb_decode_unit_branch_update_target_PC;
	logic [LH_LENGTH-1:0] tb_decode_unit_branch_update_LH;
	logic [GH_LENGTH-1:0] tb_decode_unit_branch_update_GH;
	logic [RAS_INDEX_WIDTH-1:0] tb_decode_unit_branch_update_ras_index;

    // mdpt update
	logic tb_mdpt_update_valid;
	logic [31:0] tb_mdpt_update_start_full_PC;
	logic [ASID_WIDTH-1:0] tb_mdpt_update_ASID;
	logic [MDPT_INFO_WIDTH-1:0] tb_mdpt_update_mdp_info;

    // ----------------------------------------------------------------
    // DUT instantiation:

	fetch_unit #(
		.INIT_PC(32'h0),
		.INIT_ASID(9'h0),
		.INIT_EXEC_MODE(M_MODE),
		.INIT_VIRTUAL_MODE(1'b0),
		.INIT_WAIT_FOR_RESTART_STATE(1'b1)
	) DUT (
		// seq
		.CLK(CLK),
		.nRST(nRST),


	    // itlb req
		.itlb_req_valid(DUT_itlb_req_valid),
		.itlb_req_exec_mode(DUT_itlb_req_exec_mode),
		.itlb_req_virtual_mode(DUT_itlb_req_virtual_mode),
		.itlb_req_vpn(DUT_itlb_req_vpn),
		.itlb_req_ASID(DUT_itlb_req_ASID),

	    // itlb resp
		.itlb_resp_valid(tb_itlb_resp_valid),
		.itlb_resp_ppn(tb_itlb_resp_ppn),
		.itlb_resp_page_fault(tb_itlb_resp_page_fault),
		.itlb_resp_access_fault(tb_itlb_resp_access_fault),

	    // icache req
		.icache_req_valid(DUT_icache_req_valid),
		.icache_req_block_offset(DUT_icache_req_block_offset),
		.icache_req_index(DUT_icache_req_index),

	    // icache resp
		.icache_resp_valid_by_way(tb_icache_resp_valid_by_way),
		.icache_resp_tag_by_way(tb_icache_resp_tag_by_way),
		.icache_resp_instr_16B_by_way(tb_icache_resp_instr_16B_by_way),

	    // icache resp feedback
		.icache_resp_hit_valid(DUT_icache_resp_hit_valid),
		.icache_resp_hit_way(DUT_icache_resp_hit_way),
		.icache_resp_miss_valid(DUT_icache_resp_miss_valid),
		.icache_resp_miss_tag(DUT_icache_resp_miss_tag),

	    // output to istream
		.istream_valid_SENQ(DUT_istream_valid_SENQ),
		.istream_valid_by_fetch_2B_SENQ(DUT_istream_valid_by_fetch_2B_SENQ),
		.istream_one_hot_redirect_by_fetch_2B_SENQ(DUT_istream_one_hot_redirect_by_fetch_2B_SENQ),
		.istream_instr_2B_by_fetch_2B_SENQ(DUT_istream_instr_2B_by_fetch_2B_SENQ),
		.istream_pred_info_by_fetch_2B_SENQ(DUT_istream_pred_info_by_fetch_2B_SENQ),
		.istream_pred_lru_by_fetch_2B_SENQ(DUT_istream_pred_lru_by_fetch_2B_SENQ),
		.istream_mdp_info_by_fetch_2B_SENQ(DUT_istream_mdp_info_by_fetch_2B_SENQ),
		.istream_after_PC_SENQ(DUT_istream_after_PC_SENQ),
		.istream_LH_SENQ(DUT_istream_LH_SENQ),
		.istream_GH_SENQ(DUT_istream_GH_SENQ),
		.istream_ras_index_SENQ(DUT_istream_ras_index_SENQ),
		.istream_page_fault_SENQ(DUT_istream_page_fault_SENQ),
		.istream_access_fault_SENQ(DUT_istream_access_fault_SENQ),

	    // istream feedback
		.istream_stall_SENQ(tb_istream_stall_SENQ),

	    // fetch + decode restart from ROB
		.rob_restart_valid(tb_rob_restart_valid),
		.rob_restart_PC(tb_rob_restart_PC),
		.rob_restart_ASID(tb_rob_restart_ASID),
		.rob_restart_exec_mode(tb_rob_restart_exec_mode),
		.rob_restart_virtual_mode(tb_rob_restart_virtual_mode),

	    // decode unit control
		.decode_restart_valid(tb_decode_restart_valid),
		.decode_restart_PC(tb_decode_restart_PC),
		.decode_trigger_wait_for_restart(tb_decode_trigger_wait_for_restart),

	    // branch update from decode unit
		.decode_unit_branch_update_valid(tb_decode_unit_branch_update_valid),
		.decode_unit_branch_update_has_checkpoint(tb_decode_unit_branch_update_has_checkpoint),
		.decode_unit_branch_update_is_mispredict(tb_decode_unit_branch_update_is_mispredict),
		.decode_unit_branch_update_is_taken(tb_decode_unit_branch_update_is_taken),
		.decode_unit_branch_update_is_complex(tb_decode_unit_branch_update_is_complex),
		.decode_unit_branch_update_use_upct(tb_decode_unit_branch_update_use_upct),
		.decode_unit_branch_update_intermediate_pred_info(tb_decode_unit_branch_update_intermediate_pred_info),
		.decode_unit_branch_update_pred_lru(tb_decode_unit_branch_update_pred_lru),
		.decode_unit_branch_update_start_PC(tb_decode_unit_branch_update_start_PC),
		.decode_unit_branch_update_target_PC(tb_decode_unit_branch_update_target_PC),
		.decode_unit_branch_update_LH(tb_decode_unit_branch_update_LH),
		.decode_unit_branch_update_GH(tb_decode_unit_branch_update_GH),
		.decode_unit_branch_update_ras_index(tb_decode_unit_branch_update_ras_index),

	    // mdpt update
		.mdpt_update_valid(tb_mdpt_update_valid),
		.mdpt_update_start_full_PC(tb_mdpt_update_start_full_PC),
		.mdpt_update_ASID(tb_mdpt_update_ASID),
		.mdpt_update_mdp_info(tb_mdpt_update_mdp_info)
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

		if (expected_itlb_req_vpn !== DUT_itlb_req_vpn) begin
			$display("TB ERROR: expected_itlb_req_vpn (%h) != DUT_itlb_req_vpn (%h)",
				expected_itlb_req_vpn, DUT_itlb_req_vpn);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_itlb_req_ASID !== DUT_itlb_req_ASID) begin
			$display("TB ERROR: expected_itlb_req_ASID (%h) != DUT_itlb_req_ASID (%h)",
				expected_itlb_req_ASID, DUT_itlb_req_ASID);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_valid !== DUT_icache_req_valid) begin
			$display("TB ERROR: expected_icache_req_valid (%h) != DUT_icache_req_valid (%h)",
				expected_icache_req_valid, DUT_icache_req_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_block_offset !== DUT_icache_req_block_offset) begin
			$display("TB ERROR: expected_icache_req_block_offset (%h) != DUT_icache_req_block_offset (%h)",
				expected_icache_req_block_offset, DUT_icache_req_block_offset);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_req_index !== DUT_icache_req_index) begin
			$display("TB ERROR: expected_icache_req_index (%h) != DUT_icache_req_index (%h)",
				expected_icache_req_index, DUT_icache_req_index);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_hit_valid !== DUT_icache_resp_hit_valid) begin
			$display("TB ERROR: expected_icache_resp_hit_valid (%h) != DUT_icache_resp_hit_valid (%h)",
				expected_icache_resp_hit_valid, DUT_icache_resp_hit_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_hit_way !== DUT_icache_resp_hit_way) begin
			$display("TB ERROR: expected_icache_resp_hit_way (%h) != DUT_icache_resp_hit_way (%h)",
				expected_icache_resp_hit_way, DUT_icache_resp_hit_way);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_miss_valid !== DUT_icache_resp_miss_valid) begin
			$display("TB ERROR: expected_icache_resp_miss_valid (%h) != DUT_icache_resp_miss_valid (%h)",
				expected_icache_resp_miss_valid, DUT_icache_resp_miss_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_icache_resp_miss_tag !== DUT_icache_resp_miss_tag) begin
			$display("TB ERROR: expected_icache_resp_miss_tag (%h) != DUT_icache_resp_miss_tag (%h)",
				expected_icache_resp_miss_tag, DUT_icache_resp_miss_tag);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_valid_SENQ !== DUT_istream_valid_SENQ) begin
			$display("TB ERROR: expected_istream_valid_SENQ (%h) != DUT_istream_valid_SENQ (%h)",
				expected_istream_valid_SENQ, DUT_istream_valid_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_valid_by_fetch_2B_SENQ !== DUT_istream_valid_by_fetch_2B_SENQ) begin
			$display("TB ERROR: expected_istream_valid_by_fetch_2B_SENQ (%h) != DUT_istream_valid_by_fetch_2B_SENQ (%h)",
				expected_istream_valid_by_fetch_2B_SENQ, DUT_istream_valid_by_fetch_2B_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_one_hot_redirect_by_fetch_2B_SENQ !== DUT_istream_one_hot_redirect_by_fetch_2B_SENQ) begin
			$display("TB ERROR: expected_istream_one_hot_redirect_by_fetch_2B_SENQ (%h) != DUT_istream_one_hot_redirect_by_fetch_2B_SENQ (%h)",
				expected_istream_one_hot_redirect_by_fetch_2B_SENQ, DUT_istream_one_hot_redirect_by_fetch_2B_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_instr_2B_by_fetch_2B_SENQ !== DUT_istream_instr_2B_by_fetch_2B_SENQ) begin
			$display("TB ERROR: expected_istream_instr_2B_by_fetch_2B_SENQ (%h) != DUT_istream_instr_2B_by_fetch_2B_SENQ (%h)",
				expected_istream_instr_2B_by_fetch_2B_SENQ, DUT_istream_instr_2B_by_fetch_2B_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_pred_info_by_fetch_2B_SENQ !== DUT_istream_pred_info_by_fetch_2B_SENQ) begin
			$display("TB ERROR: expected_istream_pred_info_by_fetch_2B_SENQ (%h) != DUT_istream_pred_info_by_fetch_2B_SENQ (%h)",
				expected_istream_pred_info_by_fetch_2B_SENQ, DUT_istream_pred_info_by_fetch_2B_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_pred_lru_by_fetch_2B_SENQ !== DUT_istream_pred_lru_by_fetch_2B_SENQ) begin
			$display("TB ERROR: expected_istream_pred_lru_by_fetch_2B_SENQ (%h) != DUT_istream_pred_lru_by_fetch_2B_SENQ (%h)",
				expected_istream_pred_lru_by_fetch_2B_SENQ, DUT_istream_pred_lru_by_fetch_2B_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_mdp_info_by_fetch_2B_SENQ !== DUT_istream_mdp_info_by_fetch_2B_SENQ) begin
			$display("TB ERROR: expected_istream_mdp_info_by_fetch_2B_SENQ (%h) != DUT_istream_mdp_info_by_fetch_2B_SENQ (%h)",
				expected_istream_mdp_info_by_fetch_2B_SENQ, DUT_istream_mdp_info_by_fetch_2B_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_after_PC_SENQ !== DUT_istream_after_PC_SENQ) begin
			$display("TB ERROR: expected_istream_after_PC_SENQ (%h) != DUT_istream_after_PC_SENQ (%h)",
				expected_istream_after_PC_SENQ, DUT_istream_after_PC_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_LH_SENQ !== DUT_istream_LH_SENQ) begin
			$display("TB ERROR: expected_istream_LH_SENQ (%h) != DUT_istream_LH_SENQ (%h)",
				expected_istream_LH_SENQ, DUT_istream_LH_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_GH_SENQ !== DUT_istream_GH_SENQ) begin
			$display("TB ERROR: expected_istream_GH_SENQ (%h) != DUT_istream_GH_SENQ (%h)",
				expected_istream_GH_SENQ, DUT_istream_GH_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_ras_index_SENQ !== DUT_istream_ras_index_SENQ) begin
			$display("TB ERROR: expected_istream_ras_index_SENQ (%h) != DUT_istream_ras_index_SENQ (%h)",
				expected_istream_ras_index_SENQ, DUT_istream_ras_index_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_page_fault_SENQ !== DUT_istream_page_fault_SENQ) begin
			$display("TB ERROR: expected_istream_page_fault_SENQ (%h) != DUT_istream_page_fault_SENQ (%h)",
				expected_istream_page_fault_SENQ, DUT_istream_page_fault_SENQ);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_istream_access_fault_SENQ !== DUT_istream_access_fault_SENQ) begin
			$display("TB ERROR: expected_istream_access_fault_SENQ (%h) != DUT_istream_access_fault_SENQ (%h)",
				expected_istream_access_fault_SENQ, DUT_istream_access_fault_SENQ);
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
		tb_itlb_resp_ppn = 22'h0;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {22'h0, 22'h0};
		tb_icache_resp_instr_16B_by_way = {128'h0, 128'h0};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b0;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h0;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b0;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h0;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h0;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
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
		tb_itlb_resp_ppn = 22'h0;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {22'h0, 22'h0};
		tb_icache_resp_instr_16B_by_way = {128'h0, 128'h0};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b0;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h0;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b0;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h0;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h0;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

        // ------------------------------------------------------------
        // simple sequence:
        test_case = "simple sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "rob restart @ 0x12340000";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_ppn = 22'h0;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {22'h0, 22'h0};
		tb_icache_resp_instr_16B_by_way = {128'h0, 128'h0};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b1;
		tb_rob_restart_PC = 32'h12340000;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b0;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h0;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b0;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h0;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h0;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340000, resp: IDLE";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_ppn = 22'h0;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b00;
		tb_icache_resp_tag_by_way = {22'h0, 22'h0};
		tb_icache_resp_instr_16B_by_way = {128'h0, 128'h0};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h0;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h0;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340000;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340000, resp: 12340000 itlb miss";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_ppn = 22'h0;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b11;
		tb_icache_resp_tag_by_way = {22'h12340, 22'h56780};
		tb_icache_resp_instr_16B_by_way = {128'hdeadbeef, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h0;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h12345678;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340000;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340000, resp: 12340000 itlb miss";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b0;
		tb_itlb_resp_ppn = 22'h0;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b11;
		tb_icache_resp_tag_by_way = {22'h12345, 22'h56789};
		tb_icache_resp_instr_16B_by_way = {128'hdeadbeef, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h0;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h12345678;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340000;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340000, resp: 12340000 icache miss";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b11;
		tb_icache_resp_tag_by_way = {22'h12345, 22'h56789};
		tb_icache_resp_instr_16B_by_way = {128'hdeadbeef, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b1;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h12345678;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340000;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340000, resp: 12340000 ihit & istream stall";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b11;
		tb_icache_resp_tag_by_way = {22'h123456, 22'h56789};
		tb_icache_resp_instr_16B_by_way = {128'h081a2b3c4d5e6f8091a2b3c4d5e6f7, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b1;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b1;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h081a2b3c4d5e6f8091a2b3c4d5e6f7;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340000;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340010, resp: 12340000 ihit";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b11;
		tb_icache_resp_tag_by_way = {22'h123456, 22'h56789};
		tb_icache_resp_instr_16B_by_way = {128'h08192a3b4c5d6e7f8091a2b3c4d5e6f7, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b1;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h08192a3b4c5d6e7f8091a2b3c4d5e6f7;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340010;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340020, resp: 12340010 ihit";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b11;
		tb_icache_resp_tag_by_way = {22'h123456, 22'h56789};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h1;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b1;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h0123456789abcdeffedcba9876543210;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340020;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340020, resp: 12340020 icache miss";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h123456, 22'h56789};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h1;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b1;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h12345678;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340020;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340020, resp: 12340020 icache miss 2";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h123456, 22'h56789};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'h12345678};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h1;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b0;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b1;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h12345678;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340020;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = "req: 12340030, resp: 12340020 ihit";
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'h0;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h0;
		tb_decode_unit_branch_update_target_PC = 32'h0;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h1;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340030;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

        // ------------------------------------------------------------
        // branch updates:
        test_case = "branch updates";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		// branch updates
			// "\t\tbranch update 56780010 J -> 5677FFF2"
			// "\t\tbranch update 5677FFF8 JAL -> BCDEEFFE"
			// "\t\tbranch update BCDEFF04 RETL -> 5677FFFA"
			// "\t\tbranch update 5678000C RET -> ABCDEF06"
			// "\t\tbranch update BCDEFF0A simple B NT"
			// "\t\tbranch update BCDEFF0E simple B T -> BCDEFFDE"
			// "\t\tbranch update BCDEEFFC J (ignored) -> 12345678"
			// "\t\tbranch update 5677FFF2 nothing"
			
			// "\t\tbranch update BCDEFFE6 complex B local A NT -> BCDEFFFC",
				// "\n\t\t\tlocal A AA->58, global 123->246"
			// "\t\tbranch update BCDEFFE8 complex B global B NT -> BCDF0004",
				// "\n\t\t\tlocal B BB->76, global 246->48C"
			// "\t\tbranch update BCDEFFFE complex B local C T -> BCDEFFE4",
				// "\n\t\t\tlocal C CC->99, global 48C->919"
			// "\t\tbranch update BCDEFFE6 complex B local A T -> BCDEFFFC",
				// "\n\t\t\tlocal A 58->B0, global 919->233"
			// "\t\tbranch update BCDEFFFE complex B local C NT -> BCDEFFE4",
				// "\n\t\t\tlocal C 99->32, global 233->466"
			// "\t\tbranch update BCDF0006 complex B global D T -> BCDEFFE8",
				// "\n\t\t\tlocal D DD->BB, global 466->8CD"
			// "\t\tbranch update BCDEFFE8 complex B global B T -> BCDF0004",
				// "\n\t\t\tlocal B 76->ED, global 8CD->19B"
			// "\t\tbranch update BCDF0006 complex B global D NT -> BCDEFFE8",
				// "\n\t\t\tlocal D BB->76, global 19B->336"

			// "\t\tbranch update BCDEFFE6 complex B local A -> BCDEFFFC",
				// "\n\t\t\tLH=AA, GH=FFE"
			// "\t\tbranch update BCDEFFE8 complex B global B -> BCDF0004",
				// "\n\t\t\tLH=BB, GH=FFF"
			// "\t\tbranch update BCDEFFFE complex B local C -> BCDEFFE4",
				// "\n\t\t\tLH=CC, GH=FFE"
			// "\t\tbranch update BCDF0006 complex B local D -> BCDEFFE8",
				// "\n\t\t\tLH=DD, GH=123, ras_index=2"

			// "\t\tbranch update BCDF000A J -> 80808080"

			// restart @ 5678000E

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340040, resp: 12340030 ihit\n",
			"\t\tbranch update 56780010 J -> 5677FFF2"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b1;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b01000111;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h56780010;
		tb_decode_unit_branch_update_target_PC = 32'h5677FFF2;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h2;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340040;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340050, resp: 12340040 ihit\n",
			"\t\tbranch update 5677FFF8 JAL -> BCDEEFFE"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b1;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b01010101;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'h5677FFF8;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEEFFE;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h2;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340050;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340060, resp: 12340050 ihit\n",
			"\t\tbranch update BCDEFF04 RETL -> 5677FFFA"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b01110111;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFF04;
		tb_decode_unit_branch_update_target_PC = 32'h01234567;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h3;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340060;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340070, resp: 12340060 ihit\n",
			"\t\tbranch update 5678000C RET -> ABCDEF06"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b01100110;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h5678000C;
		tb_decode_unit_branch_update_target_PC = 32'h89abcdef;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h3;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340070;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340080, resp: 12340070 ihit\n",
			"\t\tbranch update BCDEFF0A simple B NT"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b1;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b10011001;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFF0A;
		tb_decode_unit_branch_update_target_PC = 32'h01020304;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h4;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340080;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340090, resp: 12340080 ihit\n",
			"\t\tbranch update BCDEFF0E simple B T -> BCDEFFDE"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b10100101;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFF0E;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFDE;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h4;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340090;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 123400A0, resp: 12340090 ihit\n",
			"\t\tbranch update BCDEEFFC J (ignored) -> 12345678"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b10000000;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEEFFC;
		tb_decode_unit_branch_update_target_PC = 32'h12345678;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h5;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h123400A0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 123400B0, resp: 123400A0 ihit\n",
			"\t\tbranch update 5677FFF2 nothing"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b00111111;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'h5677FFF2;
		tb_decode_unit_branch_update_target_PC = 32'h12345678;
		tb_decode_unit_branch_update_LH = 8'h0;
		tb_decode_unit_branch_update_GH = 12'h0;
		tb_decode_unit_branch_update_ras_index = 3'h0;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h5;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h123400B0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 123400C0, resp: 123400B0 ihit\n",
			"\t\tbranch update BCDEFFE6 complex B local A NT -> BCDEFFFC",
				"\n\t\t\tlocal A AA->58, global 123->246"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11100000;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFE6;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFFC;
		tb_decode_unit_branch_update_LH = 8'hAA;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h6;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h123400C0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 123400D0, resp: 123400C0 ihit\n",
			"\t\tbranch update BCDEFFE8 complex B global B NT -> BCDF0004",
				"\n\t\t\tlocal B BB->76, global 246->48C"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11011011;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFE8;
		tb_decode_unit_branch_update_target_PC = 32'hBCDF0004;
		tb_decode_unit_branch_update_LH = 8'hBB;
		tb_decode_unit_branch_update_GH = 12'h246;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h6;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h123400D0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 123400E0, resp: 123400D0 ihit\n",
			"\t\tbranch update BCDEFFFE complex B local C T -> BCDEFFE4",
				"\n\t\t\tlocal C CC->99, global 48C->919"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11010000;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFFE;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFE4;
		tb_decode_unit_branch_update_LH = 8'hCC;
		tb_decode_unit_branch_update_GH = 12'h48C;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h7;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h123400E0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 123400F0, resp: 123400E0 ihit\n",
			"\t\tbranch update BCDEFFE6 complex B local A T -> BCDEFFFC",
				"\n\t\t\tlocal A 58->B0, global 919->233"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11100000;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFE6;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFFC;
		tb_decode_unit_branch_update_LH = 8'h58;
		tb_decode_unit_branch_update_GH = 12'h919;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h7;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h123400F0;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340100, resp: 123400F0 ihit\n",
			"\t\tbranch update BCDEFFFE complex B local C NT -> BCDEFFE4",
				"\n\t\t\tlocal C 99->32, global 233->466"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11010000;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFFE;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFE4;
		tb_decode_unit_branch_update_LH = 8'h99;
		tb_decode_unit_branch_update_GH = 12'h233;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h8;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340100;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340110, resp: 12340100 ihit\n",
			"\t\tbranch update BCDF0006 complex B global D T -> BCDEFFE8",
				"\n\t\t\tlocal D DD->BB, global 466->8CD"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11110000;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDF0006;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFE8;
		tb_decode_unit_branch_update_LH = 8'hDD;
		tb_decode_unit_branch_update_GH = 12'h466;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h8;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340110;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340120, resp: 12340110 ihit\n",
			"\t\tbranch update BCDEFFE8 complex B global B T -> BCDF0004",
				"\n\t\t\tlocal B 76->ED, global 8CD->19B"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11011011;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFE8;
		tb_decode_unit_branch_update_target_PC = 32'hBCDF0004;
		tb_decode_unit_branch_update_LH = 8'h76;
		tb_decode_unit_branch_update_GH = 12'h8CD;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h9;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340120;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340130, resp: 12340120 ihit\n",
			"\t\tbranch update BCDF0006 complex B global D NT -> BCDEFFE8",
				"\n\t\t\tlocal D BB->76, global 19B->336"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11110000;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDF0006;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFE8;
		tb_decode_unit_branch_update_LH = 8'hBB;
		tb_decode_unit_branch_update_GH = 12'h19B;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h9;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340130;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340140, resp: 12340130 ihit\n",
			"\t\tbranch update BCDEFFE6 complex B local A -> BCDEFFFC",
				"\n\t\t\tLH=AA, GH=FFF"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b1;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11100000;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFE6;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFFC;
		tb_decode_unit_branch_update_LH = 8'h55;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'hA;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340140;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h0;
		expected_istream_ras_index_SENQ = 3'h0;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340150, resp: 12340140 ihit\n",
			"\t\tbranch update BCDEFFE8 complex B global B -> BCDF0004",
				"\n\t\t\tLH=BB, GH=FFF"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b1;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11100000;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFE8;
		tb_decode_unit_branch_update_target_PC = 32'hBCDF0004;
		tb_decode_unit_branch_update_LH = 8'h5D;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'hA;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340150;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'hFFE;
		expected_istream_ras_index_SENQ = 3'h7;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340160, resp: 12340150 ihit\n",
			"\t\tbranch update BCDEFFFE complex B local C -> BCDEFFE4",
				"\n\t\t\tLH=CC, GH=FFE"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b1;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11010000;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDEFFFE;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFE4;
		tb_decode_unit_branch_update_LH = 8'h66;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'hB;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340160;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'hFFF;
		expected_istream_ras_index_SENQ = 3'h7;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340170, resp: 12340160 ihit\n",
			"\t\tbranch update BCDEFFFE complex B local D -> BCDEFFE8",
				"\n\t\t\tLH=DD, GH=123, ras_index=2"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b1;
		tb_decode_unit_branch_update_is_mispredict = 1'b1;
		tb_decode_unit_branch_update_is_taken = 1'b1;
		tb_decode_unit_branch_update_is_complex = 1'b1;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b11110000;
		tb_decode_unit_branch_update_pred_lru = 1'b1;
		tb_decode_unit_branch_update_start_PC = 32'hBCDF0006;
		tb_decode_unit_branch_update_target_PC = 32'hBCDEFFE8;
		tb_decode_unit_branch_update_LH = 8'h6E;
		tb_decode_unit_branch_update_GH = 12'h891;
		tb_decode_unit_branch_update_ras_index = 3'h2;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'hB;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340170;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'hFFE;
		expected_istream_ras_index_SENQ = 3'h7;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340180, resp: 12340170 ihit\n",
			"\t\tbranch update BCDF000A J -> 80808080"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b1;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b1;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'b10000001;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hBCDF000A;
		tb_decode_unit_branch_update_target_PC = 32'h80808080;
		tb_decode_unit_branch_update_LH = 8'hFF;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'hC;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340180;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h123;
		expected_istream_ras_index_SENQ = 3'h2;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

        // ------------------------------------------------------------
        // branch sequence:
        test_case = "branch sequence";
        $display("\ntest %0d: %s", test_num, test_case);
        test_num++;

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 12340190, resp: 12340180 ihit, decode restart @ 5678000E"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b1;
		tb_decode_restart_PC = 32'h5678000E;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'hFF;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hFFFFFFFF;
		tb_decode_unit_branch_update_target_PC = 32'hFFFFFFFF;
		tb_decode_unit_branch_update_LH = 8'hFF;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h12340;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'hC;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h12340190;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h123;
		expected_istream_ras_index_SENQ = 3'h2;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 5678000E, resp: 12340180 IDLE"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h123456;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b01;
		tb_icache_resp_tag_by_way = {22'h56789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'hFF;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hFFFFFFFF;
		tb_decode_unit_branch_update_target_PC = 32'hFFFFFFFF;
		tb_decode_unit_branch_update_LH = 8'hFF;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h56780;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b0;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b0;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h123456;
	    // output to istream
		expected_istream_valid_SENQ = 1'b0;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b11111111;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'hfedcba98765432100123456789abcdef;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h5678000E;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h123;
		expected_istream_ras_index_SENQ = 3'h2;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
	    // mdpt update

		check_outputs();

		@(posedge CLK); #(PERIOD/10);

		// inputs
		sub_test_case = {
			"req: 56780010, resp: 5678000E ihit"
		};
		$display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // itlb req
	    // itlb resp
		tb_itlb_resp_valid = 1'b1;
		tb_itlb_resp_ppn = 22'h056789;
		tb_itlb_resp_page_fault = 1'b0;
		tb_itlb_resp_access_fault = 1'b0;
	    // icache req
	    // icache resp
		tb_icache_resp_valid_by_way = 2'b10;
		tb_icache_resp_tag_by_way = {22'h056789, 22'h123456};
		tb_icache_resp_instr_16B_by_way = {128'h0123456789abcdeffedcba9876543210, 128'hfedcba98765432100123456789abcdef};
	    // icache resp feedback
	    // output to istream
	    // istream feedback
		tb_istream_stall_SENQ = 1'b0;
	    // fetch + decode restart from ROB
		tb_rob_restart_valid = 1'b0;
		tb_rob_restart_PC = 32'h0;
		tb_rob_restart_ASID = 9'h0;
		tb_rob_restart_exec_mode = M_MODE;
		tb_rob_restart_virtual_mode = 1'b0;
	    // decode unit control
		tb_decode_restart_valid = 1'b0;
		tb_decode_restart_PC = 32'h0;
		tb_decode_trigger_wait_for_restart = 1'b0;
	    // branch update from decode unit
		tb_decode_unit_branch_update_valid = 1'b0;
		tb_decode_unit_branch_update_has_checkpoint = 1'b0;
		tb_decode_unit_branch_update_is_mispredict = 1'b0;
		tb_decode_unit_branch_update_is_taken = 1'b0;
		tb_decode_unit_branch_update_is_complex = 1'b0;
		tb_decode_unit_branch_update_use_upct = 1'b0;
		tb_decode_unit_branch_update_intermediate_pred_info = 8'hFF;
		tb_decode_unit_branch_update_pred_lru = 1'b0;
		tb_decode_unit_branch_update_start_PC = 32'hFFFFFFFF;
		tb_decode_unit_branch_update_target_PC = 32'hFFFFFFFF;
		tb_decode_unit_branch_update_LH = 8'hFF;
		tb_decode_unit_branch_update_GH = 12'hFFF;
		tb_decode_unit_branch_update_ras_index = 3'h7;
	    // mdpt update
		tb_mdpt_update_valid = 1'b0;
		tb_mdpt_update_start_full_PC = 32'h0;
		tb_mdpt_update_ASID = 9'h0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h56780;
		expected_itlb_req_ASID = 9'h0;
	    // itlb resp
	    // icache req
		expected_icache_req_valid = 1'b1;
		expected_icache_req_block_offset = 1'b1;
		expected_icache_req_index = 7'h0;
	    // icache resp
	    // icache resp feedback
		expected_icache_resp_hit_valid = 1'b1;
		expected_icache_resp_hit_way = 1'b1;
		expected_icache_resp_miss_valid = 1'b0;
		expected_icache_resp_miss_tag = 22'h056789;
	    // output to istream
		expected_istream_valid_SENQ = 1'b1;
		expected_istream_valid_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = 128'h0123456789abcdeffedcba9876543210;
		expected_istream_pred_info_by_fetch_2B_SENQ = {
			8'h0,
			8'b01100110,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
		expected_istream_pred_lru_by_fetch_2B_SENQ = 8'b00100000;
		expected_istream_mdp_info_by_fetch_2B_SENQ = 64'h0;
		expected_istream_after_PC_SENQ = 32'h56780010;
		expected_istream_LH_SENQ = 8'h0;
		expected_istream_GH_SENQ = 12'h123;
		expected_istream_ras_index_SENQ = 3'h2;
		expected_istream_page_fault_SENQ = 1'b0;
		expected_istream_access_fault_SENQ = 1'b0;
	    // istream feedback
	    // fetch + decode restart from ROB
	    // decode unit control
	    // branch update from decode unit
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
            $display("FAIL: %d tests fail", num_errors);
        end
        else begin
            $display("SUCCESS: all tests pass");
        end
        $display();

        $finish();
    end

endmodule