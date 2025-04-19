// need to send decode_unit restart to fetch_unit AFTER decode_unit update has finished
    // don't want another mispred


    #(
		.INIT_PC(32'h0),
		.INIT_ASID(9'h0),
		.INIT_EXEC_MODE(M_MODE),
		.INIT_VIRTUAL_MODE(1'b0),
		.INIT_WAIT_FOR_RESTART_STATE(1'b1)
	) 


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
		tb_icache_resp_instr_16B_by_way = {
			{
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00
			},
			{
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00
			}
		};
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
		tb_decode_wait_for_restart = 1'b0;
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
		tb_mdpt_update_ASID = 1'b0;
		tb_mdpt_update_mdp_info = 8'h0;

		@(negedge CLK);

		// outputs:

	    // itlb req
		expected_itlb_req_valid = 1'b1;
		expected_itlb_req_exec_mode = M_MODE;
		expected_itlb_req_virtual_mode = 1'b0;
		expected_itlb_req_vpn = 22'h0;
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
		expected_istream_valid_by_fetch_2B_SENQ = 8'b00000000;
		expected_istream_one_hot_redirect_by_fetch_2B_SENQ = 8'b10000000;
		expected_istream_instr_2B_by_fetch_2B_SENQ = {
			{
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00
			},
			{
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00,
				14'h0, 2'b00
			}
		};
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
		expected_istream_mdp_info_by_fetch_2B_SENQ = {
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0,
			8'h0
		};
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