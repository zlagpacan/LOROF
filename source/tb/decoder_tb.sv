/*
    Filename: decoder_tb.sv
    Author: zlagpacan
    Description: Testbench for decoder module. 
    Spec: LOROF/spec/design/decoder.md
*/

`timescale 1ns/100ps

`include "corep.vh"
`include "instrp.vh"

module decoder_tb #(
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

    // environment info
	corep::exec_mode_t tb_env_exec_mode;
	logic tb_env_trap_sfence;
	logic tb_env_trap_wfi;
	logic tb_env_trap_sret;
	logic tb_env_menvconfig_FIOM;
	logic tb_env_senvconfig_FIOM;

    // instr info
	corep::fetch4B_t tb_fetch4B;
	logic tb_btb_hit;
	logic tb_redirect_taken;
	logic tb_mid_instr_redirect;

    // FU select
	logic DUT_is_alu_reg, expected_is_alu_reg;
	logic DUT_is_alu_imm, expected_is_alu_imm;
	logic DUT_is_bru, expected_is_bru;
	logic DUT_is_mdu, expected_is_mdu;
	logic DUT_is_fpu, expected_is_fpu;
	logic DUT_is_ldu, expected_is_ldu;
	logic DUT_is_store, expected_is_store;
	logic DUT_is_amo, expected_is_amo;
	logic DUT_is_fence, expected_is_fence;
	logic DUT_is_sysu, expected_is_sysu;
	logic DUT_is_illegal_instr, expected_is_illegal_instr;

    // op
	logic [3:0] DUT_op, expected_op;
	logic DUT_dest_write, expected_dest_write;
	logic DUT_has_freg, expected_has_freg;
	logic DUT_trigger_wfr, expected_trigger_wfr;
	logic DUT_strong_want_checkpoint, expected_strong_want_checkpoint;
	logic DUT_weak_want_checkpoint, expected_weak_want_checkpoint;

    // A operand
	corep::ar6_t DUT_A_ar6, expected_A_ar6;
	logic DUT_A_unneeded, expected_A_unneeded;
	logic DUT_A_is_zero, expected_A_is_zero;
	logic DUT_A_is_ret_ra, expected_A_is_ret_ra;

    // B operand
	corep::ar6_t DUT_B_ar6, expected_B_ar6;
	logic DUT_B_unneeded, expected_B_unneeded;
	logic DUT_B_is_zero, expected_B_is_zero;

    // C operand
	corep::ar5_t DUT_C_ar5, expected_C_ar5;

    // dest operand
	corep::ar6_t DUT_dest_ar6, expected_dest_ar6;
	logic DUT_dest_is_zero, expected_dest_is_zero;
	logic DUT_dest_is_link_ra, expected_dest_is_link_ra;

    // imm
	logic [19:0] DUT_imm20, expected_imm20;

    // ordering
	logic DUT_amo_is_double, expected_amo_is_double;
	logic DUT_mem_aq, expected_mem_aq;
	logic DUT_io_aq, expected_io_aq;
	logic DUT_mem_rl, expected_mem_rl;
	logic DUT_io_rl, expected_io_rl;

    // yielding
	logic DUT_instr_yield, expected_instr_yield;
	logic DUT_restart_valid, expected_restart_valid;
	logic [1:0] DUT_restart_pc38_offset, expected_restart_pc38_offset;

    // ----------------------------------------------------------------
    // DUT instantiation:

	decoder #(
	) DUT (

	    // environment info
		.env_exec_mode(tb_env_exec_mode),
		.env_trap_sfence(tb_env_trap_sfence),
		.env_trap_wfi(tb_env_trap_wfi),
		.env_trap_sret(tb_env_trap_sret),
		.env_menvconfig_FIOM(tb_env_menvconfig_FIOM),
		.env_senvconfig_FIOM(tb_env_senvconfig_FIOM),

	    // instr info
		.fetch4B(tb_fetch4B),
		.btb_hit(tb_btb_hit),
		.redirect_taken(tb_redirect_taken),
		.mid_instr_redirect(tb_mid_instr_redirect),

	    // FU select
		.is_alu_reg(DUT_is_alu_reg),
		.is_alu_imm(DUT_is_alu_imm),
		.is_bru(DUT_is_bru),
		.is_mdu(DUT_is_mdu),
		.is_fpu(DUT_is_fpu),
		.is_ldu(DUT_is_ldu),
		.is_store(DUT_is_store),
		.is_amo(DUT_is_amo),
		.is_fence(DUT_is_fence),
		.is_sysu(DUT_is_sysu),
		.is_illegal_instr(DUT_is_illegal_instr),

	    // op
		.op(DUT_op),
		.dest_write(DUT_dest_write),
		.has_freg(DUT_has_freg),
		.trigger_wfr(DUT_trigger_wfr),
		.strong_want_checkpoint(DUT_strong_want_checkpoint),
		.weak_want_checkpoint(DUT_weak_want_checkpoint),

	    // A operand
		.A_ar6(DUT_A_ar6),
		.A_unneeded(DUT_A_unneeded),
		.A_is_zero(DUT_A_is_zero),
		.A_is_ret_ra(DUT_A_is_ret_ra),

	    // B operand
		.B_ar6(DUT_B_ar6),
		.B_unneeded(DUT_B_unneeded),
		.B_is_zero(DUT_B_is_zero),

	    // C operand
		.C_ar5(DUT_C_ar5),

	    // dest operand
		.dest_ar6(DUT_dest_ar6),
		.dest_is_zero(DUT_dest_is_zero),
		.dest_is_link_ra(DUT_dest_is_link_ra),

	    // imm
		.imm20(DUT_imm20),

	    // ordering
		.amo_is_double(DUT_amo_is_double),
		.mem_aq(DUT_mem_aq),
		.io_aq(DUT_io_aq),
		.mem_rl(DUT_mem_rl),
		.io_rl(DUT_io_rl),

	    // yielding
		.instr_yield(DUT_instr_yield),
		.restart_valid(DUT_restart_valid),
		.restart_pc38_offset(DUT_restart_pc38_offset)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_is_alu_reg !== DUT_is_alu_reg) begin
			$display("TB ERROR: expected_is_alu_reg (%0d'h%h) != DUT_is_alu_reg (%0d'h%h)",
				$bits(expected_is_alu_reg), expected_is_alu_reg,
				$bits(DUT_is_alu_reg), DUT_is_alu_reg);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_alu_imm !== DUT_is_alu_imm) begin
			$display("TB ERROR: expected_is_alu_imm (%0d'h%h) != DUT_is_alu_imm (%0d'h%h)",
				$bits(expected_is_alu_imm), expected_is_alu_imm,
				$bits(DUT_is_alu_imm), DUT_is_alu_imm);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_bru !== DUT_is_bru) begin
			$display("TB ERROR: expected_is_bru (%0d'h%h) != DUT_is_bru (%0d'h%h)",
				$bits(expected_is_bru), expected_is_bru,
				$bits(DUT_is_bru), DUT_is_bru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_mdu !== DUT_is_mdu) begin
			$display("TB ERROR: expected_is_mdu (%0d'h%h) != DUT_is_mdu (%0d'h%h)",
				$bits(expected_is_mdu), expected_is_mdu,
				$bits(DUT_is_mdu), DUT_is_mdu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_fpu !== DUT_is_fpu) begin
			$display("TB ERROR: expected_is_fpu (%0d'h%h) != DUT_is_fpu (%0d'h%h)",
				$bits(expected_is_fpu), expected_is_fpu,
				$bits(DUT_is_fpu), DUT_is_fpu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_ldu !== DUT_is_ldu) begin
			$display("TB ERROR: expected_is_ldu (%0d'h%h) != DUT_is_ldu (%0d'h%h)",
				$bits(expected_is_ldu), expected_is_ldu,
				$bits(DUT_is_ldu), DUT_is_ldu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_store !== DUT_is_store) begin
			$display("TB ERROR: expected_is_store (%0d'h%h) != DUT_is_store (%0d'h%h)",
				$bits(expected_is_store), expected_is_store,
				$bits(DUT_is_store), DUT_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_amo !== DUT_is_amo) begin
			$display("TB ERROR: expected_is_amo (%0d'h%h) != DUT_is_amo (%0d'h%h)",
				$bits(expected_is_amo), expected_is_amo,
				$bits(DUT_is_amo), DUT_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_fence !== DUT_is_fence) begin
			$display("TB ERROR: expected_is_fence (%0d'h%h) != DUT_is_fence (%0d'h%h)",
				$bits(expected_is_fence), expected_is_fence,
				$bits(DUT_is_fence), DUT_is_fence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_sysu !== DUT_is_sysu) begin
			$display("TB ERROR: expected_is_sysu (%0d'h%h) != DUT_is_sysu (%0d'h%h)",
				$bits(expected_is_sysu), expected_is_sysu,
				$bits(DUT_is_sysu), DUT_is_sysu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_illegal_instr !== DUT_is_illegal_instr) begin
			$display("TB ERROR: expected_is_illegal_instr (%0d'h%h) != DUT_is_illegal_instr (%0d'h%h)",
				$bits(expected_is_illegal_instr), expected_is_illegal_instr,
				$bits(DUT_is_illegal_instr), DUT_is_illegal_instr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_op !== DUT_op) begin
			$display("TB ERROR: expected_op (%0d'h%h) != DUT_op (%0d'h%h)",
				$bits(expected_op), expected_op,
				$bits(DUT_op), DUT_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_write !== DUT_dest_write) begin
			$display("TB ERROR: expected_dest_write (%0d'h%h) != DUT_dest_write (%0d'h%h)",
				$bits(expected_dest_write), expected_dest_write,
				$bits(DUT_dest_write), DUT_dest_write);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_has_freg !== DUT_has_freg) begin
			$display("TB ERROR: expected_has_freg (%0d'h%h) != DUT_has_freg (%0d'h%h)",
				$bits(expected_has_freg), expected_has_freg,
				$bits(DUT_has_freg), DUT_has_freg);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_trigger_wfr !== DUT_trigger_wfr) begin
			$display("TB ERROR: expected_trigger_wfr (%0d'h%h) != DUT_trigger_wfr (%0d'h%h)",
				$bits(expected_trigger_wfr), expected_trigger_wfr,
				$bits(DUT_trigger_wfr), DUT_trigger_wfr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_strong_want_checkpoint !== DUT_strong_want_checkpoint) begin
			$display("TB ERROR: expected_strong_want_checkpoint (%0d'h%h) != DUT_strong_want_checkpoint (%0d'h%h)",
				$bits(expected_strong_want_checkpoint), expected_strong_want_checkpoint,
				$bits(DUT_strong_want_checkpoint), DUT_strong_want_checkpoint);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_weak_want_checkpoint !== DUT_weak_want_checkpoint) begin
			$display("TB ERROR: expected_weak_want_checkpoint (%0d'h%h) != DUT_weak_want_checkpoint (%0d'h%h)",
				$bits(expected_weak_want_checkpoint), expected_weak_want_checkpoint,
				$bits(DUT_weak_want_checkpoint), DUT_weak_want_checkpoint);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_ar6 !== DUT_A_ar6) begin
			$display("TB ERROR: expected_A_ar6 (%0d'h%h) != DUT_A_ar6 (%0d'h%h)",
				$bits(expected_A_ar6), expected_A_ar6,
				$bits(DUT_A_ar6), DUT_A_ar6);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_unneeded !== DUT_A_unneeded) begin
			$display("TB ERROR: expected_A_unneeded (%0d'h%h) != DUT_A_unneeded (%0d'h%h)",
				$bits(expected_A_unneeded), expected_A_unneeded,
				$bits(DUT_A_unneeded), DUT_A_unneeded);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_is_zero !== DUT_A_is_zero) begin
			$display("TB ERROR: expected_A_is_zero (%0d'h%h) != DUT_A_is_zero (%0d'h%h)",
				$bits(expected_A_is_zero), expected_A_is_zero,
				$bits(DUT_A_is_zero), DUT_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_is_ret_ra !== DUT_A_is_ret_ra) begin
			$display("TB ERROR: expected_A_is_ret_ra (%0d'h%h) != DUT_A_is_ret_ra (%0d'h%h)",
				$bits(expected_A_is_ret_ra), expected_A_is_ret_ra,
				$bits(DUT_A_is_ret_ra), DUT_A_is_ret_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_ar6 !== DUT_B_ar6) begin
			$display("TB ERROR: expected_B_ar6 (%0d'h%h) != DUT_B_ar6 (%0d'h%h)",
				$bits(expected_B_ar6), expected_B_ar6,
				$bits(DUT_B_ar6), DUT_B_ar6);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_unneeded !== DUT_B_unneeded) begin
			$display("TB ERROR: expected_B_unneeded (%0d'h%h) != DUT_B_unneeded (%0d'h%h)",
				$bits(expected_B_unneeded), expected_B_unneeded,
				$bits(DUT_B_unneeded), DUT_B_unneeded);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_is_zero !== DUT_B_is_zero) begin
			$display("TB ERROR: expected_B_is_zero (%0d'h%h) != DUT_B_is_zero (%0d'h%h)",
				$bits(expected_B_is_zero), expected_B_is_zero,
				$bits(DUT_B_is_zero), DUT_B_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_C_ar5 !== DUT_C_ar5) begin
			$display("TB ERROR: expected_C_ar5 (%0d'h%h) != DUT_C_ar5 (%0d'h%h)",
				$bits(expected_C_ar5), expected_C_ar5,
				$bits(DUT_C_ar5), DUT_C_ar5);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_ar6 !== DUT_dest_ar6) begin
			$display("TB ERROR: expected_dest_ar6 (%0d'h%h) != DUT_dest_ar6 (%0d'h%h)",
				$bits(expected_dest_ar6), expected_dest_ar6,
				$bits(DUT_dest_ar6), DUT_dest_ar6);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_is_zero !== DUT_dest_is_zero) begin
			$display("TB ERROR: expected_dest_is_zero (%0d'h%h) != DUT_dest_is_zero (%0d'h%h)",
				$bits(expected_dest_is_zero), expected_dest_is_zero,
				$bits(DUT_dest_is_zero), DUT_dest_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_is_link_ra !== DUT_dest_is_link_ra) begin
			$display("TB ERROR: expected_dest_is_link_ra (%0d'h%h) != DUT_dest_is_link_ra (%0d'h%h)",
				$bits(expected_dest_is_link_ra), expected_dest_is_link_ra,
				$bits(DUT_dest_is_link_ra), DUT_dest_is_link_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_imm20 !== DUT_imm20) begin
			$display("TB ERROR: expected_imm20 (%0d'h%h) != DUT_imm20 (%0d'h%h)",
				$bits(expected_imm20), expected_imm20,
				$bits(DUT_imm20), DUT_imm20);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_amo_is_double !== DUT_amo_is_double) begin
			$display("TB ERROR: expected_amo_is_double (%0d'h%h) != DUT_amo_is_double (%0d'h%h)",
				$bits(expected_amo_is_double), expected_amo_is_double,
				$bits(DUT_amo_is_double), DUT_amo_is_double);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_mem_aq !== DUT_mem_aq) begin
			$display("TB ERROR: expected_mem_aq (%0d'h%h) != DUT_mem_aq (%0d'h%h)",
				$bits(expected_mem_aq), expected_mem_aq,
				$bits(DUT_mem_aq), DUT_mem_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_io_aq !== DUT_io_aq) begin
			$display("TB ERROR: expected_io_aq (%0d'h%h) != DUT_io_aq (%0d'h%h)",
				$bits(expected_io_aq), expected_io_aq,
				$bits(DUT_io_aq), DUT_io_aq);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_mem_rl !== DUT_mem_rl) begin
			$display("TB ERROR: expected_mem_rl (%0d'h%h) != DUT_mem_rl (%0d'h%h)",
				$bits(expected_mem_rl), expected_mem_rl,
				$bits(DUT_mem_rl), DUT_mem_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_io_rl !== DUT_io_rl) begin
			$display("TB ERROR: expected_io_rl (%0d'h%h) != DUT_io_rl (%0d'h%h)",
				$bits(expected_io_rl), expected_io_rl,
				$bits(DUT_io_rl), DUT_io_rl);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_instr_yield !== DUT_instr_yield) begin
			$display("TB ERROR: expected_instr_yield (%0d'h%h) != DUT_instr_yield (%0d'h%h)",
				$bits(expected_instr_yield), expected_instr_yield,
				$bits(DUT_instr_yield), DUT_instr_yield);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_valid !== DUT_restart_valid) begin
			$display("TB ERROR: expected_restart_valid (%0d'h%h) != DUT_restart_valid (%0d'h%h)",
				$bits(expected_restart_valid), expected_restart_valid,
				$bits(DUT_restart_valid), DUT_restart_valid);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_pc38_offset !== DUT_restart_pc38_offset) begin
			$display("TB ERROR: expected_restart_pc38_offset (%0d'h%h) != DUT_restart_pc38_offset (%0d'h%h)",
				$bits(expected_restart_pc38_offset), expected_restart_pc38_offset,
				$bits(DUT_restart_pc38_offset), DUT_restart_pc38_offset);
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
	    // environment info
		tb_env_exec_mode = corep::EXEC_MODE_M;
		tb_env_trap_sfence = 1'b0;
		tb_env_trap_wfi = 1'b0;
		tb_env_trap_sret = 1'b0;
		tb_env_menvconfig_FIOM = 1'b0;
		tb_env_senvconfig_FIOM = 1'b0;
	    // instr info
		tb_fetch4B = 32'h0000_0000;
		tb_btb_hit = 1'b0;
		tb_redirect_taken = 1'b0;
		tb_mid_instr_redirect = 1'b0;
	    // FU select
	    // op
	    // A operand
	    // B operand
	    // C operand
	    // dest operand
	    // imm
	    // ordering
	    // yielding

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // environment info
	    // instr info
	    // FU select
		expected_is_alu_reg = 1'b0;
		expected_is_alu_imm = 1'b0;
		expected_is_bru = 1'b0;
		expected_is_mdu = 1'b0;
		expected_is_fpu = 1'b0;
		expected_is_ldu = 1'b0;
		expected_is_store = 1'b0;
		expected_is_amo = 1'b0;
		expected_is_fence = 1'b0;
		expected_is_sysu = 1'b0;
		expected_is_illegal_instr = 1'b1;
	    // op
		expected_op = instrp::ALU_ADD;
		expected_dest_write = 1'b0;
		expected_has_freg = 1'b0;
		expected_trigger_wfr = 1'b1;
		expected_strong_want_checkpoint = 1'b0;
		expected_weak_want_checkpoint = 1'b0;
	    // A operand
		expected_A_ar6 = {1'b0, 5'h02};
		expected_A_unneeded = 1'b1;
		expected_A_is_zero = 1'b0;
		expected_A_is_ret_ra = 1'b0;
	    // B operand
		expected_B_ar6 = {1'b0, 5'h08};
		expected_B_unneeded = 1'b1;
		expected_B_is_zero = 1'b0;
	    // C operand
		expected_C_ar5 = 5'h00;
	    // dest operand
		expected_dest_ar6 = {1'b0, 5'h08};
		expected_dest_is_zero = 1'b0;
		expected_dest_is_link_ra = 1'b0;
	    // imm
		expected_imm20 = 20'h00000;
	    // ordering
		expected_amo_is_double = 1'b0;
		expected_mem_aq = 1'b0;
		expected_io_aq = 1'b0;
		expected_mem_rl = 1'b0;
		expected_io_rl = 1'b0;
	    // yielding
		expected_instr_yield = 1'b1;
		expected_restart_valid = 1'b0;
		expected_restart_pc38_offset = 2'b00;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // environment info
		tb_env_exec_mode = corep::EXEC_MODE_M;
		tb_env_trap_sfence = 1'b0;
		tb_env_trap_wfi = 1'b0;
		tb_env_trap_sret = 1'b0;
		tb_env_menvconfig_FIOM = 1'b0;
		tb_env_senvconfig_FIOM = 1'b0;
	    // instr info
		tb_fetch4B = 32'h0000_0000;
		tb_btb_hit = 1'b0;
		tb_redirect_taken = 1'b0;
		tb_mid_instr_redirect = 1'b0;
	    // FU select
	    // op
	    // A operand
	    // B operand
	    // C operand
	    // dest operand
	    // imm
	    // ordering
	    // yielding

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // environment info
	    // instr info
	    // FU select
		expected_is_alu_reg = 1'b0;
		expected_is_alu_imm = 1'b0;
		expected_is_bru = 1'b0;
		expected_is_mdu = 1'b0;
		expected_is_fpu = 1'b0;
		expected_is_ldu = 1'b0;
		expected_is_store = 1'b0;
		expected_is_amo = 1'b0;
		expected_is_fence = 1'b0;
		expected_is_sysu = 1'b0;
		expected_is_illegal_instr = 1'b1;
	    // op
		expected_op = instrp::ALU_ADD;
		expected_dest_write = 1'b0;
		expected_has_freg = 1'b0;
		expected_trigger_wfr = 1'b1;
		expected_strong_want_checkpoint = 1'b0;
		expected_weak_want_checkpoint = 1'b0;
	    // A operand
		expected_A_ar6 = {1'b0, 5'h02};
		expected_A_unneeded = 1'b1;
		expected_A_is_zero = 1'b0;
		expected_A_is_ret_ra = 1'b0;
	    // B operand
		expected_B_ar6 = {1'b0, 5'h08};
		expected_B_unneeded = 1'b1;
		expected_B_is_zero = 1'b0;
	    // C operand
		expected_C_ar5 = 5'h00;
	    // dest operand
		expected_dest_ar6 = {1'b0, 5'h08};
		expected_dest_is_zero = 1'b0;
		expected_dest_is_link_ra = 1'b0;
	    // imm
		expected_imm20 = 20'h00000;
	    // ordering
		expected_amo_is_double = 1'b0;
		expected_mem_aq = 1'b0;
		expected_io_aq = 1'b0;
		expected_mem_rl = 1'b0;
		expected_io_rl = 1'b0;
	    // yielding
		expected_instr_yield = 1'b1;
		expected_restart_valid = 1'b0;
		expected_restart_pc38_offset = 2'b00;

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
	    // environment info
		tb_env_exec_mode = corep::EXEC_MODE_M;
		tb_env_trap_sfence = 1'b0;
		tb_env_trap_wfi = 1'b0;
		tb_env_trap_sret = 1'b0;
		tb_env_menvconfig_FIOM = 1'b0;
		tb_env_senvconfig_FIOM = 1'b0;
	    // instr info
		tb_fetch4B = 32'h0000_0000;
		tb_btb_hit = 1'b0;
		tb_redirect_taken = 1'b0;
		tb_mid_instr_redirect = 1'b0;
	    // FU select
	    // op
	    // A operand
	    // B operand
	    // C operand
	    // dest operand
	    // imm
	    // ordering
	    // yielding

		@(negedge CLK);

		// outputs:

	    // environment info
	    // instr info
	    // FU select
		expected_is_alu_reg = 1'b0;
		expected_is_alu_imm = 1'b0;
		expected_is_bru = 1'b0;
		expected_is_mdu = 1'b0;
		expected_is_fpu = 1'b0;
		expected_is_ldu = 1'b0;
		expected_is_store = 1'b0;
		expected_is_amo = 1'b0;
		expected_is_fence = 1'b0;
		expected_is_sysu = 1'b0;
		expected_is_illegal_instr = 1'b1;
	    // op
		expected_op = instrp::ALU_ADD;
		expected_dest_write = 1'b0;
		expected_has_freg = 1'b0;
		expected_trigger_wfr = 1'b1;
		expected_strong_want_checkpoint = 1'b0;
		expected_weak_want_checkpoint = 1'b0;
	    // A operand
		expected_A_ar6 = {1'b0, 5'h02};
		expected_A_unneeded = 1'b1;
		expected_A_is_zero = 1'b0;
		expected_A_is_ret_ra = 1'b0;
	    // B operand
		expected_B_ar6 = {1'b0, 5'h08};
		expected_B_unneeded = 1'b1;
		expected_B_is_zero = 1'b0;
	    // C operand
		expected_C_ar5 = 5'h00;
	    // dest operand
		expected_dest_ar6 = {1'b0, 5'h08};
		expected_dest_is_zero = 1'b0;
		expected_dest_is_link_ra = 1'b0;
	    // imm
		expected_imm20 = 20'h00000;
	    // ordering
		expected_amo_is_double = 1'b0;
		expected_mem_aq = 1'b0;
		expected_io_aq = 1'b0;
		expected_mem_rl = 1'b0;
		expected_io_rl = 1'b0;
	    // yielding
		expected_instr_yield = 1'b1;
		expected_restart_valid = 1'b0;
		expected_restart_pc38_offset = 2'b00;

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