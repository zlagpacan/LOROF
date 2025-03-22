/*
    Filename: decoder_tb.sv
    Author: zlagpacan
    Description: Testbench for decoder module. 
    Spec: LOROF/spec/design/decoder.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module decoder_tb ();

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

    // input info
	logic tb_uncompressed;
	logic [31:0] tb_instr32;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_pred_info_chunk0;
	logic [BTB_PRED_INFO_WIDTH-1:0] tb_pred_info_chunk1;

    // FU select
	logic DUT_is_alu_reg, expected_is_alu_reg;
	logic DUT_is_alu_imm, expected_is_alu_imm;
	logic DUT_is_bru, expected_is_bru;
	logic DUT_is_mdu, expected_is_mdu;
	logic DUT_is_ldu, expected_is_ldu;
	logic DUT_is_store, expected_is_store;
	logic DUT_is_amo, expected_is_amo;
	logic DUT_is_fence, expected_is_fence;
	logic DUT_is_sys, expected_is_sys;
	logic DUT_is_illegal_instr, expected_is_illegal_instr;

    // op
	logic [3:0] DUT_op, expected_op;
	logic DUT_is_reg_write, expected_is_reg_write;

    // A operand
	logic [4:0] DUT_A_AR, expected_A_AR;
	logic DUT_A_unneeded, expected_A_unneeded;
	logic DUT_A_is_zero, expected_A_is_zero;
	logic DUT_A_is_ret_ra, expected_A_is_ret_ra;

    // B operand
	logic [4:0] DUT_B_AR, expected_B_AR;
	logic DUT_B_unneeded, expected_B_unneeded;
	logic DUT_B_is_zero, expected_B_is_zero;

    // dest operand
	logic [4:0] DUT_dest_AR, expected_dest_AR;
	logic DUT_dest_is_zero, expected_dest_is_zero;
	logic DUT_dest_is_link_ra, expected_dest_is_link_ra;

    // imm
	logic [19:0] DUT_imm20, expected_imm20;

    // pred info out
	logic [BTB_PRED_INFO_WIDTH-1:0] DUT_pred_info_out, expected_pred_info_out;
	logic DUT_missing_pred, expected_missing_pred;

    // ordering
	logic DUT_flush_fetch, expected_flush_fetch;
	logic DUT_stall_mem_read, expected_stall_mem_read;
	logic DUT_stall_mem_write, expected_stall_mem_write;
	logic DUT_wait_write_buffer, expected_wait_write_buffer;

    // faults
	logic DUT_instr_yield, expected_instr_yield;
	logic DUT_non_branch_notif_chunk0, expected_non_branch_notif_chunk0;
	logic DUT_non_branch_notif_chunk1, expected_non_branch_notif_chunk1;
	logic DUT_restart_on_chunk0, expected_restart_on_chunk0;
	logic DUT_restart_after_chunk0, expected_restart_after_chunk0;
	logic DUT_restart_after_chunk1, expected_restart_after_chunk1;
	logic DUT_unrecoverable_fault, expected_unrecoverable_fault;

    // ----------------------------------------------------------------
    // DUT instantiation:

	decoder DUT (

	    // input info
		.uncompressed(tb_uncompressed),
		.instr32(tb_instr32),
		.pred_info_chunk0(tb_pred_info_chunk0),
		.pred_info_chunk1(tb_pred_info_chunk1),

	    // FU select
		.is_alu_reg(DUT_is_alu_reg),
		.is_alu_imm(DUT_is_alu_imm),
		.is_bru(DUT_is_bru),
		.is_mdu(DUT_is_mdu),
		.is_ldu(DUT_is_ldu),
		.is_store(DUT_is_store),
		.is_amo(DUT_is_amo),
		.is_fence(DUT_is_fence),
		.is_sys(DUT_is_sys),
		.is_illegal_instr(DUT_is_illegal_instr),

	    // op
		.op(DUT_op),
		.is_reg_write(DUT_is_reg_write),

	    // A operand
		.A_AR(DUT_A_AR),
		.A_unneeded(DUT_A_unneeded),
		.A_is_zero(DUT_A_is_zero),
		.A_is_ret_ra(DUT_A_is_ret_ra),

	    // B operand
		.B_AR(DUT_B_AR),
		.B_unneeded(DUT_B_unneeded),
		.B_is_zero(DUT_B_is_zero),

	    // dest operand
		.dest_AR(DUT_dest_AR),
		.dest_is_zero(DUT_dest_is_zero),
		.dest_is_link_ra(DUT_dest_is_link_ra),

	    // imm
		.imm20(DUT_imm20),

	    // pred info out
		.pred_info_out(DUT_pred_info_out),
		.missing_pred(DUT_missing_pred),

	    // ordering
		.flush_fetch(DUT_flush_fetch),
		.stall_mem_read(DUT_stall_mem_read),
		.stall_mem_write(DUT_stall_mem_write),
		.wait_write_buffer(DUT_wait_write_buffer),

	    // faults
		.instr_yield(DUT_instr_yield),
		.non_branch_notif_chunk0(DUT_non_branch_notif_chunk0),
		.non_branch_notif_chunk1(DUT_non_branch_notif_chunk1),
		.restart_on_chunk0(DUT_restart_on_chunk0),
		.restart_after_chunk0(DUT_restart_after_chunk0),
		.restart_after_chunk1(DUT_restart_after_chunk1),
		.unrecoverable_fault(DUT_unrecoverable_fault)
	);

    // ----------------------------------------------------------------
    // tasks:

    task check_outputs();
    begin
		if (expected_is_alu_reg !== DUT_is_alu_reg) begin
			$display("TB ERROR: expected_is_alu_reg (%h) != DUT_is_alu_reg (%h)",
				expected_is_alu_reg, DUT_is_alu_reg);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_alu_imm !== DUT_is_alu_imm) begin
			$display("TB ERROR: expected_is_alu_imm (%h) != DUT_is_alu_imm (%h)",
				expected_is_alu_imm, DUT_is_alu_imm);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_bru !== DUT_is_bru) begin
			$display("TB ERROR: expected_is_bru (%h) != DUT_is_bru (%h)",
				expected_is_bru, DUT_is_bru);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_mdu !== DUT_is_mdu) begin
			$display("TB ERROR: expected_is_mdu (%h) != DUT_is_mdu (%h)",
				expected_is_mdu, DUT_is_mdu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_ldu !== DUT_is_ldu) begin
			$display("TB ERROR: expected_is_ldu (%h) != DUT_is_ldu (%h)",
				expected_is_ldu, DUT_is_ldu);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_store !== DUT_is_store) begin
			$display("TB ERROR: expected_is_store (%h) != DUT_is_store (%h)",
				expected_is_store, DUT_is_store);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_amo !== DUT_is_amo) begin
			$display("TB ERROR: expected_is_amo (%h) != DUT_is_amo (%h)",
				expected_is_amo, DUT_is_amo);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_fence !== DUT_is_fence) begin
			$display("TB ERROR: expected_is_fence (%h) != DUT_is_fence (%h)",
				expected_is_fence, DUT_is_fence);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_sys !== DUT_is_sys) begin
			$display("TB ERROR: expected_is_sys (%h) != DUT_is_sys (%h)",
				expected_is_sys, DUT_is_sys);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_illegal_instr !== DUT_is_illegal_instr) begin
			$display("TB ERROR: expected_is_illegal_instr (%h) != DUT_is_illegal_instr (%h)",
				expected_is_illegal_instr, DUT_is_illegal_instr);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_op !== DUT_op) begin
			$display("TB ERROR: expected_op (%h) != DUT_op (%h)",
				expected_op, DUT_op);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_is_reg_write !== DUT_is_reg_write) begin
			$display("TB ERROR: expected_is_reg_write (%h) != DUT_is_reg_write (%h)",
				expected_is_reg_write, DUT_is_reg_write);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_AR !== DUT_A_AR) begin
			$display("TB ERROR: expected_A_AR (%h) != DUT_A_AR (%h)",
				expected_A_AR, DUT_A_AR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_unneeded !== DUT_A_unneeded) begin
			$display("TB ERROR: expected_A_unneeded (%h) != DUT_A_unneeded (%h)",
				expected_A_unneeded, DUT_A_unneeded);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_is_zero !== DUT_A_is_zero) begin
			$display("TB ERROR: expected_A_is_zero (%h) != DUT_A_is_zero (%h)",
				expected_A_is_zero, DUT_A_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_A_is_ret_ra !== DUT_A_is_ret_ra) begin
			$display("TB ERROR: expected_A_is_ret_ra (%h) != DUT_A_is_ret_ra (%h)",
				expected_A_is_ret_ra, DUT_A_is_ret_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_AR !== DUT_B_AR) begin
			$display("TB ERROR: expected_B_AR (%h) != DUT_B_AR (%h)",
				expected_B_AR, DUT_B_AR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_unneeded !== DUT_B_unneeded) begin
			$display("TB ERROR: expected_B_unneeded (%h) != DUT_B_unneeded (%h)",
				expected_B_unneeded, DUT_B_unneeded);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_B_is_zero !== DUT_B_is_zero) begin
			$display("TB ERROR: expected_B_is_zero (%h) != DUT_B_is_zero (%h)",
				expected_B_is_zero, DUT_B_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_AR !== DUT_dest_AR) begin
			$display("TB ERROR: expected_dest_AR (%h) != DUT_dest_AR (%h)",
				expected_dest_AR, DUT_dest_AR);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_is_zero !== DUT_dest_is_zero) begin
			$display("TB ERROR: expected_dest_is_zero (%h) != DUT_dest_is_zero (%h)",
				expected_dest_is_zero, DUT_dest_is_zero);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_dest_is_link_ra !== DUT_dest_is_link_ra) begin
			$display("TB ERROR: expected_dest_is_link_ra (%h) != DUT_dest_is_link_ra (%h)",
				expected_dest_is_link_ra, DUT_dest_is_link_ra);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_imm20 !== DUT_imm20) begin
			$display("TB ERROR: expected_imm20 (%h) != DUT_imm20 (%h)",
				expected_imm20, DUT_imm20);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_pred_info_out !== DUT_pred_info_out) begin
			$display("TB ERROR: expected_pred_info_out (%h) != DUT_pred_info_out (%h)",
				expected_pred_info_out, DUT_pred_info_out);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_missing_pred !== DUT_missing_pred) begin
			$display("TB ERROR: expected_missing_pred (%h) != DUT_missing_pred (%h)",
				expected_missing_pred, DUT_missing_pred);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_flush_fetch !== DUT_flush_fetch) begin
			$display("TB ERROR: expected_flush_fetch (%h) != DUT_flush_fetch (%h)",
				expected_flush_fetch, DUT_flush_fetch);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stall_mem_read !== DUT_stall_mem_read) begin
			$display("TB ERROR: expected_stall_mem_read (%h) != DUT_stall_mem_read (%h)",
				expected_stall_mem_read, DUT_stall_mem_read);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_stall_mem_write !== DUT_stall_mem_write) begin
			$display("TB ERROR: expected_stall_mem_write (%h) != DUT_stall_mem_write (%h)",
				expected_stall_mem_write, DUT_stall_mem_write);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_wait_write_buffer !== DUT_wait_write_buffer) begin
			$display("TB ERROR: expected_wait_write_buffer (%h) != DUT_wait_write_buffer (%h)",
				expected_wait_write_buffer, DUT_wait_write_buffer);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_instr_yield !== DUT_instr_yield) begin
			$display("TB ERROR: expected_instr_yield (%h) != DUT_instr_yield (%h)",
				expected_instr_yield, DUT_instr_yield);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_non_branch_notif_chunk0 !== DUT_non_branch_notif_chunk0) begin
			$display("TB ERROR: expected_non_branch_notif_chunk0 (%h) != DUT_non_branch_notif_chunk0 (%h)",
				expected_non_branch_notif_chunk0, DUT_non_branch_notif_chunk0);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_non_branch_notif_chunk1 !== DUT_non_branch_notif_chunk1) begin
			$display("TB ERROR: expected_non_branch_notif_chunk1 (%h) != DUT_non_branch_notif_chunk1 (%h)",
				expected_non_branch_notif_chunk1, DUT_non_branch_notif_chunk1);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_on_chunk0 !== DUT_restart_on_chunk0) begin
			$display("TB ERROR: expected_restart_on_chunk0 (%h) != DUT_restart_on_chunk0 (%h)",
				expected_restart_on_chunk0, DUT_restart_on_chunk0);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_after_chunk0 !== DUT_restart_after_chunk0) begin
			$display("TB ERROR: expected_restart_after_chunk0 (%h) != DUT_restart_after_chunk0 (%h)",
				expected_restart_after_chunk0, DUT_restart_after_chunk0);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_restart_after_chunk1 !== DUT_restart_after_chunk1) begin
			$display("TB ERROR: expected_restart_after_chunk1 (%h) != DUT_restart_after_chunk1 (%h)",
				expected_restart_after_chunk1, DUT_restart_after_chunk1);
			num_errors++;
			tb_error = 1'b1;
		end

		if (expected_unrecoverable_fault !== DUT_unrecoverable_fault) begin
			$display("TB ERROR: expected_unrecoverable_fault (%h) != DUT_unrecoverable_fault (%h)",
				expected_unrecoverable_fault, DUT_unrecoverable_fault);
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
	    // input info
		tb_uncompressed = 1'b0;
		tb_instr32 = 32'h0;
		tb_pred_info_chunk0 = 8'h0;
		tb_pred_info_chunk1 = 8'h0;
	    // FU select
	    // op
	    // A operand
	    // B operand
	    // dest operand
	    // imm
	    // pred info out
	    // ordering
	    // faults

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // input info
	    // FU select
		expected_is_alu_reg = 1'b0;
		expected_is_alu_imm = 1'b0;
		expected_is_bru = 1'b0;
		expected_is_mdu = 1'b0;
		expected_is_ldu = 1'b0;
		expected_is_store = 1'b0;
		expected_is_amo = 1'b0;
		expected_is_fence = 1'b0;
		expected_is_sys = 1'b0;
		expected_is_illegal_instr = 1'b1;
	    // op
		expected_op = 4'h0;
		expected_is_reg_write = 1'b0;
	    // A operand
		expected_A_AR = 5'h2;
		expected_A_unneeded = 1'b1;
		expected_A_is_zero = 1'b0;
		expected_A_is_ret_ra = 1'b0;
	    // B operand
		expected_B_AR = 5'h8;
		expected_B_unneeded = 1'b1;
		expected_B_is_zero = 1'b0;
	    // dest operand
		expected_dest_AR = 5'h8;
		expected_dest_is_zero = 1'b0;
		expected_dest_is_link_ra = 1'b0;
	    // imm
		expected_imm20 = 20'h0;
	    // pred info out
		expected_pred_info_out = 8'h0;
		expected_missing_pred = 1'b0;
	    // ordering
		expected_flush_fetch = 1'b0;
		expected_stall_mem_read = 1'b0;
		expected_stall_mem_write = 1'b0;
		expected_wait_write_buffer = 1'b0;
	    // faults
		expected_instr_yield = 1'b1;
		expected_non_branch_notif_chunk0 = 1'b0;
		expected_non_branch_notif_chunk1 = 1'b0;
		expected_restart_on_chunk0 = 1'b0;
		expected_restart_after_chunk0 = 1'b0;
		expected_restart_after_chunk1 = 1'b0;
		expected_unrecoverable_fault = 1'b0;

		check_outputs();

        // inputs:
        sub_test_case = "deassert reset";
        $display("\t- sub_test: %s", sub_test_case);

		// reset
		nRST = 1'b1;
	    // input info
		tb_uncompressed = 1'b0;
		tb_instr32 = 32'h0;
		tb_pred_info_chunk0 = 8'h0;
		tb_pred_info_chunk1 = 8'h0;
	    // FU select
	    // op
	    // A operand
	    // B operand
	    // dest operand
	    // imm
	    // pred info out
	    // ordering
	    // faults

		@(posedge CLK); #(PERIOD/10);

		// outputs:

	    // input info
	    // FU select
		expected_is_alu_reg = 1'b0;
		expected_is_alu_imm = 1'b0;
		expected_is_bru = 1'b0;
		expected_is_mdu = 1'b0;
		expected_is_ldu = 1'b0;
		expected_is_store = 1'b0;
		expected_is_amo = 1'b0;
		expected_is_fence = 1'b0;
		expected_is_sys = 1'b0;
		expected_is_illegal_instr = 1'b1;
	    // op
		expected_op = 4'h0;
		expected_is_reg_write = 1'b0;
	    // A operand
		expected_A_AR = 5'h2;
		expected_A_unneeded = 1'b1;
		expected_A_is_zero = 1'b0;
		expected_A_is_ret_ra = 1'b0;
	    // B operand
		expected_B_AR = 5'h8;
		expected_B_unneeded = 1'b1;
		expected_B_is_zero = 1'b0;
	    // dest operand
		expected_dest_AR = 5'h8;
		expected_dest_is_zero = 1'b0;
		expected_dest_is_link_ra = 1'b0;
	    // imm
		expected_imm20 = 20'h0;
	    // pred info out
		expected_pred_info_out = 8'h0;
		expected_missing_pred = 1'b0;
	    // ordering
		expected_flush_fetch = 1'b0;
		expected_stall_mem_read = 1'b0;
		expected_stall_mem_write = 1'b0;
		expected_wait_write_buffer = 1'b0;
	    // faults
		expected_instr_yield = 1'b1;
		expected_non_branch_notif_chunk0 = 1'b0;
		expected_non_branch_notif_chunk1 = 1'b0;
		expected_restart_on_chunk0 = 1'b0;
		expected_restart_after_chunk0 = 1'b0;
		expected_restart_after_chunk1 = 1'b0;
		expected_unrecoverable_fault = 1'b0;

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
	    // input info
		tb_uncompressed = 1'b0;
		tb_instr32 = 32'h0;
		tb_pred_info_chunk0 = 8'h0;
		tb_pred_info_chunk1 = 8'h0;
	    // FU select
	    // op
	    // A operand
	    // B operand
	    // dest operand
	    // imm
	    // pred info out
	    // ordering
	    // faults

		@(negedge CLK);

		// outputs:

	    // input info
	    // FU select
		expected_is_alu_reg = 1'b0;
		expected_is_alu_imm = 1'b0;
		expected_is_bru = 1'b0;
		expected_is_mdu = 1'b0;
		expected_is_ldu = 1'b0;
		expected_is_store = 1'b0;
		expected_is_amo = 1'b0;
		expected_is_fence = 1'b0;
		expected_is_sys = 1'b0;
		expected_is_illegal_instr = 1'b1;
	    // op
		expected_op = 4'h0;
		expected_is_reg_write = 1'b0;
	    // A operand
		expected_A_AR = 5'h2;
		expected_A_unneeded = 1'b1;
		expected_A_is_zero = 1'b0;
		expected_A_is_ret_ra = 1'b0;
	    // B operand
		expected_B_AR = 5'h8;
		expected_B_unneeded = 1'b1;
		expected_B_is_zero = 1'b0;
	    // dest operand
		expected_dest_AR = 5'h8;
		expected_dest_is_zero = 1'b0;
		expected_dest_is_link_ra = 1'b0;
	    // imm
		expected_imm20 = 20'h0;
	    // pred info out
		expected_pred_info_out = 8'h0;
		expected_missing_pred = 1'b0;
	    // ordering
		expected_flush_fetch = 1'b0;
		expected_stall_mem_read = 1'b0;
		expected_stall_mem_write = 1'b0;
		expected_wait_write_buffer = 1'b0;
	    // faults
		expected_instr_yield = 1'b1;
		expected_non_branch_notif_chunk0 = 1'b0;
		expected_non_branch_notif_chunk1 = 1'b0;
		expected_restart_on_chunk0 = 1'b0;
		expected_restart_after_chunk0 = 1'b0;
		expected_restart_after_chunk1 = 1'b0;
		expected_unrecoverable_fault = 1'b0;

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