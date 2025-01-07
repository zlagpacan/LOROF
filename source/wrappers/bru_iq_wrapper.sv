/*
    Filename: bru_iq_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around bru_iq module. 
    Spec: LOROF/spec/design/bru_iq.md
*/

`timescale 1ns/100ps

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_iq_wrapper (

    // seq
    input logic CLK,
    input logic nRST,


    // BRU op dispatch by entry
	input logic [3:0] next_dispatch_valid_by_entry,
	input logic [3:0][3:0] next_dispatch_op_by_entry,
	input logic [3:0][31:0] next_dispatch_PC_by_entry,
	input logic [3:0][31:0] next_dispatch_speculated_next_PC_by_entry,
	input logic [3:0][31:0] next_dispatch_imm_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_A_PR_by_entry,
	input logic [3:0] next_dispatch_A_unneeded_by_entry,
	input logic [3:0] next_dispatch_A_ready_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_B_PR_by_entry,
	input logic [3:0] next_dispatch_B_unneeded_by_entry,
	input logic [3:0] next_dispatch_B_ready_by_entry,
	input logic [3:0][LOG_PR_COUNT-1:0] next_dispatch_dest_PR_by_entry,
	input logic [3:0][LOG_ROB_ENTRIES-1:0] next_dispatch_ROB_index_by_entry,

    // BRU op dispatch feedback by entry
	output logic [3:0] last_dispatch_open_by_entry,

    // BRU pipeline feedback
	input logic next_pipeline_ready,

    // writeback bus by bank
	input logic [PRF_BANK_COUNT-1:0] next_WB_bus_valid_by_bank,
	input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] next_WB_bus_upper_PR_by_bank,

    // BRU op issue to BRU pipeline
	output logic last_issue_valid,
	output logic [3:0] last_issue_op,
	output logic [31:0] last_issue_PC,
	output logic [31:0] last_issue_speculated_next_PC,
	output logic [31:0] last_issue_imm,
	output logic last_issue_A_unneeded,
	output logic last_issue_A_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_A_bank,
	output logic last_issue_B_unneeded,
	output logic last_issue_B_forward,
	output logic [LOG_PRF_BANK_COUNT-1:0] last_issue_B_bank,
	output logic [LOG_PR_COUNT-1:0] last_issue_dest_PR,
	output logic [LOG_ROB_ENTRIES-1:0] last_issue_ROB_index,

    // reg read req to PRF
	output logic last_PRF_req_A_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_A_PR,
	output logic last_PRF_req_B_valid,
	output logic [LOG_PR_COUNT-1:0] last_PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Direct Module Connections:


    // BRU op dispatch by entry
	logic [3:0] dispatch_valid_by_entry;
	logic [3:0][3:0] dispatch_op_by_entry;
	logic [3:0][31:0] dispatch_PC_by_entry;
	logic [3:0][31:0] dispatch_speculated_next_PC_by_entry;
	logic [3:0][31:0] dispatch_imm_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_A_PR_by_entry;
	logic [3:0] dispatch_A_unneeded_by_entry;
	logic [3:0] dispatch_A_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_B_PR_by_entry;
	logic [3:0] dispatch_B_unneeded_by_entry;
	logic [3:0] dispatch_B_ready_by_entry;
	logic [3:0][LOG_PR_COUNT-1:0] dispatch_dest_PR_by_entry;
	logic [3:0][LOG_ROB_ENTRIES-1:0] dispatch_ROB_index_by_entry;

    // BRU op dispatch feedback by entry
	logic [3:0] dispatch_open_by_entry;

    // BRU pipeline feedback
	logic pipeline_ready;

    // writeback bus by bank
	logic [PRF_BANK_COUNT-1:0] WB_bus_valid_by_bank;
	logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;

    // BRU op issue to BRU pipeline
	logic issue_valid;
	logic [3:0] issue_op;
	logic [31:0] issue_PC;
	logic [31:0] issue_speculated_next_PC;
	logic [31:0] issue_imm;
	logic issue_A_unneeded;
	logic issue_A_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_A_bank;
	logic issue_B_unneeded;
	logic issue_B_forward;
	logic [LOG_PRF_BANK_COUNT-1:0] issue_B_bank;
	logic [LOG_PR_COUNT-1:0] issue_dest_PR;
	logic [LOG_ROB_ENTRIES-1:0] issue_ROB_index;

    // reg read req to PRF
	logic PRF_req_A_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_A_PR;
	logic PRF_req_B_valid;
	logic [LOG_PR_COUNT-1:0] PRF_req_B_PR;

    // ----------------------------------------------------------------
    // Module Instantiation:

    bru_iq WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin


		    // BRU op dispatch by entry
			dispatch_valid_by_entry <= 4'b0000;
			dispatch_op_by_entry <= 4'b0000;
			dispatch_PC_by_entry <= {32'h0, 32'h0, 32'h0, 32'h0};
			dispatch_speculated_next_PC_by_entry <= {32'h0, 32'h0, 32'h0, 32'h0};
			dispatch_imm_by_entry <= {32'h0, 32'h0, 32'h0, 32'h0};
			dispatch_A_PR_by_entry <= {7'h0, 7'h0, 7'h0, 7'h0};
			dispatch_A_unneeded_by_entry <= 4'b0000;
			dispatch_A_ready_by_entry <= 4'b0000;
			dispatch_B_PR_by_entry <= {7'h0, 7'h0, 7'h0, 7'h0};
			dispatch_B_unneeded_by_entry <= 4'b0000;
			dispatch_B_ready_by_entry <= 4'b0000;
			dispatch_dest_PR_by_entry <= {7'h0, 7'h0, 7'h0, 7'h0};
			dispatch_ROB_index_by_entry <= {7'h0, 7'h0, 7'h0, 7'h0};

		    // BRU op dispatch feedback by entry
			last_dispatch_open_by_entry <= 4'b1111;

		    // BRU pipeline feedback
			pipeline_ready <= 1'b0;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= 4'b0000;
			WB_bus_upper_PR_by_bank <= {5'h0, 5'h0, 5'h0, 5'h0};

		    // BRU op issue to BRU pipeline
			last_issue_valid <= 1'b0;
			last_issue_op <= 4'b0000;
			last_issue_PC <= 32'h0;
			last_issue_speculated_next_PC <= 32'h0;
			last_issue_imm <= 32'h0;
			last_issue_A_unneeded <= 1'b0;
			last_issue_A_forward <= 1'b0;
			last_issue_A_bank <= 2'h0;
			last_issue_B_unneeded <= 1'b0;
			last_issue_B_forward <= 1'b0;
			last_issue_B_bank <= 2'h0;
			last_issue_dest_PR <= 7'h0;
			last_issue_ROB_index <= 7'h0;

		    // reg read req to PRF
			last_PRF_req_A_valid <= 1'b0;
			last_PRF_req_A_PR <= 7'h0;
			last_PRF_req_B_valid <= 1'b0;
			last_PRF_req_B_PR <= 7'h0;
        end
        else begin


		    // BRU op dispatch by entry
			dispatch_valid_by_entry <= next_dispatch_valid_by_entry;
			dispatch_op_by_entry <= next_dispatch_op_by_entry;
			dispatch_PC_by_entry <= next_dispatch_PC_by_entry;
			dispatch_speculated_next_PC_by_entry <= next_dispatch_speculated_next_PC_by_entry;
			dispatch_imm_by_entry <= next_dispatch_imm_by_entry;
			dispatch_A_PR_by_entry <= next_dispatch_A_PR_by_entry;
			dispatch_A_unneeded_by_entry <= next_dispatch_A_unneeded_by_entry;
			dispatch_A_ready_by_entry <= next_dispatch_A_ready_by_entry;
			dispatch_B_PR_by_entry <= next_dispatch_B_PR_by_entry;
			dispatch_B_unneeded_by_entry <= next_dispatch_B_unneeded_by_entry;
			dispatch_B_ready_by_entry <= next_dispatch_B_ready_by_entry;
			dispatch_dest_PR_by_entry <= next_dispatch_dest_PR_by_entry;
			dispatch_ROB_index_by_entry <= next_dispatch_ROB_index_by_entry;

		    // BRU op dispatch feedback by entry
			last_dispatch_open_by_entry <= dispatch_open_by_entry;

		    // BRU pipeline feedback
			pipeline_ready <= next_pipeline_ready;

		    // writeback bus by bank
			WB_bus_valid_by_bank <= next_WB_bus_valid_by_bank;
			WB_bus_upper_PR_by_bank <= next_WB_bus_upper_PR_by_bank;

		    // BRU op issue to BRU pipeline
			last_issue_valid <= issue_valid;
			last_issue_op <= issue_op;
			last_issue_PC <= issue_PC;
			last_issue_speculated_next_PC <= issue_speculated_next_PC;
			last_issue_imm <= issue_imm;
			last_issue_A_unneeded <= issue_A_unneeded;
			last_issue_A_forward <= issue_A_forward;
			last_issue_A_bank <= issue_A_bank;
			last_issue_B_unneeded <= issue_B_unneeded;
			last_issue_B_forward <= issue_B_forward;
			last_issue_B_bank <= issue_B_bank;
			last_issue_dest_PR <= issue_dest_PR;
			last_issue_ROB_index <= issue_ROB_index;

		    // reg read req to PRF
			last_PRF_req_A_valid <= PRF_req_A_valid;
			last_PRF_req_A_PR <= PRF_req_A_PR;
			last_PRF_req_B_valid <= PRF_req_B_valid;
			last_PRF_req_B_PR <= PRF_req_B_PR;
        end
    end

endmodule