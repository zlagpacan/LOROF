/*
    Filename: bru_iq.sv
    Author: zlagpacan
    Description: RTL for Branch Resolution Unit Issue Queue
    Spec: LOROF/spec/design/bru_iq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_iq #(
    parameter BRU_IQ_ENTRIES = 6
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
    input logic                             iq_enq_valid,
    input logic [3:0]                       iq_enq_op,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   iq_enq_pred_info,
    input logic                             iq_enq_pred_lru,
    input logic                             iq_enq_is_link_ra,
    input logic                             iq_enq_is_ret_ra,
    input logic [31:0]                      iq_enq_PC,
    input logic [31:0]                      iq_enq_pred_PC,
    input logic [19:0]                      iq_enq_imm20,
    input logic [LOG_PR_COUNT-1:0]          iq_enq_A_PR,
    input logic                             iq_enq_A_ready,
    input logic                             iq_enq_A_unneeded_or_is_zero,
    input logic [LOG_PR_COUNT-1:0]          iq_enq_B_PR,
    input logic                             iq_enq_B_ready,
    input logic                             iq_enq_B_unneeded_or_is_zero,
    input logic [LOG_PR_COUNT-1:0]          iq_enq_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       iq_enq_ROB_index,

    // issue queue enqueue feedback
    output logic                        iq_enq_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // pipeline issue
    output logic                            issue_valid,
    output logic [3:0]                      issue_op,
    output logic [BTB_PRED_INFO_WIDTH-1:0]  issue_pred_info,
    output logic                            issue_pred_lru,
    output logic                            issue_is_link_ra,
    output logic                            issue_is_ret_ra,
    output logic [31:0]                     issue_PC,
    output logic [31:0]                     issue_pred_PC,
    output logic [19:0]                     issue_imm20,
    output logic                            issue_A_forward,
    output logic                            issue_A_unneeded_or_is_zero,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_A_bank,
    output logic                            issue_B_forward,
    output logic                            issue_B_unneeded_or_is_zero,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_B_bank,
    output logic [LOG_PR_COUNT-1:0]         issue_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]      issue_ROB_index,

    // pipeline feedback
    input logic                             issue_ready,

    // reg read req to PRF
    output logic                        PRF_req_A_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_A_PR,
    output logic                        PRF_req_B_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Signals:

    // IQ entries
    logic [BRU_IQ_ENTRIES-1:0]                              valid_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][3:0]                         op_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][BTB_PRED_INFO_WIDTH-1:0]     pred_info_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              pred_lru_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              is_link_ra_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              is_ret_ra_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][31:0]                        PC_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][31:0]                        pred_PC_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][19:0]                        imm20_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            A_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              A_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              A_unneeded_or_is_zero_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            B_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              B_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              B_unneeded_or_is_zero_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            dest_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]         ROB_index_by_entry;

    // issue logic helper signals
    logic [BRU_IQ_ENTRIES-1:0] A_forward_by_entry;
    logic [BRU_IQ_ENTRIES-1:0] B_forward_by_entry;

    logic [BRU_IQ_ENTRIES-1:0] issue_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0] issue_one_hot_by_entry;
    logic [BRU_IQ_ENTRIES-1:0] issue_mask;

    // incoming dispatch crossbar by entry
    logic [BRU_IQ_ENTRIES-1:0] dispatch_valid_by_entry;

    // incoming dispatch reg mask
    logic [BRU_IQ_ENTRIES-1:0] dispatch_open_mask;
    logic [BRU_IQ_ENTRIES-1:0] dispatch_pe_one_hot;
    logic [BRU_IQ_ENTRIES-1:0] dispatch_one_hot;

    // ----------------------------------------------------------------
    // Issue Logic:

    // forwarding check
    always_comb begin
        for (int i = 0; i < BRU_IQ_ENTRIES; i++) begin
            A_forward_by_entry[i] = (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            B_forward_by_entry[i] = (B_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
        end
    end

    // issue:
    
    // ready check
    assign issue_ready_by_entry = 
        {BRU_IQ_ENTRIES{issue_ready}}
        & valid_by_entry
        & (A_ready_by_entry | A_forward_by_entry | A_unneeded_or_is_zero_by_entry)
        & (B_ready_by_entry | B_forward_by_entry | B_unneeded_or_is_zero_by_entry);

    // pe
    pe_lsb #(.WIDTH(BRU_IQ_ENTRIES)) ISSUE_PE_LSB (
        .req_vec(issue_ready_by_entry),
        .ack_one_hot(issue_one_hot_by_entry),
        .ack_mask(issue_mask)
    );

    // mux
    always_comb begin
        
        // issue automatically valid if an entry ready
        issue_valid = |issue_ready_by_entry;

        // one-hot mux over entries for final issue:
        issue_op = '0;
        issue_pred_info = '0;
        issue_pred_lru = '0;
        issue_is_link_ra = '0;
        issue_is_ret_ra = '0;
        issue_PC = '0;
        issue_pred_PC = '0;
        issue_imm20 = '0;
        issue_A_forward = '0;
        issue_A_unneeded_or_is_zero = '0;
        issue_A_bank = '0;
        issue_B_forward = '0;
        issue_B_unneeded_or_is_zero = '0;
        issue_B_bank = '0;
        issue_dest_PR = '0;
        issue_ROB_index = '0;

        PRF_req_A_valid = '0;
        PRF_req_A_PR = '0;
        PRF_req_B_valid = '0;
        PRF_req_B_PR = '0;

        for (int entry = 0; entry < BRU_IQ_ENTRIES; entry++) begin

            if (issue_one_hot_by_entry[entry]) begin

                issue_op |= op_by_entry[entry];
                issue_pred_info |= pred_info_by_entry[entry];
                issue_pred_lru |= pred_lru_by_entry[entry];
                issue_is_link_ra |= is_link_ra_by_entry[entry];
                issue_is_ret_ra |= is_ret_ra_by_entry[entry];
                issue_PC |= PC_by_entry[entry];
                issue_pred_PC |= pred_PC_by_entry[entry];
                issue_imm20 |= imm20_by_entry[entry];
                issue_A_forward |= A_forward_by_entry[entry];
                issue_A_unneeded_or_is_zero |= A_unneeded_or_is_zero_by_entry[entry];
                issue_A_bank |= A_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0];
                issue_B_forward |= B_forward_by_entry[entry];
                issue_B_unneeded_or_is_zero |= B_unneeded_or_is_zero_by_entry[entry];
                issue_B_bank |= B_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0];
                issue_dest_PR |= dest_PR_by_entry[entry];
                issue_ROB_index |= ROB_index_by_entry[entry];

                PRF_req_A_valid |= ~A_forward_by_entry[entry] & ~A_unneeded_or_is_zero_by_entry[entry];
                PRF_req_A_PR |= A_PR_by_entry[entry];
                PRF_req_B_valid |= ~B_forward_by_entry[entry] & ~B_unneeded_or_is_zero_by_entry[entry];
                PRF_req_B_PR |= B_PR_by_entry[entry];
            end
        end
    end

    // ----------------------------------------------------------------
    // Dispatch Logic:

    assign dispatch_open_mask = ~valid_by_entry;
    pe_lsb #(.WIDTH(BRU_IQ_ENTRIES)) DISPATCH_PE_LSB (
        .req_vec(dispatch_open_mask),
        .ack_one_hot(dispatch_pe_one_hot),
        .ack_mask() // unused
    );
    assign dispatch_one_hot = dispatch_pe_one_hot & {BRU_IQ_ENTRIES{iq_enq_valid}};

    // give dispatch feedback
    assign iq_enq_ready = |dispatch_open_mask;

    // route PE'd dispatch to entries
    assign dispatch_valid_by_entry = dispatch_one_hot;

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_by_entry <= '0;
            op_by_entry <= '0;
            pred_info_by_entry <= '0;
            pred_lru_by_entry <= '0;
            is_link_ra_by_entry <= '0;
            is_ret_ra_by_entry <= '0;
            PC_by_entry <= '0;
            pred_PC_by_entry <= '0;
            imm20_by_entry <= '0;
            A_PR_by_entry <= '0;
            A_ready_by_entry <= '0;
            A_unneeded_or_is_zero_by_entry <= '0;
            B_PR_by_entry <= '0;
            B_ready_by_entry <= '0;
            B_unneeded_or_is_zero_by_entry <= '0;
            dest_PR_by_entry <= '0;
            ROB_index_by_entry <= '0;
        end
        else begin

            // --------------------------------------------------------
            // highest entry only takes self:
                // self: [BRU_IQ_ENTRIES-1]

            // check take above
            if (issue_mask[BRU_IQ_ENTRIES-1]) begin
                valid_by_entry[BRU_IQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[BRU_IQ_ENTRIES-1]) begin
                    valid_by_entry[BRU_IQ_ENTRIES-1] <= 1'b1;
                    op_by_entry[BRU_IQ_ENTRIES-1] <= op_by_entry[BRU_IQ_ENTRIES-1];
                    pred_info_by_entry[BRU_IQ_ENTRIES-1] <= pred_info_by_entry[BRU_IQ_ENTRIES-1];
                    pred_lru_by_entry[BRU_IQ_ENTRIES-1] <= pred_lru_by_entry[BRU_IQ_ENTRIES-1];
                    is_link_ra_by_entry[BRU_IQ_ENTRIES-1] <= is_link_ra_by_entry[BRU_IQ_ENTRIES-1];
                    is_ret_ra_by_entry[BRU_IQ_ENTRIES-1] <= is_ret_ra_by_entry[BRU_IQ_ENTRIES-1];
                    PC_by_entry[BRU_IQ_ENTRIES-1] <= PC_by_entry[BRU_IQ_ENTRIES-1];
                    pred_PC_by_entry[BRU_IQ_ENTRIES-1] <= pred_PC_by_entry[BRU_IQ_ENTRIES-1];
                    imm20_by_entry[BRU_IQ_ENTRIES-1] <= imm20_by_entry[BRU_IQ_ENTRIES-1];
                    A_PR_by_entry[BRU_IQ_ENTRIES-1] <= A_PR_by_entry[BRU_IQ_ENTRIES-1];
                    A_ready_by_entry[BRU_IQ_ENTRIES-1] <= A_ready_by_entry[BRU_IQ_ENTRIES-1] | A_forward_by_entry[BRU_IQ_ENTRIES-1];
                    A_unneeded_or_is_zero_by_entry[BRU_IQ_ENTRIES-1] <= A_unneeded_or_is_zero_by_entry[BRU_IQ_ENTRIES-1];
                    B_PR_by_entry[BRU_IQ_ENTRIES-1] <= B_PR_by_entry[BRU_IQ_ENTRIES-1];
                    B_ready_by_entry[BRU_IQ_ENTRIES-1] <= B_ready_by_entry[BRU_IQ_ENTRIES-1] | B_forward_by_entry[BRU_IQ_ENTRIES-1];
                    B_unneeded_or_is_zero_by_entry[BRU_IQ_ENTRIES-1] <= B_unneeded_or_is_zero_by_entry[BRU_IQ_ENTRIES-1];
                    dest_PR_by_entry[BRU_IQ_ENTRIES-1] <= dest_PR_by_entry[BRU_IQ_ENTRIES-1];
                    ROB_index_by_entry[BRU_IQ_ENTRIES-1] <= ROB_index_by_entry[BRU_IQ_ENTRIES-1];
                end

                // take self dispatch
                else begin
                    valid_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_valid_by_entry[BRU_IQ_ENTRIES-1];
                    op_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_op;
                    pred_info_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_pred_info;
                    pred_lru_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_pred_lru;
                    is_link_ra_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_is_link_ra;
                    is_ret_ra_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_is_ret_ra;
                    PC_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_PC;
                    pred_PC_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_pred_PC;
                    imm20_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_imm20;
                    A_PR_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_A_PR;
                    A_ready_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_A_ready;
                    A_unneeded_or_is_zero_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_A_unneeded_or_is_zero;
                    B_PR_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_B_PR;
                    B_ready_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_B_ready;
                    B_unneeded_or_is_zero_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_B_unneeded_or_is_zero;
                    dest_PR_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_dest_PR;
                    ROB_index_by_entry[BRU_IQ_ENTRIES-1] <= iq_enq_ROB_index;
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
            for (int i = 0; i <= BRU_IQ_ENTRIES-2; i++) begin

                // check take above
                if (issue_mask[i]) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= 1'b1;
                        op_by_entry[i] <= op_by_entry[i+1];
                        pred_info_by_entry[i] <= pred_info_by_entry[i+1];
                        pred_lru_by_entry[i] <= pred_lru_by_entry[i+1];
                        is_link_ra_by_entry[i] <= is_link_ra_by_entry[i+1];
                        is_ret_ra_by_entry[i] <= is_ret_ra_by_entry[i+1];
                        PC_by_entry[i] <= PC_by_entry[i+1];
                        pred_PC_by_entry[i] <= pred_PC_by_entry[i+1];
                        imm20_by_entry[i] <= imm20_by_entry[i+1];
                        A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= A_ready_by_entry[i+1] | A_forward_by_entry[i+1];
                        A_unneeded_or_is_zero_by_entry[i] <= A_unneeded_or_is_zero_by_entry[i+1];
                        B_PR_by_entry[i] <= B_PR_by_entry[i+1];
                        B_ready_by_entry[i] <= B_ready_by_entry[i+1] | B_forward_by_entry[i+1];
                        B_unneeded_or_is_zero_by_entry[i] <= B_unneeded_or_is_zero_by_entry[i+1];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i+1];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i+1];
                        op_by_entry[i] <= iq_enq_op;
                        pred_info_by_entry[i] <= iq_enq_pred_info;
                        pred_lru_by_entry[i] <= iq_enq_pred_lru;
                        is_link_ra_by_entry[i] <= iq_enq_is_link_ra;
                        is_ret_ra_by_entry[i] <= iq_enq_is_ret_ra;
                        PC_by_entry[i] <= iq_enq_PC;
                        pred_PC_by_entry[i] <= iq_enq_pred_PC;
                        imm20_by_entry[i] <= iq_enq_imm20;
                        A_PR_by_entry[i] <= iq_enq_A_PR;
                        A_ready_by_entry[i] <= iq_enq_A_ready;
                        A_unneeded_or_is_zero_by_entry[i] <= iq_enq_A_unneeded_or_is_zero;
                        B_PR_by_entry[i] <= iq_enq_B_PR;
                        B_ready_by_entry[i] <= iq_enq_B_ready;
                        B_unneeded_or_is_zero_by_entry[i] <= iq_enq_B_unneeded_or_is_zero;
                        dest_PR_by_entry[i] <= iq_enq_dest_PR;
                        ROB_index_by_entry[i] <= iq_enq_ROB_index;
                    end
                end

                // otherwise take self
                else begin

                    // take self valid entry
                    if (valid_by_entry[i]) begin
                        valid_by_entry[i] <= 1'b1;
                        op_by_entry[i] <= op_by_entry[i+1];
                        pred_info_by_entry[i] <= pred_info_by_entry[i];
                        pred_lru_by_entry[i] <= pred_lru_by_entry[i];
                        is_link_ra_by_entry[i] <= is_link_ra_by_entry[i];
                        is_ret_ra_by_entry[i] <= is_ret_ra_by_entry[i];
                        PC_by_entry[i] <= PC_by_entry[i];
                        pred_PC_by_entry[i] <= pred_PC_by_entry[i];
                        imm20_by_entry[i] <= imm20_by_entry[i];
                        A_PR_by_entry[i] <= A_PR_by_entry[i];
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | A_forward_by_entry[i];
                        A_unneeded_or_is_zero_by_entry[i] <= A_unneeded_or_is_zero_by_entry[i];
                        B_PR_by_entry[i] <= B_PR_by_entry[i];
                        B_ready_by_entry[i] <= B_ready_by_entry[i] | B_forward_by_entry[i];
                        B_unneeded_or_is_zero_by_entry[i] <= B_unneeded_or_is_zero_by_entry[i];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];
                    end

                    // take self dispatch
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        op_by_entry[i] <= iq_enq_op;
                        pred_info_by_entry[i] <= iq_enq_pred_info;
                        pred_lru_by_entry[i] <= iq_enq_pred_lru;
                        is_link_ra_by_entry[i] <= iq_enq_is_link_ra;
                        is_ret_ra_by_entry[i] <= iq_enq_is_ret_ra;
                        PC_by_entry[i] <= iq_enq_PC;
                        pred_PC_by_entry[i] <= iq_enq_pred_PC;
                        imm20_by_entry[i] <= iq_enq_imm20;
                        A_PR_by_entry[i] <= iq_enq_A_PR;
                        A_ready_by_entry[i] <= iq_enq_A_ready;
                        A_unneeded_or_is_zero_by_entry[i] <= iq_enq_A_unneeded_or_is_zero;
                        B_PR_by_entry[i] <= iq_enq_B_PR;
                        B_ready_by_entry[i] <= iq_enq_B_ready;
                        B_unneeded_or_is_zero_by_entry[i] <= iq_enq_B_unneeded_or_is_zero;
                        dest_PR_by_entry[i] <= iq_enq_dest_PR;
                        ROB_index_by_entry[i] <= iq_enq_ROB_index;
                    end
                end
            end
        end
    end

endmodule