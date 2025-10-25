/*
    Filename: alu_reg_mdu_iq_single.sv
    Author: zlagpacan
    Description: RTL for ALU Reg-Reg + Mul-Div Unit Issue Queue
    Spec: LOROF/spec/design/alu_reg_mdu_iq_single.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_mdu_iq_single #(
    parameter ALU_REG_MDU_IQ_ENTRIES = 12
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
    input logic                         iq_enq_valid,
    input logic                         iq_enq_is_alu_reg,
    input logic                         iq_enq_is_mdu,
    input logic [3:0]                   iq_enq_op,
    input logic [LOG_PR_COUNT-1:0]      iq_enq_A_PR,
    input logic                         iq_enq_A_ready,
    input logic                         iq_enq_A_is_zero,
    input logic [LOG_PR_COUNT-1:0]      iq_enq_B_PR,
    input logic                         iq_enq_B_ready,
    input logic                         iq_enq_B_is_zero,
    input logic [LOG_PR_COUNT-1:0]      iq_enq_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]   iq_enq_ROB_index,

    // issue queue enqueue feedback
    output logic                        iq_enq_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // ALU reg pipeline issue
    output logic                            alu_reg_issue_valid,

    // MDU pipeline issue
    output logic                            mdu_issue_valid,

    // shared issue info
    output logic [3:0]                  issue_op,
    output logic                        issue_A_forward,
    output logic                        issue_A_is_zero,
    output logic [LOG_PR_COUNT-1:0]     issue_A_PR,
    output logic                        issue_B_forward,
    output logic                        issue_B_is_zero,
    output logic [LOG_PR_COUNT-1:0]     issue_B_PR,
    output logic [LOG_PR_COUNT-1:0]     issue_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  issue_ROB_index,

    // ALU reg pipeline feedback
    input logic                             alu_reg_issue_ready,

    // MDU pipeline feedback
    input logic                             mdu_issue_ready,

    // reg read req to PRF
    output logic                        PRF_req_A_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_A_PR,
    output logic                        PRF_req_B_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Signals:

    // IQ entries
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0]                          valid_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0]                          is_alu_reg_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0]                          is_mdu_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0][3:0]                     op_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        A_PR_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0]                          A_ready_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0]                          A_is_zero_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        B_PR_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0]                          B_ready_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0]                          B_is_zero_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dest_PR_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]     ROB_index_by_entry;

    // issue logic helper signals
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] A_forward_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] B_forward_by_entry;

    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] issue_ready_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] issue_one_hot_by_entry;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] issue_mask;

    // incoming dispatch crossbar by entry
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] dispatch_valid_by_entry;

    // incoming dispatch reg mask
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] dispatch_open_mask;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] dispatch_pe_one_hot;
    logic [ALU_REG_MDU_IQ_ENTRIES-1:0] dispatch_one_hot;

    // ----------------------------------------------------------------
    // Issue Logic:

    // forwarding check
    always_comb begin
        for (int i = 0; i < ALU_REG_MDU_IQ_ENTRIES; i++) begin
            A_forward_by_entry[i] = (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            B_forward_by_entry[i] = (B_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
        end
    end

    // issue:
    
    // ready check
    assign issue_ready_by_entry = 
        (
            {ALU_REG_MDU_IQ_ENTRIES{alu_reg_issue_ready}} & is_alu_reg_by_entry
            | {ALU_REG_MDU_IQ_ENTRIES{mdu_issue_ready}} & is_mdu_by_entry
        )
        & valid_by_entry
        & (A_ready_by_entry | A_forward_by_entry | A_is_zero_by_entry)
        & (B_ready_by_entry | B_forward_by_entry | B_is_zero_by_entry);

    // pe
    pe_lsb #(.WIDTH(ALU_REG_MDU_IQ_ENTRIES)) ISSUE_PE_LSB (
        .req_vec(issue_ready_by_entry),
        .ack_one_hot(issue_one_hot_by_entry),
        .ack_mask(issue_mask)
    );

    // mux
    always_comb begin
        
        // issue automatically valid if an entry ready
        alu_reg_issue_valid = |(issue_ready_by_entry & is_alu_reg_by_entry);
        mdu_issue_valid = |(issue_ready_by_entry & is_mdu_by_entry);

        // one-hot mux over entries for final issue:
        issue_op = '0;
        issue_A_forward = '0;
        issue_A_is_zero = '0;
        issue_A_PR = '0;
        issue_B_forward = '0;
        issue_B_is_zero = '0;
        issue_B_PR = '0;
        issue_dest_PR = '0;
        issue_ROB_index = '0;

        PRF_req_A_valid = '0;
        PRF_req_A_PR = '0;
        PRF_req_B_valid = '0;
        PRF_req_B_PR = '0;

        for (int entry = 0; entry < ALU_REG_MDU_IQ_ENTRIES; entry++) begin

            if (issue_one_hot_by_entry[entry]) begin

                issue_op |= op_by_entry[entry];
                issue_A_forward |= A_forward_by_entry[entry];
                issue_A_is_zero |= A_is_zero_by_entry[entry];
                issue_A_PR |= A_PR_by_entry[entry];
                issue_B_forward |= B_forward_by_entry[entry];
                issue_B_is_zero |= B_is_zero_by_entry[entry];
                issue_B_PR |= B_PR_by_entry[entry];
                issue_dest_PR |= dest_PR_by_entry[entry];
                issue_ROB_index |= ROB_index_by_entry[entry];

                PRF_req_A_valid |= ~A_forward_by_entry[entry] & ~A_is_zero_by_entry[entry];
                PRF_req_A_PR |= A_PR_by_entry[entry];
                PRF_req_B_valid |= ~B_forward_by_entry[entry] & ~B_is_zero_by_entry[entry];
                PRF_req_B_PR |= B_PR_by_entry[entry];
            end
        end
    end

    // ----------------------------------------------------------------
    // Dispatch Logic:

    assign dispatch_open_mask = ~valid_by_entry;
    pe_lsb #(.WIDTH(ALU_REG_MDU_IQ_ENTRIES)) DISPATCH_PE_LSB (
        .req_vec(dispatch_open_mask),
        .ack_one_hot(dispatch_pe_one_hot),
        .ack_mask() // unused
    );
    assign dispatch_one_hot = dispatch_pe_one_hot & {ALU_REG_MDU_IQ_ENTRIES{iq_enq_valid}};

    // give dispatch feedback
    assign iq_enq_ready = |dispatch_open_mask;

    // route PE'd dispatch to entries
    assign dispatch_valid_by_entry = dispatch_one_hot;

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_by_entry <= '0;
            is_alu_reg_by_entry <= '0;
            is_mdu_by_entry <= '0;
            op_by_entry <= '0;
            A_PR_by_entry <= '0;
            A_ready_by_entry <= '0;
            A_is_zero_by_entry <= '0;
            B_PR_by_entry <= '0;
            B_ready_by_entry <= '0;
            B_is_zero_by_entry <= '0;
            dest_PR_by_entry <= '0;
            ROB_index_by_entry <= '0;
        end
        else begin

            // --------------------------------------------------------
            // highest entry only takes self:
                // self: [ALU_REG_MDU_IQ_ENTRIES-1]

            // check take above or 2 above -> clear entry
            if (issue_mask[ALU_REG_MDU_IQ_ENTRIES-1]) begin
                valid_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[ALU_REG_MDU_IQ_ENTRIES-1]) begin
                    valid_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= 1'b1;
                    is_alu_reg_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= is_alu_reg_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    is_mdu_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= is_mdu_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    op_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= op_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    A_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= A_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    A_ready_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= A_ready_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] | A_forward_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    A_is_zero_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= A_is_zero_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    B_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= B_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    B_ready_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= B_ready_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] | B_forward_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    B_is_zero_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= B_is_zero_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    dest_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= dest_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    ROB_index_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= ROB_index_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                end

                // take self dispatch
                else begin
                    valid_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= dispatch_valid_by_entry[ALU_REG_MDU_IQ_ENTRIES-1];
                    is_alu_reg_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_is_alu_reg;
                    is_mdu_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_is_mdu;
                    op_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_op;
                    A_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_A_PR;
                    A_ready_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_A_ready;
                    A_is_zero_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_A_is_zero;
                    B_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_B_PR;
                    B_ready_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_B_ready;
                    B_is_zero_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_B_is_zero;
                    dest_PR_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_dest_PR;
                    ROB_index_by_entry[ALU_REG_MDU_IQ_ENTRIES-1] <= iq_enq_ROB_index;
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
                // [ALU_REG_MDU_IQ_ENTRIES-1] can only take self
            for (int i = 0; i <= ALU_REG_MDU_IQ_ENTRIES-2; i++) begin

                // check take above
                if (issue_mask[i]) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= 1'b1;
                        is_alu_reg_by_entry[i] <= is_alu_reg_by_entry[i+1];
                        is_mdu_by_entry[i] <= is_mdu_by_entry[i+1];
                        op_by_entry[i] <= op_by_entry[i+1];
                        A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= A_ready_by_entry[i+1] | A_forward_by_entry[i+1];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i+1];
                        B_PR_by_entry[i] <= B_PR_by_entry[i+1];
                        B_ready_by_entry[i] <= B_ready_by_entry[i+1] | B_forward_by_entry[i+1];
                        B_is_zero_by_entry[i] <= B_is_zero_by_entry[i+1];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i+1];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i+1];
                        is_alu_reg_by_entry[i] <= iq_enq_is_alu_reg;
                        is_mdu_by_entry[i] <= iq_enq_is_mdu;
                        op_by_entry[i] <= iq_enq_op;
                        A_PR_by_entry[i] <= iq_enq_A_PR;
                        A_ready_by_entry[i] <= iq_enq_A_ready;
                        A_is_zero_by_entry[i] <= iq_enq_A_is_zero;
                        B_PR_by_entry[i] <= iq_enq_B_PR;
                        B_ready_by_entry[i] <= iq_enq_B_ready;
                        B_is_zero_by_entry[i] <= iq_enq_B_is_zero;
                        dest_PR_by_entry[i] <= iq_enq_dest_PR;
                        ROB_index_by_entry[i] <= iq_enq_ROB_index;
                    end
                end

                // otherwise take self
                else begin

                    // take self valid entry
                    if (valid_by_entry[i]) begin
                        valid_by_entry[i] <= 1'b1;
                        is_alu_reg_by_entry[i] <= is_alu_reg_by_entry[i];
                        is_mdu_by_entry[i] <= is_mdu_by_entry[i];
                        op_by_entry[i] <= op_by_entry[i];
                        A_PR_by_entry[i] <= A_PR_by_entry[i];
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | A_forward_by_entry[i];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i];
                        B_PR_by_entry[i] <= B_PR_by_entry[i];
                        B_ready_by_entry[i] <= B_ready_by_entry[i] | B_forward_by_entry[i];
                        B_is_zero_by_entry[i] <= B_is_zero_by_entry[i];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];
                    end

                    // take self dispatch
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        is_alu_reg_by_entry[i] <= iq_enq_is_alu_reg;
                        is_mdu_by_entry[i] <= iq_enq_is_mdu;
                        op_by_entry[i] <= iq_enq_op;
                        A_PR_by_entry[i] <= iq_enq_A_PR;
                        A_ready_by_entry[i] <= iq_enq_A_ready;
                        A_is_zero_by_entry[i] <= iq_enq_A_is_zero;
                        B_PR_by_entry[i] <= iq_enq_B_PR;
                        B_ready_by_entry[i] <= iq_enq_B_ready;
                        B_is_zero_by_entry[i] <= iq_enq_B_is_zero;
                        dest_PR_by_entry[i] <= iq_enq_dest_PR;
                        ROB_index_by_entry[i] <= iq_enq_ROB_index;
                    end
                end
            end
        end
    end

endmodule