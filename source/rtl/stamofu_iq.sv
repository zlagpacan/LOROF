/*
    Filename: stamofu_iq.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Issue Queue
    Spec: LOROF/spec/design/stamofu_iq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stamofu_iq #(
    parameter STAMOFU_IQ_ENTRIES = 8,
    parameter FAST_FORWARD_PIPE_COUNT = 4,
    parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
    input logic                                 stamofu_iq_enq_valid,
    input logic                                 stamofu_iq_enq_is_store,
    input logic                                 stamofu_iq_enq_is_amo,
    input logic                                 stamofu_iq_enq_is_fence,
    input logic [3:0]                           stamofu_iq_enq_op,
    input logic [11:0]                          stamofu_iq_enq_imm12,
    input logic [LOG_PR_COUNT-1:0]              stamofu_iq_enq_A_PR,
    input logic                                 stamofu_iq_enq_A_ready,
    input logic                                 stamofu_iq_enq_A_is_zero,
    input logic [LOG_PR_COUNT-1:0]              stamofu_iq_enq_B_PR,
    input logic                                 stamofu_iq_enq_B_ready,
    input logic                                 stamofu_iq_enq_B_is_zero,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_iq_enq_cq_index,

    // issue queue enqueue feedback
    output logic                                stamofu_iq_enq_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // fast forward notifs
    input logic [FAST_FORWARD_PIPE_COUNT-1:0]                       fast_forward_notif_valid_by_pipe,
    input logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0]     fast_forward_notif_PR_by_pipe,

    // pipeline issue 
    output logic                                    issue_valid,
    output logic                                    issue_is_store,
    output logic                                    issue_is_amo,
    output logic                                    issue_is_fence,
    output logic [3:0]                              issue_op,
    output logic [11:0]                             issue_imm12,
    output logic                                    issue_A_is_reg,
    output logic                                    issue_A_is_bus_forward,
    output logic                                    issue_A_is_fast_forward,
    output logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]  issue_A_fast_forward_pipe,
    output logic [LOG_PRF_BANK_COUNT-1:0]           issue_A_bank,
    output logic                                    issue_B_is_reg,
    output logic                                    issue_B_is_bus_forward,
    output logic                                    issue_B_is_fast_forward,
    output logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]  issue_B_fast_forward_pipe,
    output logic [LOG_PRF_BANK_COUNT-1:0]           issue_B_bank,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]       issue_cq_index,

    // pipeline feedback
    input logic                                     issue_ready,

    // reg read req to PRF
    output logic                        PRF_req_A_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_A_PR,
    output logic                        PRF_req_B_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_B_PR
);

    // don't have to worry about rob instruction kills
        // this is handled by stamofu_dq and stamofu_cq

    // ----------------------------------------------------------------
    // Signals:

    // IQ entries
    logic [STAMOFU_IQ_ENTRIES-1:0]                              valid_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0]                              is_store_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0]                              is_amo_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0]                              is_fence_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0][3:0]                         op_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0][11:0]                        imm12_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            A_PR_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0]                              A_ready_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0]                              A_is_zero_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            B_PR_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0]                              B_ready_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0]                              B_is_zero_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0][LOG_STAMOFU_CQ_ENTRIES-1:0]  cq_index_by_entry;

    // issue logic helper signals
    logic [STAMOFU_IQ_ENTRIES-1:0] A_is_bus_forward_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0] B_is_bus_forward_by_entry;

    logic [ALU_IMM_IQ_ENTRIES-1:0]                                      A_is_fast_forward_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][LOG_FAST_FORWARD_PIPE_COUNT-1:0]     A_fast_forward_pipe_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0]                                      B_is_fast_forward_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][LOG_FAST_FORWARD_PIPE_COUNT-1:0]     B_fast_forward_pipe_by_entry;

    logic [STAMOFU_IQ_ENTRIES-1:0] issue_ready_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0] issue_one_hot_by_entry;
    logic [STAMOFU_IQ_ENTRIES-1:0] issue_mask;

    // incoming dispatch crossbar by entry
    logic [STAMOFU_IQ_ENTRIES-1:0] dispatch_valid_by_entry;

    // incoming dispatch req mask
    logic [STAMOFU_IQ_ENTRIES-1:0] dispatch_open_mask;
    logic [STAMOFU_IQ_ENTRIES-1:0] dispatch_pe_one_hot;
    logic [STAMOFU_IQ_ENTRIES-1:0] dispatch_one_hot;

    // ----------------------------------------------------------------
    // Issue Logic:

    // forwarding check
    always_comb begin
        for (int i = 0; i < STAMOFU_IQ_ENTRIES; i++) begin
            A_is_bus_forward_by_entry[i] = (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            B_is_bus_forward_by_entry[i] = (B_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];

            A_is_fast_forward_by_entry[i] = 1'b0;
            A_fast_forward_pipe_by_entry[i] = 0;
            for (int pipe = 0; pipe < FAST_FORWARD_PIPE_COUNT; pipe++) begin
                if (fast_forward_notif_valid_by_pipe[pipe] & (A_PR_by_entry[i] == fast_forward_notif_PR_by_pipe[pipe])) begin
                    A_is_fast_forward_by_entry[i] = 1'b1;
                    A_fast_forward_pipe_by_entry[i] = pipe;
                end
            end
            B_is_fast_forward_by_entry[i] = 1'b0;
            B_fast_forward_pipe_by_entry[i] = 0;
            for (int pipe = 0; pipe < FAST_FORWARD_PIPE_COUNT; pipe++) begin
                if (fast_forward_notif_valid_by_pipe[pipe] & (B_PR_by_entry[i] == fast_forward_notif_PR_by_pipe[pipe])) begin
                    B_is_fast_forward_by_entry[i] = 1'b1;
                    B_fast_forward_pipe_by_entry[i] = pipe;
                end
            end
        end
    end

    // issue:
    
    // ready check
    assign issue_ready_by_entry = 
        {STAMOFU_IQ_ENTRIES{issue_ready}}
        & valid_by_entry
        & (A_ready_by_entry | A_is_bus_forward_by_entry | A_is_fast_forward_by_entry | A_is_zero_by_entry)
        & (B_ready_by_entry | B_is_bus_forward_by_entry | B_is_fast_forward_by_entry | B_is_zero_by_entry);

    // pe
    pe_lsb #(.WIDTH(STAMOFU_IQ_ENTRIES)) ISSUE_PE_LSB (
        .req_vec(issue_ready_by_entry),
        .ack_one_hot(issue_one_hot_by_entry),
        .ack_mask(issue_mask)
    );

    // mux
    always_comb begin
        
        // issue automatically valid if an entry ready
        issue_valid = |issue_ready_by_entry;

        // one-hot mux over entries for final issue:
        issue_is_store = '0;
        issue_is_amo = '0;
        issue_is_fence = '0;
        issue_op = '0;
        issue_imm12 = '0;
        issue_A_is_reg = '0;
        issue_A_is_bus_forward = '0;
        issue_A_is_fast_forward = '0;
        issue_A_fast_forward_pipe = '0;
        issue_A_bank = '0;
        issue_B_is_reg = '0;
        issue_B_is_bus_forward = '0;
        issue_B_is_fast_forward = '0;
        issue_B_fast_forward_pipe = '0;
        issue_B_bank = '0;
        issue_cq_index = '0;

        PRF_req_A_valid = '0;
        PRF_req_A_PR = '0;
        PRF_req_B_valid = '0;
        PRF_req_B_PR = '0;

        for (int entry = 0; entry < STAMOFU_IQ_ENTRIES; entry++) begin

            if (issue_one_hot_by_entry[entry]) begin

                issue_is_store |= is_store_by_entry[entry];
                issue_is_amo |= is_amo_by_entry[entry];
                issue_is_fence |= is_fence_by_entry[entry];
                issue_op |= op_by_entry[entry];
                issue_imm12 |= imm12_by_entry[entry];
                issue_A_is_reg |= ~(A_is_zero_by_entry[entry] | A_is_bus_forward_by_entry[entry] | A_is_fast_forward_by_entry[entry]);
                issue_A_is_bus_forward |= A_is_bus_forward_by_entry[entry];
                issue_A_is_fast_forward |= A_is_fast_forward_by_entry[entry];
                issue_A_fast_forward_pipe |= A_fast_forward_pipe_by_entry[entry];
                issue_A_bank |= A_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0];
                issue_B_is_reg |= ~(B_is_zero_by_entry[entry] | B_is_bus_forward_by_entry[entry] | B_is_fast_forward_by_entry[entry]);
                issue_B_is_bus_forward |= B_is_bus_forward_by_entry[entry];
                issue_B_is_fast_forward |= B_is_fast_forward_by_entry[entry];
                issue_B_fast_forward_pipe |= B_fast_forward_pipe_by_entry[entry];
                issue_B_bank |= B_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0];
                issue_cq_index |= cq_index_by_entry[entry];

                PRF_req_A_valid |= ~A_is_bus_forward_by_entry[entry] & ~A_is_zero_by_entry[entry];
                PRF_req_A_PR |= A_PR_by_entry[entry];
                PRF_req_B_valid |= ~B_is_bus_forward_by_entry[entry] & ~B_is_zero_by_entry[entry];
                PRF_req_B_PR |= B_PR_by_entry[entry];
            end
        end
    end

    // ----------------------------------------------------------------
    // Dispatch Logic:

    assign dispatch_open_mask = ~valid_by_entry;
    pe_lsb #(.WIDTH(STAMOFU_IQ_ENTRIES)) DISPATCH_PE_LSB (
        .req_vec(dispatch_open_mask),
        .ack_one_hot(dispatch_pe_one_hot),
        .ack_mask() // unused
    );
    assign dispatch_one_hot = dispatch_pe_one_hot & {STAMOFU_IQ_ENTRIES{stamofu_iq_enq_valid}};

    // give dispatch feedback
    assign stamofu_iq_enq_ready = |dispatch_open_mask;

    // route PE'd dispatch to entries
    assign dispatch_valid_by_entry = dispatch_one_hot;

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            valid_by_entry <= '0;
            is_store_by_entry <= '0;
            is_amo_by_entry <= '0;
            is_fence_by_entry <= '0;
            op_by_entry <= '0;
            imm12_by_entry <= '0;
            A_PR_by_entry <= '0;
            A_ready_by_entry <= '0;
            A_is_zero_by_entry <= '0;
            B_PR_by_entry <= '0;
            B_ready_by_entry <= '0;
            B_is_zero_by_entry <= '0;
            cq_index_by_entry <= '0;
        end
        else begin

            // --------------------------------------------------------
            // highest entry only takes self:
                // self: [STAMOFU_IQ_ENTRIES-1]

            // check take above
            if (issue_mask[STAMOFU_IQ_ENTRIES-1]) begin
                valid_by_entry[STAMOFU_IQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[STAMOFU_IQ_ENTRIES-1]) begin
                    valid_by_entry[STAMOFU_IQ_ENTRIES-1] <= 1'b1;
                    is_store_by_entry[STAMOFU_IQ_ENTRIES-1] <= is_store_by_entry[STAMOFU_IQ_ENTRIES-1];
                    is_amo_by_entry[STAMOFU_IQ_ENTRIES-1] <= is_amo_by_entry[STAMOFU_IQ_ENTRIES-1];
                    is_fence_by_entry[STAMOFU_IQ_ENTRIES-1] <= is_fence_by_entry[STAMOFU_IQ_ENTRIES-1];
                    op_by_entry[STAMOFU_IQ_ENTRIES-1] <= op_by_entry[STAMOFU_IQ_ENTRIES-1];
                    imm12_by_entry[STAMOFU_IQ_ENTRIES-1] <= imm12_by_entry[STAMOFU_IQ_ENTRIES-1];
                    A_PR_by_entry[STAMOFU_IQ_ENTRIES-1] <= A_PR_by_entry[STAMOFU_IQ_ENTRIES-1];
                    A_ready_by_entry[STAMOFU_IQ_ENTRIES-1] <= A_ready_by_entry[STAMOFU_IQ_ENTRIES-1] | A_is_bus_forward_by_entry[STAMOFU_IQ_ENTRIES-1];
                    A_is_zero_by_entry[STAMOFU_IQ_ENTRIES-1] <= A_is_zero_by_entry[STAMOFU_IQ_ENTRIES-1];
                    B_PR_by_entry[STAMOFU_IQ_ENTRIES-1] <= B_PR_by_entry[STAMOFU_IQ_ENTRIES-1];
                    B_ready_by_entry[STAMOFU_IQ_ENTRIES-1] <= B_ready_by_entry[STAMOFU_IQ_ENTRIES-1] | B_is_bus_forward_by_entry[STAMOFU_IQ_ENTRIES-1];
                    B_is_zero_by_entry[STAMOFU_IQ_ENTRIES-1] <= B_is_zero_by_entry[STAMOFU_IQ_ENTRIES-1];
                    cq_index_by_entry[STAMOFU_IQ_ENTRIES-1] <= cq_index_by_entry[STAMOFU_IQ_ENTRIES-1];
                end

                // take self dispatch
                else begin
                    valid_by_entry[STAMOFU_IQ_ENTRIES-1] <= dispatch_valid_by_entry[STAMOFU_IQ_ENTRIES-1];
                    is_store_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_is_store;
                    is_amo_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_is_amo;
                    is_fence_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_is_fence;
                    op_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_op;
                    imm12_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_imm12;
                    A_PR_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_A_PR;
                    A_ready_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_A_ready;
                    A_is_zero_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_A_is_zero;
                    B_PR_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_B_PR;
                    B_ready_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_B_ready;
                    B_is_zero_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_B_is_zero;
                    cq_index_by_entry[STAMOFU_IQ_ENTRIES-1] <= stamofu_iq_enq_cq_index;
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
            for (int i = 0; i <= STAMOFU_IQ_ENTRIES-2; i++) begin

                // check take above
                if (issue_mask[i]) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= 1'b1;
                        is_store_by_entry[i] <= is_store_by_entry[i+1];
                        is_amo_by_entry[i] <= is_amo_by_entry[i+1];
                        is_fence_by_entry[i] <= is_fence_by_entry[i+1];
                        op_by_entry[i] <= op_by_entry[i+1];
                        imm12_by_entry[i] <= imm12_by_entry[i+1];
                        A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= A_ready_by_entry[i+1] | A_is_bus_forward_by_entry[i+1];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i+1];
                        B_PR_by_entry[i] <= B_PR_by_entry[i+1];
                        B_ready_by_entry[i] <= B_ready_by_entry[i+1] | B_is_bus_forward_by_entry[i+1];
                        B_is_zero_by_entry[i] <= B_is_zero_by_entry[i+1];
                        cq_index_by_entry[i] <= cq_index_by_entry[i+1];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i+1];
                        is_store_by_entry[i] <= stamofu_iq_enq_is_store;
                        is_amo_by_entry[i] <= stamofu_iq_enq_is_amo;
                        is_fence_by_entry[i] <= stamofu_iq_enq_is_fence;
                        op_by_entry[i] <= stamofu_iq_enq_op;
                        imm12_by_entry[i] <= stamofu_iq_enq_imm12;
                        A_PR_by_entry[i] <= stamofu_iq_enq_A_PR;
                        A_ready_by_entry[i] <= stamofu_iq_enq_A_ready;
                        A_is_zero_by_entry[i] <= stamofu_iq_enq_A_is_zero;
                        B_PR_by_entry[i] <= stamofu_iq_enq_B_PR;
                        B_ready_by_entry[i] <= stamofu_iq_enq_B_ready;
                        B_is_zero_by_entry[i] <= stamofu_iq_enq_B_is_zero;
                        cq_index_by_entry[i] <= stamofu_iq_enq_cq_index;
                    end
                end

                // otherwise take self
                else begin

                    // take self valid entry
                    if (valid_by_entry[i]) begin
                        valid_by_entry[i] <= 1'b1;
                        is_store_by_entry[i] <= is_store_by_entry[i];
                        is_amo_by_entry[i] <= is_amo_by_entry[i];
                        is_fence_by_entry[i] <= is_fence_by_entry[i];
                        op_by_entry[i] <= op_by_entry[i];
                        imm12_by_entry[i] <= imm12_by_entry[i];
                        A_PR_by_entry[i] <= A_PR_by_entry[i];
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | A_is_bus_forward_by_entry[i];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i];
                        B_PR_by_entry[i] <= B_PR_by_entry[i];
                        B_ready_by_entry[i] <= B_ready_by_entry[i] | B_is_bus_forward_by_entry[i];
                        B_is_zero_by_entry[i] <= B_is_zero_by_entry[i];
                        cq_index_by_entry[i] <= cq_index_by_entry[i];
                    end

                    // take self dispatch
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        is_store_by_entry[i] <= stamofu_iq_enq_is_store;
                        is_amo_by_entry[i] <= stamofu_iq_enq_is_amo;
                        is_fence_by_entry[i] <= stamofu_iq_enq_is_fence;
                        op_by_entry[i] <= stamofu_iq_enq_op;
                        imm12_by_entry[i] <= stamofu_iq_enq_imm12;
                        A_PR_by_entry[i] <= stamofu_iq_enq_A_PR;
                        A_ready_by_entry[i] <= stamofu_iq_enq_A_ready;
                        A_is_zero_by_entry[i] <= stamofu_iq_enq_A_is_zero;
                        B_PR_by_entry[i] <= stamofu_iq_enq_B_PR;
                        B_ready_by_entry[i] <= stamofu_iq_enq_B_ready;
                        B_is_zero_by_entry[i] <= stamofu_iq_enq_B_is_zero;
                        cq_index_by_entry[i] <= stamofu_iq_enq_cq_index;
                    end
                end
            end
        end
    end

endmodule