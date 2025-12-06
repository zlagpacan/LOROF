/*
    Filename: alu_imm_iq.sv
    Author: zlagpacan
    Description: RTL for ALU Reg-Imm Issue Queue
    Spec: LOROF/spec/design/alu_imm_iq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_iq #(
    parameter ALU_IMM_IQ_ENTRIES = 12,
    parameter FAST_FORWARD_PIPE_COUNT = 4,
    parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FF_PIPELINE_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to issue queue
    input logic                         iq_enq_valid,
    input logic [3:0]                   iq_enq_op,
    input logic [11:0]                  iq_enq_imm12,
    input logic [LOG_PR_COUNT-1:0]      iq_enq_A_PR,
    input logic                         iq_enq_A_ready,
    input logic                         iq_enq_A_is_zero,
    input logic [LOG_PR_COUNT-1:0]      iq_enq_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]   iq_enq_ROB_index,

    // issue queue enqueue feedback
    output logic                        iq_enq_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // fast forward notifs
    input logic [FAST_FORWARD_PIPE_COUNT-1:0]                       fast_forward_valid_by_pipe,
    input logic [FAST_FORWARD_PIPE_COUNT-1:0][LOG_PR_COUNT-1:0]     fast_forward_PR_by_pipe,

    // pipeline issue
    output logic                                    issue_valid,
    output logic [3:0]                              issue_op,
    output logic [11:0]                             issue_imm12,
    output logic                                    issue_A_is_reg,
    output logic                                    issue_A_is_bus_forward,
    output logic                                    issue_A_is_fast_forward,
    output logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]  issue_A_fast_forward_pipe,
    output logic [LOG_PRF_BANK_COUNT-1:0]           issue_A_bank,
    output logic [LOG_PR_COUNT-1:0]                 issue_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]              issue_ROB_index,

    // pipeline feedback
    output logic                                    issue_ready,

    // reg read req to PRF
    output logic                        PRF_req_A_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_A_PR
);

    // ----------------------------------------------------------------
    // Signals:

    // IQ entries
    logic [ALU_IMM_IQ_ENTRIES-1:0]                          valid_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][3:0]                     op_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][11:0]                    imm12_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        A_PR_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0]                          A_ready_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0]                          A_is_zero_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dest_PR_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]     ROB_index_by_entry;

    // issue logic helper signals
    logic [ALU_IMM_IQ_ENTRIES-1:0] A_is_bus_forward_by_entry;

    logic [ALU_IMM_IQ_ENTRIES-1:0]                                      A_is_fast_forward_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0][LOG_FAST_FORWARD_PIPE_COUNT-1:0]     A_fast_forward_pipe_by_entry;

    logic [ALU_IMM_IQ_ENTRIES-1:0] issue_ready_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0] issue_one_hot_by_entry;
    logic [ALU_IMM_IQ_ENTRIES-1:0] issue_mask;

    // incoming dispatch crossbar by entry
    logic [ALU_IMM_IQ_ENTRIES-1:0] dispatch_valid_by_entry;

    // incoming dispatch reg mask
    logic [ALU_IMM_IQ_ENTRIES-1:0] dispatch_open_mask;
    logic [ALU_IMM_IQ_ENTRIES-1:0] dispatch_pe_one_hot;
    logic [ALU_IMM_IQ_ENTRIES-1:0] dispatch_one_hot;

    // ----------------------------------------------------------------
    // Issue Logic:

    // forwarding checks
    always_comb begin
        for (int i = 0; i < ALU_IMM_IQ_ENTRIES; i++) begin
            A_is_bus_forward_by_entry[i] = (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            A_is_fast_forward_by_entry[i] = 1'b0;
            for (int pipe = 0; pipe < FAST_FORWARD_PIPE_COUNT; pipe++) begin
                if (fast_forward_valid_by_pipe[pipe] & (A_PR_by_entry[i] == fast_forward_PR_by_pipe[pipe])) begin
                    A_is_fast_forward_by_entry[i] = 1'b1;
                    A_fast_forward_pipe_by_entry[i] = pipe;
                end
            end
        end
    end

    // issue:
    
    // ready check
    assign issue_ready_by_entry = 
        {ALU_IMM_IQ_ENTRIES{issue_ready}}
        & valid_by_entry
        & (A_ready_by_entry | A_is_bus_forward_by_entry | A_is_fast_forward_by_entry | A_is_zero_by_entry);

    // pe
    pe_lsb #(.WIDTH(ALU_IMM_IQ_ENTRIES)) ISSUE_PE_LSB (
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
        issue_imm12 = '0;
        issue_A_is_reg = '0;
        issue_A_is_bus_forward = '0;
        issue_A_is_fast_forward = '0;
        issue_A_fast_forward_pipe = '0;
        issue_A_bank = '0;
        issue_dest_PR = '0;
        issue_ROB_index = '0;

        PRF_req_A_valid = '0;
        PRF_req_A_PR = '0;

        for (int entry = 0; entry < ALU_IMM_IQ_ENTRIES; entry++) begin

            if (issue_one_hot_by_entry[entry]) begin

                issue_op |= op_by_entry[entry];
                issue_imm12 |= imm12_by_entry[entry];
                issue_A_is_reg |= ~(A_is_zero_by_entry[entry] | A_is_bus_forward_by_entry[entry] | A_is_fast_forward_by_entry[entry]);
                issue_A_is_bus_forward |= A_is_bus_forward_by_entry[entry];
                issue_A_is_fast_forward |= A_is_fast_forward_by_entry[entry];
                issue_A_fast_forward_pipe |= A_fast_forward_pipe_by_entry[entry];
                issue_A_bank |= A_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0];
                issue_dest_PR |= dest_PR_by_entry[entry];
                issue_ROB_index |= ROB_index_by_entry[entry];

                PRF_req_A_valid |= ~(A_is_zero_by_entry[entry] | A_is_bus_forward_by_entry[entry] | A_is_fast_forward_by_entry[entry]);
                PRF_req_A_PR |= A_PR_by_entry[entry];
            end
        end
    end

    // ----------------------------------------------------------------
    // Dispatch Logic:

    assign dispatch_open_mask = ~valid_by_entry;
    pe_lsb #(.WIDTH(ALU_IMM_IQ_ENTRIES)) DISPATCH_PE_LSB (
        .req_vec(dispatch_open_mask),
        .ack_one_hot(dispatch_pe_one_hot),
        .ack_mask() // unused
    );
    assign dispatch_one_hot = dispatch_pe_one_hot & {ALU_IMM_IQ_ENTRIES{iq_enq_valid}};

    // give dispatch feedback
    assign iq_enq_ready = |dispatch_open_mask;

    // route PE'd dispatch to entries
    assign dispatch_valid_by_entry = dispatch_one_hot;

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            valid_by_entry <= '0;
            op_by_entry <= '0;
            imm12_by_entry <= '0;
            A_PR_by_entry <= '0;
            A_ready_by_entry <= '0;
            A_is_zero_by_entry <= '0;
            dest_PR_by_entry <= '0;
            ROB_index_by_entry <= '0;
        end
        else begin

            // --------------------------------------------------------
            // highest entry only takes self:
                // self: [ALU_IMM_IQ_ENTRIES-1]

            // check take above
            if (issue_mask[ALU_IMM_IQ_ENTRIES-1]) begin
                valid_by_entry[ALU_IMM_IQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[ALU_IMM_IQ_ENTRIES-1]) begin
                    valid_by_entry[ALU_IMM_IQ_ENTRIES-1] <= 1'b1;
                    op_by_entry[ALU_IMM_IQ_ENTRIES-1] <= op_by_entry[ALU_IMM_IQ_ENTRIES-1];
                    imm12_by_entry[ALU_IMM_IQ_ENTRIES-1] <= imm12_by_entry[ALU_IMM_IQ_ENTRIES-1];
                    A_PR_by_entry[ALU_IMM_IQ_ENTRIES-1] <= A_PR_by_entry[ALU_IMM_IQ_ENTRIES-1];
                    A_ready_by_entry[ALU_IMM_IQ_ENTRIES-1] <= A_ready_by_entry[ALU_IMM_IQ_ENTRIES-1] | A_is_bus_forward_by_entry[ALU_IMM_IQ_ENTRIES-1];
                    A_is_zero_by_entry[ALU_IMM_IQ_ENTRIES-1] <= A_is_zero_by_entry[ALU_IMM_IQ_ENTRIES-1];
                    dest_PR_by_entry[ALU_IMM_IQ_ENTRIES-1] <= dest_PR_by_entry[ALU_IMM_IQ_ENTRIES-1];
                    ROB_index_by_entry[ALU_IMM_IQ_ENTRIES-1] <= ROB_index_by_entry[ALU_IMM_IQ_ENTRIES-1];
                end

                // take self dispatch
                else begin
                    valid_by_entry[ALU_IMM_IQ_ENTRIES-1] <= dispatch_valid_by_entry[ALU_IMM_IQ_ENTRIES-1];
                    op_by_entry[ALU_IMM_IQ_ENTRIES-1] <= iq_enq_op;
                    imm12_by_entry[ALU_IMM_IQ_ENTRIES-1] <= iq_enq_imm12;
                    A_PR_by_entry[ALU_IMM_IQ_ENTRIES-1] <= iq_enq_A_PR;
                    A_ready_by_entry[ALU_IMM_IQ_ENTRIES-1] <= iq_enq_A_ready;
                    A_is_zero_by_entry[ALU_IMM_IQ_ENTRIES-1] <= iq_enq_A_is_zero;
                    dest_PR_by_entry[ALU_IMM_IQ_ENTRIES-1] <= iq_enq_dest_PR;
                    ROB_index_by_entry[ALU_IMM_IQ_ENTRIES-1] <= iq_enq_ROB_index;
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
            for (int i = 0; i <= ALU_IMM_IQ_ENTRIES-2; i++) begin

                // check take above
                if (issue_mask[i]) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= 1'b1;
                        op_by_entry[i] <= op_by_entry[i+1];
                        imm12_by_entry[i] <= imm12_by_entry[i+1];
                        A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= A_ready_by_entry[i+1] | A_is_bus_forward_by_entry[i+1];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i+1];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i+1];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i+1];
                        op_by_entry[i] <= iq_enq_op;
                        imm12_by_entry[i] <= iq_enq_imm12;
                        A_PR_by_entry[i] <= iq_enq_A_PR;
                        A_ready_by_entry[i] <= iq_enq_A_ready;
                        A_is_zero_by_entry[i] <= iq_enq_A_is_zero;
                        dest_PR_by_entry[i] <= iq_enq_dest_PR;
                        ROB_index_by_entry[i] <= iq_enq_ROB_index;
                    end
                end

                // otherwise take self
                else begin

                    // take self valid entry
                    if (valid_by_entry[i]) begin
                        valid_by_entry[i] <= 1'b1;
                        op_by_entry[i] <= op_by_entry[i];
                        imm12_by_entry[i] <= imm12_by_entry[i];
                        A_PR_by_entry[i] <= A_PR_by_entry[i];
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | A_is_bus_forward_by_entry[i];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];
                    end

                    // take self dispatch
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        op_by_entry[i] <= iq_enq_op;
                        imm12_by_entry[i] <= iq_enq_imm12;
                        A_PR_by_entry[i] <= iq_enq_A_PR;
                        A_ready_by_entry[i] <= iq_enq_A_ready;
                        A_is_zero_by_entry[i] <= iq_enq_A_is_zero;
                        dest_PR_by_entry[i] <= iq_enq_dest_PR;
                        ROB_index_by_entry[i] <= iq_enq_ROB_index;
                    end
                end
            end
        end
    end

endmodule