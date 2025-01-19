/*
    Filename: alu_reg_iq.sv
    Author: zlagpacan
    Description: RTL for ALU Register-Register Issue Queue
    Spec: LOROF/spec/design/alu_reg_iq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_iq (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU op dispatch by way
    input logic [3:0]                       dispatch_valid_by_way,
    input logic [3:0][3:0]                  dispatch_op_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_A_PR_by_way,
    input logic [3:0]                       dispatch_A_ready_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_B_PR_by_way,
    input logic [3:0]                       dispatch_B_ready_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_dest_PR_by_way,
    input logic [3:0][LOG_ROB_ENTRIES-1:0]  dispatch_ROB_index_by_way,

    // ALU op dispatch feedback by way
    output logic [3:0] dispatch_ready_by_way,

    // ALU pipeline feedback
    input logic pipeline_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // ALU op issue to ALU pipeline
    output logic                            issue_valid,
    output logic [3:0]                      issue_op,
    output logic                            issue_A_forward,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_A_bank,
    output logic                            issue_B_forward,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_B_bank,
    output logic [LOG_PR_COUNT-1:0]         issue_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]      issue_ROB_index,

    // reg read req to PRF
    output logic                        PRF_req_A_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_A_PR,
    output logic                        PRF_req_B_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Signals:

    // IQ entries
    logic [ALU_REG_IQ_ENTRIES-1:0]                      valid_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][3:0]                 op_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]    A_PR_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]                      A_ready_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]    B_PR_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]                      B_ready_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]    dest_PR_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0] ROB_index_by_entry;

    // issue logic helper signals
    logic [ALU_REG_IQ_ENTRIES-1:0]  A_forward_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]  B_forward_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]  issue_ready_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]  issue_one_hot_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]  issue_mask;
    logic [ALU_REG_IQ_ENTRIES-1:0]  take_above_mask;

    // incoming dispatch crossbar by entry
    logic [ALU_REG_IQ_ENTRIES-1:0]                          dispatch_valid_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][3:0]                     dispatch_op_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dispatch_A_PR_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]                          dispatch_A_ready_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dispatch_B_PR_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0]                          dispatch_B_ready_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dispatch_dest_PR_by_entry;
    logic [ALU_REG_IQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]     dispatch_ROB_index_by_entry;

    // incoming dispatch req masks for each of 4 possible dispatch ways
    logic [3:0][ALU_REG_IQ_ENTRIES-1:0]     dispatch_open_mask_by_way;
    logic [3:0][ALU_REG_IQ_ENTRIES-1:0]     pq_one_hot_by_way;
    logic [3:0][ALU_REG_IQ_ENTRIES-1:0]     dispatch_one_hot_by_way;

    // ----------------------------------------------------------------
    // Issue Logic:

    always_comb begin
        for (int i = 0; i < ALU_REG_IQ_ENTRIES; i++) begin
            A_forward_by_entry[i] = (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            B_forward_by_entry[i] = (B_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
        end
    end

    assign issue_ready_by_entry = 
        {ALU_REG_IQ_ENTRIES{pipeline_ready}}
        &
        valid_by_entry
        &
        (A_ready_by_entry | A_forward_by_entry)
        &
        (B_ready_by_entry | B_forward_by_entry)
    ;

    pq_lsb #(.WIDTH(8)) ISSUE_PQ_LSB (
        .req_vec(issue_ready_by_entry),
        .ack_one_hot(issue_one_hot_by_entry),
        .ack_mask(issue_mask)
    );

    always_comb begin

        // issue automatically valid if any entry ready
        issue_valid = |issue_ready_by_entry;

        // one-hot mux over entries for final issue:
        issue_op = '0;
        issue_A_forward = '0;
        issue_A_bank = '0;
        issue_B_forward = '0;
        issue_B_bank = '0;
        issue_dest_PR = '0;
        issue_ROB_index = '0;

        PRF_req_A_valid = '0;
        PRF_req_A_PR = '0;
        PRF_req_B_valid = '0;
        PRF_req_B_PR = '0;

        for (int entry = 0; entry < ALU_REG_IQ_ENTRIES; entry++) begin

            issue_op |= op_by_entry[entry] 
                & {4{issue_one_hot_by_entry[entry]}};

            issue_A_forward |= A_forward_by_entry[entry] 
                & issue_one_hot_by_entry[entry];

            issue_A_bank |= A_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0] 
                & {LOG_PRF_BANK_COUNT{issue_one_hot_by_entry[entry]}};

            issue_B_forward |= B_forward_by_entry[entry] 
                & issue_one_hot_by_entry[entry];

            issue_B_bank |= B_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0] 
                & {LOG_PRF_BANK_COUNT{issue_one_hot_by_entry[entry]}};

            issue_dest_PR |= dest_PR_by_entry[entry] 
                & {LOG_PR_COUNT{issue_one_hot_by_entry[entry]}};

            issue_ROB_index |= ROB_index_by_entry[entry] 
                & {LOG_ROB_ENTRIES{issue_one_hot_by_entry[entry]}};

            PRF_req_A_valid |= ~A_forward_by_entry[entry] 
                & issue_one_hot_by_entry[entry];
                
            PRF_req_A_PR |= A_PR_by_entry[entry] 
                & {LOG_PR_COUNT{issue_one_hot_by_entry[entry]}};

            PRF_req_B_valid |= ~B_forward_by_entry[entry] 
                & issue_one_hot_by_entry[entry];

            PRF_req_B_PR |= B_PR_by_entry[entry] 
                & {LOG_PR_COUNT{issue_one_hot_by_entry[entry]}};
        end
    end

    // take above if in issue mask
    assign take_above_mask = issue_mask;

    // ----------------------------------------------------------------
    // Dispatch Logic:

    // immediately advertise ready following top 4 entries open
    assign dispatch_ready_by_way = ~valid_by_entry[ALU_REG_IQ_ENTRIES-1 -: 4];

    // cascaded dispatch mask PQ's by way:

    // way 0
    assign dispatch_open_mask_by_way[0] = ~valid_by_entry;
    pq_lsb #(.WIDTH(8)) DISPATCH_WAY0_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[0]),
        .ack_one_hot(pq_one_hot_by_way[0]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[0] = pq_one_hot_by_way[0] & {ALU_REG_IQ_ENTRIES{dispatch_valid_by_way[0]}};

    // way 1
    assign dispatch_open_mask_by_way[1] = dispatch_open_mask_by_way[0] & ~dispatch_one_hot_by_way[0];
    pq_lsb #(.WIDTH(8)) DISPATCH_WAY1_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[1]),
        .ack_one_hot(pq_one_hot_by_way[1]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[1] = pq_one_hot_by_way[1] & {ALU_REG_IQ_ENTRIES{dispatch_valid_by_way[1]}};
    
    assign dispatch_open_mask_by_way[2] = dispatch_open_mask_by_way[1] & ~dispatch_one_hot_by_way[1];
    pq_lsb #(.WIDTH(8)) DISPATCH_WAY2_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[2]),
        .ack_one_hot(pq_one_hot_by_way[2]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[2] = pq_one_hot_by_way[2] & {ALU_REG_IQ_ENTRIES{dispatch_valid_by_way[2]}};
    
    assign dispatch_open_mask_by_way[3] = dispatch_open_mask_by_way[2] & ~dispatch_one_hot_by_way[2];
    pq_lsb #(.WIDTH(8)) DISPATCH_WAY3_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[3]),
        .ack_one_hot(pq_one_hot_by_way[3]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[3] = pq_one_hot_by_way[3] & {ALU_REG_IQ_ENTRIES{dispatch_valid_by_way[3]}};

    // route PQ'd dispatch to entries
    always_comb begin
    
        dispatch_valid_by_entry = '0;
        dispatch_op_by_entry = '0;
        dispatch_A_PR_by_entry = '0;
        dispatch_A_ready_by_entry = '0;
        dispatch_B_PR_by_entry = '0;
        dispatch_B_ready_by_entry = '0;
        dispatch_dest_PR_by_entry = '0;
        dispatch_ROB_index_by_entry = '0;

        // one-hot mux selecting among ways at each entry
        for (int entry = 0; entry < ALU_REG_IQ_ENTRIES; entry++) begin

            for (int way = 0; way < 4; way++) begin

                dispatch_valid_by_entry[entry] |= dispatch_one_hot_by_way[way][entry];

                dispatch_op_by_entry[entry] |= dispatch_op_by_way[way]
                    & {4{dispatch_one_hot_by_way[way][entry]}};

                dispatch_A_PR_by_entry[entry] |= dispatch_A_PR_by_way[way]
                    & {LOG_PR_COUNT{dispatch_one_hot_by_way[way][entry]}};

                dispatch_A_ready_by_entry[entry] |= dispatch_A_ready_by_way[way]
                    & dispatch_one_hot_by_way[way][entry];

                dispatch_B_PR_by_entry[entry] |= dispatch_B_PR_by_way[way]
                    & {LOG_PR_COUNT{dispatch_one_hot_by_way[way][entry]}};

                dispatch_B_ready_by_entry[entry] |= dispatch_B_ready_by_way[way]
                    & dispatch_one_hot_by_way[way][entry];

                dispatch_dest_PR_by_entry[entry] |= dispatch_dest_PR_by_way[way]
                    & {LOG_PR_COUNT{dispatch_one_hot_by_way[way][entry]}};

                dispatch_ROB_index_by_entry[entry] |= dispatch_ROB_index_by_way[way]
                    & {LOG_ROB_ENTRIES{dispatch_one_hot_by_way[way][entry]}};
            end
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_by_entry <= '0;
            op_by_entry <= '0;
            A_PR_by_entry <= '0;
            A_ready_by_entry <= '0;
            B_PR_by_entry <= '0;
            B_ready_by_entry <= '0;
            dest_PR_by_entry <= '0;
            ROB_index_by_entry <= '0;
        end
        else begin

            // highest entry can't take above
                // don't want to infer unused connection (this one loops around the IQ which will be bad)
            if (valid_by_entry[ALU_REG_IQ_ENTRIES-1]) begin
                valid_by_entry[ALU_REG_IQ_ENTRIES-1] <= valid_by_entry[ALU_REG_IQ_ENTRIES-1];
                op_by_entry[ALU_REG_IQ_ENTRIES-1] <= op_by_entry[ALU_REG_IQ_ENTRIES-1];
                A_PR_by_entry[ALU_REG_IQ_ENTRIES-1] <= A_PR_by_entry[ALU_REG_IQ_ENTRIES-1];
                A_ready_by_entry[ALU_REG_IQ_ENTRIES-1] <= A_ready_by_entry[ALU_REG_IQ_ENTRIES-1] | A_forward_by_entry[ALU_REG_IQ_ENTRIES-1];
                B_PR_by_entry[ALU_REG_IQ_ENTRIES-1] <= B_PR_by_entry[ALU_REG_IQ_ENTRIES-1];
                B_ready_by_entry[ALU_REG_IQ_ENTRIES-1] <= B_ready_by_entry[ALU_REG_IQ_ENTRIES-1] | B_forward_by_entry[ALU_REG_IQ_ENTRIES-1];
                dest_PR_by_entry[ALU_REG_IQ_ENTRIES-1] <= dest_PR_by_entry[ALU_REG_IQ_ENTRIES-1];
                ROB_index_by_entry[ALU_REG_IQ_ENTRIES-1] <= ROB_index_by_entry[ALU_REG_IQ_ENTRIES-1];
            end
            else begin
                valid_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_valid_by_entry[ALU_REG_IQ_ENTRIES-1];
                op_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_op_by_entry[ALU_REG_IQ_ENTRIES-1];
                A_PR_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_A_PR_by_entry[ALU_REG_IQ_ENTRIES-1];
                A_ready_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_A_ready_by_entry[ALU_REG_IQ_ENTRIES-1];
                B_PR_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_B_PR_by_entry[ALU_REG_IQ_ENTRIES-1];
                B_ready_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_B_ready_by_entry[ALU_REG_IQ_ENTRIES-1];
                dest_PR_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_dest_PR_by_entry[ALU_REG_IQ_ENTRIES-1];
                ROB_index_by_entry[ALU_REG_IQ_ENTRIES-1] <= dispatch_ROB_index_by_entry[ALU_REG_IQ_ENTRIES-1];
            end

            // remaining lower entries can take above
            for (int i = 0; i <= ALU_REG_IQ_ENTRIES-2; i++) begin

                // check take above
                if (take_above_mask[i]) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= valid_by_entry[i+1];
                        op_by_entry[i] <= op_by_entry[i+1];
                        A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= A_ready_by_entry[i+1] | A_forward_by_entry[i+1];
                        B_PR_by_entry[i] <= B_PR_by_entry[i+1];
                        B_ready_by_entry[i] <= B_ready_by_entry[i+1] | B_forward_by_entry[i+1];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i+1];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i+1];
                        op_by_entry[i] <= dispatch_op_by_entry[i+1];
                        A_PR_by_entry[i] <= dispatch_A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= dispatch_A_ready_by_entry[i+1];
                        B_PR_by_entry[i] <= dispatch_B_PR_by_entry[i+1];
                        B_ready_by_entry[i] <= dispatch_B_ready_by_entry[i+1];
                        dest_PR_by_entry[i] <= dispatch_dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= dispatch_ROB_index_by_entry[i+1];
                    end
                end

                // check take self
                else begin

                    // take self valid entry
                    if (valid_by_entry[i]) begin
                        valid_by_entry[i] <= valid_by_entry[i];
                        op_by_entry[i] <= op_by_entry[i];
                        A_PR_by_entry[i] <= A_PR_by_entry[i];
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | A_forward_by_entry[i];
                        B_PR_by_entry[i] <= B_PR_by_entry[i];
                        B_ready_by_entry[i] <= B_ready_by_entry[i] | B_forward_by_entry[i];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];
                    end

                    // take self dispatch
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        op_by_entry[i] <= dispatch_op_by_entry[i];
                        A_PR_by_entry[i] <= dispatch_A_PR_by_entry[i];
                        A_ready_by_entry[i] <= dispatch_A_ready_by_entry[i];
                        B_PR_by_entry[i] <= dispatch_B_PR_by_entry[i];
                        B_ready_by_entry[i] <= dispatch_B_ready_by_entry[i];
                        dest_PR_by_entry[i] <= dispatch_dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= dispatch_ROB_index_by_entry[i];
                    end
                end
            end
        end
    end

endmodule