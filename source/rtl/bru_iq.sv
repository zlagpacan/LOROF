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

    // op dispatch by way
    input logic [3:0]                           dispatch_attempt_by_way,
    input logic [3:0]                           dispatch_valid_by_way,
    input logic [3:0][3:0]                      dispatch_op_by_way,
    input logic [3:0][BTB_PRED_INFO_WIDTH-1:0]  dispatch_pred_info_by_way,
    input logic [3:0]                           dispatch_pred_lru_by_way,
    input logic [3:0]                           dispatch_is_link_ra_by_way,
    input logic [3:0]                           dispatch_is_ret_ra_by_way,
    input logic [3:0][31:0]                     dispatch_PC_by_way,
    input logic [3:0][31:0]                     dispatch_pred_PC_by_way,
    input logic [3:0][19:0]                     dispatch_imm20_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]         dispatch_A_PR_by_way,
    input logic [3:0]                           dispatch_A_unneeded_by_way,
    input logic [3:0]                           dispatch_A_ready_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]         dispatch_B_PR_by_way,
    input logic [3:0]                           dispatch_B_unneeded_by_way,
    input logic [3:0]                           dispatch_B_ready_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]         dispatch_dest_PR_by_way,
    input logic [3:0][LOG_ROB_ENTRIES-1:0]      dispatch_ROB_index_by_way,

    // op dispatch feedback
    output logic [3:0] dispatch_ack_by_way,

    // BRU pipeline feedback
    input logic pipeline_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // BRU op issue to BRU pipeline
    output logic                            issue_valid,
    output logic [3:0]                      issue_op,
    output logic [BTB_PRED_INFO_WIDTH-1:0]  issue_pred_info,
    output logic                            issue_pred_lru,
    output logic                            issue_is_link_ra,
    output logic                            issue_is_ret_ra,
    output logic [31:0]                     issue_PC,
    output logic [31:0]                     issue_pred_PC,
    output logic [19:0]                     issue_imm20,
    output logic                            issue_A_unneeded,
    output logic                            issue_A_forward,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_A_bank,
    output logic                            issue_B_unneeded,
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
    logic [BRU_IQ_ENTRIES-1:0]                              A_unneeded_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              A_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            B_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              B_unneeded_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              B_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            dest_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]         ROB_index_by_entry;

    // issue logic helper signals
    logic [BRU_IQ_ENTRIES-1:0]  A_forward_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]  B_forward_by_entry;

    logic [BRU_IQ_ENTRIES-1:0] issue_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0] issue_one_hot_by_entry;
    logic [BRU_IQ_ENTRIES-1:0] issue_mask;

    // incoming dispatch crossbar by entry
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_valid_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][3:0]                         dispatch_op_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][BTB_PRED_INFO_WIDTH-1:0]     dispatch_pred_info_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_pred_lru_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_is_link_ra_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_is_ret_ra_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][31:0]                        dispatch_PC_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][31:0]                        dispatch_pred_PC_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][19:0]                        dispatch_imm20_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            dispatch_A_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_A_unneeded_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_A_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            dispatch_B_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_B_unneeded_by_entry;
    logic [BRU_IQ_ENTRIES-1:0]                              dispatch_B_ready_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]            dispatch_dest_PR_by_entry;
    logic [BRU_IQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]         dispatch_ROB_index_by_entry;

    // incoming dispatch req masks for each of 4 possible dispatch ways
    logic [3:0][BRU_IQ_ENTRIES-1:0]     dispatch_open_mask_by_way;
    logic [3:0][BRU_IQ_ENTRIES-1:0]     dispatch_pq_one_hot_by_way;
    logic [3:0][BRU_IQ_ENTRIES-1:0]     dispatch_one_hot_by_way;

    // ----------------------------------------------------------------
    // Issue Logic:

    // forwarding check
    always_comb begin
        for (int i = 0; i < BRU_IQ_ENTRIES; i++) begin
            A_forward_by_entry[i] = (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            B_forward_by_entry[i] = (B_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
        end
    end

    // ready check
    assign issue_ready_by_entry = 
        {BRU_IQ_ENTRIES{pipeline_ready}}
        &
        valid_by_entry
        &
        (A_unneeded_by_entry | A_ready_by_entry | A_forward_by_entry)
        &
        (B_unneeded_by_entry | B_ready_by_entry | B_forward_by_entry)
    ;

    // pq
    pq_lsb #(.WIDTH(BRU_IQ_ENTRIES)) ISSUE_PQ_LSB (
        .req_vec(issue_ready_by_entry),
        .ack_one_hot(issue_one_hot_by_entry),
        .ack_mask(issue_mask)
    );

    // mux
    always_comb begin

        // issue automatically valid if any entry ready
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
        issue_A_unneeded = '0;
        issue_A_forward = '0;
        issue_A_bank = '0;
        issue_B_unneeded = '0;
        issue_B_forward = '0;
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
                issue_A_unneeded |= A_unneeded_by_entry[entry];
                issue_A_forward |= A_forward_by_entry[entry];
                issue_A_bank |= A_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0];
                issue_B_unneeded |= B_unneeded_by_entry[entry];
                issue_B_forward |= B_forward_by_entry[entry];
                issue_B_bank |= B_PR_by_entry[entry][LOG_PRF_BANK_COUNT-1:0];
                issue_dest_PR |= dest_PR_by_entry[entry];
                issue_ROB_index |= ROB_index_by_entry[entry];

                PRF_req_A_valid |= ~A_forward_by_entry[entry] & ~A_unneeded_by_entry[entry];
                PRF_req_A_PR |= A_PR_by_entry[entry];
                PRF_req_B_valid |= ~B_forward_by_entry[entry] & ~B_unneeded_by_entry[entry];
                PRF_req_B_PR |= B_PR_by_entry[entry];
            end
        end
    end

    // ----------------------------------------------------------------
    // Dispatch Logic:

    // cascaded dispatch mask PQ's by way:

    // way 0
    assign dispatch_open_mask_by_way[0] = ~(valid_by_entry);
    pq_lsb #(.WIDTH(BRU_IQ_ENTRIES)) DISPATCH_WAY0_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[0]),
        .ack_one_hot(dispatch_pq_one_hot_by_way[0]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[0] = dispatch_pq_one_hot_by_way[0] & {BRU_IQ_ENTRIES{dispatch_attempt_by_way[0]}};

    // way 1
    assign dispatch_open_mask_by_way[1] = dispatch_open_mask_by_way[0] & ~dispatch_one_hot_by_way[0];
    pq_lsb #(.WIDTH(BRU_IQ_ENTRIES)) DISPATCH_WAY1_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[1]),
        .ack_one_hot(dispatch_pq_one_hot_by_way[1]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[1] = dispatch_pq_one_hot_by_way[1] & {BRU_IQ_ENTRIES{dispatch_attempt_by_way[1]}};
    
    assign dispatch_open_mask_by_way[2] = dispatch_open_mask_by_way[1] & ~dispatch_one_hot_by_way[1];
    pq_lsb #(.WIDTH(BRU_IQ_ENTRIES)) DISPATCH_WAY2_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[2]),
        .ack_one_hot(dispatch_pq_one_hot_by_way[2]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[2] = dispatch_pq_one_hot_by_way[2] & {BRU_IQ_ENTRIES{dispatch_attempt_by_way[2]}};
    
    assign dispatch_open_mask_by_way[3] = dispatch_open_mask_by_way[2] & ~dispatch_one_hot_by_way[2];
    pq_lsb #(.WIDTH(BRU_IQ_ENTRIES)) DISPATCH_WAY3_PQ_LSB (
        .req_vec(dispatch_open_mask_by_way[3]),
        .ack_one_hot(dispatch_pq_one_hot_by_way[3]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[3] = dispatch_pq_one_hot_by_way[3] & {BRU_IQ_ENTRIES{dispatch_attempt_by_way[3]}};

    // give dispatch feedback
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            dispatch_ack_by_way[way] = |dispatch_one_hot_by_way[way];
        end
    end

    // route PQ'd dispatch to entries
    always_comb begin
    
        dispatch_valid_by_entry = '0;
        dispatch_op_by_entry = '0;
        dispatch_pred_info_by_entry = '0;
        dispatch_pred_lru_by_entry = '0;
        dispatch_is_link_ra_by_entry = '0;
        dispatch_is_ret_ra_by_entry = '0;
        dispatch_PC_by_entry = '0;
        dispatch_pred_PC_by_entry = '0;
        dispatch_imm20_by_entry = '0;
        dispatch_A_PR_by_entry = '0;
        dispatch_A_unneeded_by_entry = '0;
        dispatch_A_ready_by_entry = '0;
        dispatch_B_PR_by_entry = '0;
        dispatch_B_unneeded_by_entry = '0;
        dispatch_B_ready_by_entry = '0;
        dispatch_dest_PR_by_entry = '0;
        dispatch_ROB_index_by_entry = '0;

        // one-hot mux selecting among ways at each entry
        for (int entry = 0; entry < BRU_IQ_ENTRIES; entry++) begin

            for (int way = 0; way < 4; way++) begin

                if (dispatch_one_hot_by_way[way][entry]) begin

                    dispatch_valid_by_entry[entry] |= dispatch_valid_by_way[way];
                    dispatch_op_by_entry[entry] |= dispatch_op_by_way[way];
                    dispatch_pred_info_by_entry[entry] |= dispatch_pred_info_by_way[way];
                    dispatch_pred_lru_by_entry[entry] |= dispatch_pred_lru_by_way[way];
                    dispatch_is_link_ra_by_entry[entry] |= dispatch_is_link_ra_by_way[way];
                    dispatch_is_ret_ra_by_entry[entry] |= dispatch_is_ret_ra_by_way[way];
                    dispatch_PC_by_entry[entry] |= dispatch_PC_by_way[way];
                    dispatch_pred_PC_by_entry[entry] |= dispatch_pred_PC_by_way[way];
                    dispatch_imm20_by_entry[entry] |= dispatch_imm20_by_way[way];
                    dispatch_A_PR_by_entry[entry] |= dispatch_A_PR_by_way[way];
                    dispatch_A_unneeded_by_entry[entry] |= dispatch_A_unneeded_by_way[way];
                    dispatch_A_ready_by_entry[entry] |= dispatch_A_ready_by_way[way];
                    dispatch_B_PR_by_entry[entry] |= dispatch_B_PR_by_way[way];
                    dispatch_B_unneeded_by_entry[entry] |= dispatch_B_unneeded_by_way[way];
                    dispatch_B_ready_by_entry[entry] |= dispatch_B_ready_by_way[way];
                    dispatch_dest_PR_by_entry[entry] |= dispatch_dest_PR_by_way[way];
                    dispatch_ROB_index_by_entry[entry] |= dispatch_ROB_index_by_way[way];
                end
            end
        end
    end

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
            A_unneeded_by_entry <= '0;
            A_ready_by_entry <= '0;
            B_PR_by_entry <= '0;
            B_unneeded_by_entry <= '0;
            B_ready_by_entry <= '0;
            dest_PR_by_entry <= '0;
            ROB_index_by_entry <= '0;
        end
        else begin

            // --------------------------------------------------------
            // highest entry only takes self:
                // self: [BRU_IQ_ENTRIES-1]

            // check take above -> clear entry
            if (issue_mask[BRU_IQ_ENTRIES-1]) begin
                valid_by_entry[BRU_IQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[BRU_IQ_ENTRIES-1]) begin
                    valid_by_entry[BRU_IQ_ENTRIES-1] <= valid_by_entry[BRU_IQ_ENTRIES-1];
                    op_by_entry[BRU_IQ_ENTRIES-1] <= op_by_entry[BRU_IQ_ENTRIES-1];
                    pred_info_by_entry[BRU_IQ_ENTRIES-1] <= pred_info_by_entry[BRU_IQ_ENTRIES-1];
                    pred_lru_by_entry[BRU_IQ_ENTRIES-1] <= pred_lru_by_entry[BRU_IQ_ENTRIES-1];
                    is_link_ra_by_entry[BRU_IQ_ENTRIES-1] <= is_link_ra_by_entry[BRU_IQ_ENTRIES-1];
                    is_ret_ra_by_entry[BRU_IQ_ENTRIES-1] <= is_ret_ra_by_entry[BRU_IQ_ENTRIES-1];
                    PC_by_entry[BRU_IQ_ENTRIES-1] <= PC_by_entry[BRU_IQ_ENTRIES-1];
                    pred_PC_by_entry[BRU_IQ_ENTRIES-1] <= pred_PC_by_entry[BRU_IQ_ENTRIES-1];
                    imm20_by_entry[BRU_IQ_ENTRIES-1] <= imm20_by_entry[BRU_IQ_ENTRIES-1];
                    A_PR_by_entry[BRU_IQ_ENTRIES-1] <= A_PR_by_entry[BRU_IQ_ENTRIES-1];
                    A_unneeded_by_entry[BRU_IQ_ENTRIES-1] <= A_unneeded_by_entry[BRU_IQ_ENTRIES-1];
                    A_ready_by_entry[BRU_IQ_ENTRIES-1] <= A_ready_by_entry[BRU_IQ_ENTRIES-1] | A_forward_by_entry[BRU_IQ_ENTRIES-1];
                    B_PR_by_entry[BRU_IQ_ENTRIES-1] <= B_PR_by_entry[BRU_IQ_ENTRIES-1];
                    B_unneeded_by_entry[BRU_IQ_ENTRIES-1] <= B_unneeded_by_entry[BRU_IQ_ENTRIES-1];
                    B_ready_by_entry[BRU_IQ_ENTRIES-1] <= B_ready_by_entry[BRU_IQ_ENTRIES-1] | B_forward_by_entry[BRU_IQ_ENTRIES-1];
                    dest_PR_by_entry[BRU_IQ_ENTRIES-1] <= dest_PR_by_entry[BRU_IQ_ENTRIES-1];
                    ROB_index_by_entry[BRU_IQ_ENTRIES-1] <= ROB_index_by_entry[BRU_IQ_ENTRIES-1];
                end

                // take self dispatch
                else begin
                    valid_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_valid_by_entry[BRU_IQ_ENTRIES-1];
                    op_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_op_by_entry[BRU_IQ_ENTRIES-1];
                    pred_info_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_pred_info_by_entry[BRU_IQ_ENTRIES-1];
                    pred_lru_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_pred_lru_by_entry[BRU_IQ_ENTRIES-1];
                    is_link_ra_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_is_link_ra_by_entry[BRU_IQ_ENTRIES-1];
                    is_ret_ra_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_is_ret_ra_by_entry[BRU_IQ_ENTRIES-1];
                    PC_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_PC_by_entry[BRU_IQ_ENTRIES-1];
                    pred_PC_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_pred_PC_by_entry[BRU_IQ_ENTRIES-1];
                    imm20_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_imm20_by_entry[BRU_IQ_ENTRIES-1];
                    A_PR_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_A_PR_by_entry[BRU_IQ_ENTRIES-1];
                    A_unneeded_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_A_unneeded_by_entry[BRU_IQ_ENTRIES-1];
                    A_ready_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_A_ready_by_entry[BRU_IQ_ENTRIES-1];
                    B_PR_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_B_PR_by_entry[BRU_IQ_ENTRIES-1];
                    B_unneeded_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_B_unneeded_by_entry[BRU_IQ_ENTRIES-1];
                    B_ready_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_B_ready_by_entry[BRU_IQ_ENTRIES-1];
                    dest_PR_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_dest_PR_by_entry[BRU_IQ_ENTRIES-1];
                    ROB_index_by_entry[BRU_IQ_ENTRIES-1] <= dispatch_ROB_index_by_entry[BRU_IQ_ENTRIES-1];
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
                // [BRU_IQ_ENTRIES-1] can only take self
            for (int i = 0; i <= BRU_IQ_ENTRIES-3; i++) begin

                // check take 2 above
                if (issue_mask[i]) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= valid_by_entry[i+1];
                        op_by_entry[i] <= op_by_entry[i+1];
                        pred_info_by_entry[i] <= pred_info_by_entry[i+1];
                        pred_lru_by_entry[i] <= pred_lru_by_entry[i+1];
                        is_link_ra_by_entry[i] <= is_link_ra_by_entry[i+1];
                        is_ret_ra_by_entry[i] <= is_ret_ra_by_entry[i+1];
                        PC_by_entry[i] <= PC_by_entry[i+1];
                        pred_PC_by_entry[i] <= pred_PC_by_entry[i+1];
                        imm20_by_entry[i] <= imm20_by_entry[i+1];
                        A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                        A_unneeded_by_entry[i] <= A_unneeded_by_entry[i+1];
                        A_ready_by_entry[i] <= A_ready_by_entry[i+1] | A_forward_by_entry[i+1];
                        B_PR_by_entry[i] <= B_PR_by_entry[i+1];
                        B_unneeded_by_entry[i] <= B_unneeded_by_entry[i+1];
                        B_ready_by_entry[i] <= B_ready_by_entry[i+1] | B_forward_by_entry[i+1];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i+1];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i+1];
                        op_by_entry[i] <= dispatch_op_by_entry[i+1];
                        pred_info_by_entry[i] <= dispatch_pred_info_by_entry[i+1];
                        pred_lru_by_entry[i] <= dispatch_pred_lru_by_entry[i+1];
                        is_link_ra_by_entry[i] <= dispatch_is_link_ra_by_entry[i+1];
                        is_ret_ra_by_entry[i] <= dispatch_is_ret_ra_by_entry[i+1];
                        PC_by_entry[i] <= dispatch_PC_by_entry[i+1];
                        pred_PC_by_entry[i] <= dispatch_pred_PC_by_entry[i+1];
                        imm20_by_entry[i] <= dispatch_imm20_by_entry[i+1];
                        A_PR_by_entry[i] <= dispatch_A_PR_by_entry[i+1];
                        A_unneeded_by_entry[i] <= dispatch_A_unneeded_by_entry[i+1];
                        A_ready_by_entry[i] <= dispatch_A_ready_by_entry[i+1];
                        B_PR_by_entry[i] <= dispatch_B_PR_by_entry[i+1];
                        B_unneeded_by_entry[i] <= dispatch_B_unneeded_by_entry[i+1];
                        B_ready_by_entry[i] <= dispatch_B_ready_by_entry[i+1];
                        dest_PR_by_entry[i] <= dispatch_dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= dispatch_ROB_index_by_entry[i+1];
                    end
                end

                // otherwise take self
                else begin

                    // take self valid entry
                    if (valid_by_entry[i]) begin
                        valid_by_entry[i] <= valid_by_entry[i];
                        op_by_entry[i] <= op_by_entry[i];
                        pred_info_by_entry[i] <= pred_info_by_entry[i];
                        pred_lru_by_entry[i] <= pred_lru_by_entry[i];
                        is_link_ra_by_entry[i] <= is_link_ra_by_entry[i];
                        is_ret_ra_by_entry[i] <= is_ret_ra_by_entry[i];
                        PC_by_entry[i] <= PC_by_entry[i];
                        pred_PC_by_entry[i] <= pred_PC_by_entry[i];
                        imm20_by_entry[i] <= imm20_by_entry[i];
                        A_PR_by_entry[i] <= A_PR_by_entry[i];
                        A_unneeded_by_entry[i] <= A_unneeded_by_entry[i];
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | A_forward_by_entry[i];
                        B_PR_by_entry[i] <= B_PR_by_entry[i];
                        B_unneeded_by_entry[i] <= B_unneeded_by_entry[i];
                        B_ready_by_entry[i] <= B_ready_by_entry[i] | B_forward_by_entry[i];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];
                    end

                    // take self dispatch
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        op_by_entry[i] <= dispatch_op_by_entry[i];
                        pred_info_by_entry[i] <= dispatch_pred_info_by_entry[i];
                        pred_lru_by_entry[i] <= dispatch_pred_lru_by_entry[i];
                        is_link_ra_by_entry[i] <= dispatch_is_link_ra_by_entry[i];
                        is_ret_ra_by_entry[i] <= dispatch_is_ret_ra_by_entry[i];
                        PC_by_entry[i] <= dispatch_PC_by_entry[i];
                        pred_PC_by_entry[i] <= dispatch_pred_PC_by_entry[i];
                        imm20_by_entry[i] <= dispatch_imm20_by_entry[i];
                        A_PR_by_entry[i] <= dispatch_A_PR_by_entry[i];
                        A_unneeded_by_entry[i] <= dispatch_A_unneeded_by_entry[i];
                        A_ready_by_entry[i] <= dispatch_A_ready_by_entry[i];
                        B_PR_by_entry[i] <= dispatch_B_PR_by_entry[i];
                        B_unneeded_by_entry[i] <= dispatch_B_unneeded_by_entry[i];
                        B_ready_by_entry[i] <= dispatch_B_ready_by_entry[i];
                        dest_PR_by_entry[i] <= dispatch_dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= dispatch_ROB_index_by_entry[i];
                    end
                end
            end
        end
    end

endmodule