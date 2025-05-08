/*
    Filename: alu_reg_mdu_dq.sv
    Author: zlagpacan
    Description: RTL for ALU Reg-Reg + Mul-Div Unit Dispatch Queue
    Spec: LOROF/spec/design/alu_reg_mdu_dq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_mdu_dq #(
    parameter ALU_REG_MDU_DQ_ENTRIES = 4
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
    input logic [3:0]                       dispatch_attempt_by_way,
    input logic [3:0]                       dispatch_valid_alu_reg_by_way,
    input logic [3:0]                       dispatch_valid_mdu_by_way,
    input logic [3:0][3:0]                  dispatch_op_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_A_PR_by_way,
    input logic [3:0]                       dispatch_A_ready_by_way,
    input logic [3:0]                       dispatch_A_is_zero_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_B_PR_by_way,
    input logic [3:0]                       dispatch_B_ready_by_way,
    input logic [3:0]                       dispatch_B_is_zero_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_dest_PR_by_way,
    input logic [3:0][LOG_ROB_ENTRIES-1:0]  dispatch_ROB_index_by_way,

    // op dispatch feedback
    output logic [3:0] dispatch_ack_by_way,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // op enqueue to issue queue
    output logic                        iq_enq_valid,
    output logic                        iq_enq_is_alu_reg,
    output logic                        iq_enq_is_mdu,
    output logic [3:0]                  iq_enq_op,
    output logic [LOG_PR_COUNT-1:0]     iq_enq_A_PR,
    output logic                        iq_enq_A_ready,
    output logic                        iq_enq_A_is_zero,
    output logic [LOG_PR_COUNT-1:0]     iq_enq_B_PR,
    output logic                        iq_enq_B_ready,
    output logic                        iq_enq_B_is_zero,
    output logic [LOG_PR_COUNT-1:0]     iq_enq_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  iq_enq_ROB_index,

    // issue queue enqueue feedback
    input logic                         iq_enq_ready
);

    // ----------------------------------------------------------------
    // Signals:

    // DQ entries
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          valid_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          is_alu_reg_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          is_mdu_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][3:0]                     op_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        A_PR_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          A_ready_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          A_is_zero_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        B_PR_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          B_ready_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          B_is_zero_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dest_PR_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]     ROB_index_by_entry;

    // new ready check
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0] new_A_ready_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0] new_B_ready_by_entry;

    // incoming dispatch crossbar by entry
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          dispatch_valid_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          dispatch_is_alu_reg_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          dispatch_is_mdu_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][3:0]                     dispatch_op_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dispatch_A_PR_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          dispatch_A_ready_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          dispatch_A_is_zero_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dispatch_B_PR_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          dispatch_B_ready_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0]                          dispatch_B_is_zero_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dispatch_dest_PR_by_entry;
    logic [ALU_REG_MDU_DQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]     dispatch_ROB_index_by_entry;

    // incoming dispatch req masks for each of 4 possible dispatch ways
    logic [3:0][ALU_REG_MDU_DQ_ENTRIES-1:0] dispatch_open_mask_by_way;
    logic [3:0][ALU_REG_MDU_DQ_ENTRIES-1:0] dispatch_pe_one_hot_by_way;
    logic [3:0][ALU_REG_MDU_DQ_ENTRIES-1:0] dispatch_one_hot_by_way;

    // launching
    logic launching;

    // ----------------------------------------------------------------
    // Launch Logic:

    assign launching = valid_by_entry[0] & iq_enq_ready;

    // new ready check
    always_comb begin
        for (int i = 0; i < ALU_REG_MDU_DQ_ENTRIES; i++) begin
            new_A_ready_by_entry[i] = (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            new_B_ready_by_entry[i] = (B_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) & WB_bus_valid_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
        end
    end

    // launch from lowest DQ entry
    always_comb begin
        iq_enq_valid = launching;
        iq_enq_is_alu_reg = is_alu_reg_by_entry[0];
        iq_enq_is_mdu = is_mdu_by_entry[0];
        iq_enq_op = op_by_entry[0];
        iq_enq_A_PR = A_PR_by_entry[0];
        iq_enq_A_ready = A_ready_by_entry[0] | new_A_ready_by_entry[0];
        iq_enq_A_is_zero = A_is_zero_by_entry[0];
        iq_enq_B_PR = B_PR_by_entry[0];
        iq_enq_B_ready = B_ready_by_entry[0] | new_B_ready_by_entry[0];
        iq_enq_B_is_zero = B_is_zero_by_entry[0];
        iq_enq_dest_PR = dest_PR_by_entry[0];
        iq_enq_ROB_index = ROB_index_by_entry[0];
    end

    // ----------------------------------------------------------------
    // Dispatch Logic:

    // way 0
    assign dispatch_open_mask_by_way[0] = ~valid_by_entry;
    pe_lsb #(.WIDTH(ALU_REG_MDU_DQ_ENTRIES)) DISPATCH_WAY0_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[0]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[0]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[0] = dispatch_pe_one_hot_by_way[0] & {ALU_REG_MDU_DQ_ENTRIES{dispatch_attempt_by_way[0]}};

    // way 1
    assign dispatch_open_mask_by_way[1] = dispatch_open_mask_by_way[0] & ~dispatch_one_hot_by_way[0];
    pe_lsb #(.WIDTH(ALU_REG_MDU_DQ_ENTRIES)) DISPATCH_WAY1_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[1]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[1]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[1] = dispatch_pe_one_hot_by_way[1] & {ALU_REG_MDU_DQ_ENTRIES{dispatch_attempt_by_way[1]}};
    
    assign dispatch_open_mask_by_way[2] = dispatch_open_mask_by_way[1] & ~dispatch_one_hot_by_way[1];
    pe_lsb #(.WIDTH(ALU_REG_MDU_DQ_ENTRIES)) DISPATCH_WAY2_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[2]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[2]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[2] = dispatch_pe_one_hot_by_way[2] & {ALU_REG_MDU_DQ_ENTRIES{dispatch_attempt_by_way[2]}};
    
    assign dispatch_open_mask_by_way[3] = dispatch_open_mask_by_way[2] & ~dispatch_one_hot_by_way[2];
    pe_lsb #(.WIDTH(ALU_REG_MDU_DQ_ENTRIES)) DISPATCH_WAY3_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[3]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[3]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[3] = dispatch_pe_one_hot_by_way[3] & {ALU_REG_MDU_DQ_ENTRIES{dispatch_attempt_by_way[3]}};

    // give dispatch feedback
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            dispatch_ack_by_way[way] = |(dispatch_open_mask_by_way[way] & {ALU_REG_MDU_DQ_ENTRIES{dispatch_attempt_by_way[way]}});
        end
    end

    // route PE'd dispatch to entries
    always_comb begin

        dispatch_valid_by_entry = '0;
        dispatch_is_alu_reg_by_entry = '0;
        dispatch_is_mdu_by_entry = '0;
        dispatch_op_by_entry = '0;
        dispatch_A_PR_by_entry = '0;
        dispatch_A_ready_by_entry = '0;
        dispatch_A_is_zero_by_entry = '0;
        dispatch_B_PR_by_entry = '0;
        dispatch_B_ready_by_entry = '0;
        dispatch_B_is_zero_by_entry = '0;
        dispatch_dest_PR_by_entry = '0;
        dispatch_ROB_index_by_entry = '0;

        // one-hot mux selecting among ways at each entry
        for (int entry = 0; entry < ALU_REG_MDU_DQ_ENTRIES; entry++) begin

            for (int way = 0; way < 4; way++) begin

                if (dispatch_one_hot_by_way[way][entry]) begin

                    dispatch_valid_by_entry[entry] |= dispatch_valid_alu_reg_by_way[way] | dispatch_valid_mdu_by_way[way];
                    dispatch_is_alu_reg_by_entry[entry] |= dispatch_valid_alu_reg_by_way[way];
                    dispatch_is_mdu_by_entry[entry] |= dispatch_valid_mdu_by_way[way];
                    dispatch_op_by_entry[entry] |= dispatch_op_by_way[way];
                    dispatch_A_PR_by_entry[entry] |= dispatch_A_PR_by_way[way];
                    dispatch_A_ready_by_entry[entry] |= dispatch_A_ready_by_way[way];
                    dispatch_A_is_zero_by_entry[entry] |= dispatch_A_is_zero_by_way[way];
                    dispatch_B_PR_by_entry[entry] |= dispatch_B_PR_by_way[way];
                    dispatch_B_ready_by_entry[entry] |= dispatch_B_ready_by_way[way];
                    dispatch_B_is_zero_by_entry[entry] |= dispatch_B_is_zero_by_way[way];
                    dispatch_dest_PR_by_entry[entry] |= dispatch_dest_PR_by_way[way];
                    dispatch_ROB_index_by_entry[entry] |= dispatch_ROB_index_by_way[way];
                end
            end
        end
    end

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
                // self: [ALU_REG_MDU_DQ_ENTRIES-1]

            // check launch -> clear entry
            if (launching) begin
                valid_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[ALU_REG_MDU_DQ_ENTRIES-1]) begin
                    valid_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= 1'b1;
                    is_alu_reg_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= is_alu_reg_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    is_mdu_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= is_mdu_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    op_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= op_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    A_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= A_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    A_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= A_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] | new_A_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    A_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= A_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    B_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= B_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    B_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= B_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] | new_B_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    B_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= B_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    dest_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dest_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    ROB_index_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= ROB_index_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                end

                // take self dispatch
                else begin
                    valid_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_valid_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    is_alu_reg_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_is_alu_reg_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    is_mdu_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_is_mdu_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    op_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_op_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    A_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_A_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    A_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_A_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] | new_A_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    A_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_A_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    B_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_B_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    B_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_B_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] | new_B_ready_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    B_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_B_is_zero_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    dest_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_dest_PR_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                    ROB_index_by_entry[ALU_REG_MDU_DQ_ENTRIES-1] <= dispatch_ROB_index_by_entry[ALU_REG_MDU_DQ_ENTRIES-1];
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
            for (int i = 0; i <= ALU_REG_MDU_DQ_ENTRIES-2; i++) begin

                // check launch -> take above
                if (launching) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= 1'b1;
                        is_alu_reg_by_entry[i] <= is_alu_reg_by_entry[i+1];
                        is_mdu_by_entry[i] <= is_mdu_by_entry[i+1];
                        op_by_entry[i] <= op_by_entry[i+1];
                        A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= A_ready_by_entry[i+1] | new_A_ready_by_entry[i+1];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i+1];
                        B_PR_by_entry[i] <= B_PR_by_entry[i+1];
                        B_ready_by_entry[i] <= B_ready_by_entry[i+1] | new_B_ready_by_entry[i+1];
                        B_is_zero_by_entry[i] <= B_is_zero_by_entry[i+1];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i+1];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i+1];
                        is_alu_reg_by_entry[i] <= dispatch_is_alu_reg_by_entry[i+1];
                        is_mdu_by_entry[i] <= dispatch_is_mdu_by_entry[i+1];
                        op_by_entry[i] <= dispatch_op_by_entry[i+1];
                        A_PR_by_entry[i] <= dispatch_A_PR_by_entry[i+1];
                        A_ready_by_entry[i] <= dispatch_A_ready_by_entry[i+1];
                        A_is_zero_by_entry[i] <= dispatch_A_is_zero_by_entry[i+1];
                        B_PR_by_entry[i] <= dispatch_B_PR_by_entry[i+1];
                        B_ready_by_entry[i] <= dispatch_B_ready_by_entry[i+1];
                        B_is_zero_by_entry[i] <= dispatch_B_is_zero_by_entry[i+1];
                        dest_PR_by_entry[i] <= dispatch_dest_PR_by_entry[i+1];
                        ROB_index_by_entry[i] <= dispatch_ROB_index_by_entry[i+1];
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
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | new_A_ready_by_entry[i];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i];
                        B_PR_by_entry[i] <= B_PR_by_entry[i];
                        B_ready_by_entry[i] <= B_ready_by_entry[i] | new_B_ready_by_entry[i];
                        B_is_zero_by_entry[i] <= B_is_zero_by_entry[i];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];
                    end

                    // take self dispatch
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        is_alu_reg_by_entry[i] <= dispatch_is_alu_reg_by_entry[i];
                        is_mdu_by_entry[i] <= dispatch_is_mdu_by_entry[i];
                        op_by_entry[i] <= dispatch_op_by_entry[i];
                        A_PR_by_entry[i] <= dispatch_A_PR_by_entry[i];
                        A_ready_by_entry[i] <= dispatch_A_ready_by_entry[i];
                        A_is_zero_by_entry[i] <= dispatch_A_is_zero_by_entry[i];
                        B_PR_by_entry[i] <= dispatch_B_PR_by_entry[i];
                        B_ready_by_entry[i] <= dispatch_B_ready_by_entry[i];
                        B_is_zero_by_entry[i] <= dispatch_B_is_zero_by_entry[i];
                        dest_PR_by_entry[i] <= dispatch_dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= dispatch_ROB_index_by_entry[i];
                    end
                end
            end
        end
    end

endmodule