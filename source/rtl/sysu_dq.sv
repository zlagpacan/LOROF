/*
    Filename: sysu_dq.sv
    Author: zlagpacan
    Description: RTL for System Unit Dispatch Queue
    Spec: LOROF/spec/design/sysu_dq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module sysu_dq #(
    parameter SYSU_DQ_ENTRIES = 4
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op dispatch by way
    input logic [3:0]                       dispatch_attempt_by_way,
    input logic [3:0]                       dispatch_valid_by_way,
    input logic [3:0][3:0]                  dispatch_op_by_way,
    input logic [3:0][11:0]                 dispatch_imm12_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_A_PR_by_way,
    input logic [3:0]                       dispatch_A_ready_by_way,
    input logic [3:0]                       dispatch_A_is_zero_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_B_PR_by_way,
    input logic [3:0]                       dispatch_B_ready_by_way,
    input logic [3:0]                       dispatch_B_is_zero_by_way,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_dest_PR_by_way,
    input logic [3:0][LOG_ROB_ENTRIES-1:0]  dispatch_ROB_index_by_way,

    // op dispatch feedback
    output logic [3:0]                      dispatch_ack_by_way,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

    // op launch to sysu
    output logic                        sysu_launch_valid,
    output logic                        sysu_launch_killed,
    output logic [3:0]                  sysu_launch_op,
    output logic [11:0]                 sysu_launch_imm12,
    output logic [LOG_PR_COUNT-1:0]     sysu_launch_A_PR,
    output logic                        sysu_launch_A_is_zero,
    output logic [LOG_PR_COUNT-1:0]     sysu_launch_B_PR,
    output logic                        sysu_launch_B_is_zero,
    output logic [LOG_PR_COUNT-1:0]     sysu_launch_dest_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  sysu_launch_ROB_index,

    // sysu launch feedback
    input logic                         sysu_launch_ready,

    // ROB kill
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_abs_head_index,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index
);

    // instr support
        // C.EBREAK, ECALL, EBREAK, SRET, WFI, MRET
        // CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI

    // don't need A/B_unneeded from decode as can simply check op bits
        // need A: op[0] | op[1]
        // need B: ~op[2] & (op[0] | op[1])

    // ----------------------------------------------------------------
    // Signals:

    // DQ entries
    logic [SYSU_DQ_ENTRIES-1:0]                         valid_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         killed_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][3:0]                    op_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][11:0]                   imm12_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       A_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         A_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         A_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       B_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         B_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         B_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dest_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]    ROB_index_by_entry;

    // new ready check
    logic [SYSU_DQ_ENTRIES-1:0] new_A_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0] new_B_ready_by_entry;

    // new kill check
    logic [SYSU_DQ_ENTRIES-1:0] new_killed_by_entry;

    // incoming dispatch crossbar by entry
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_attempt_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_valid_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][3:0]                    dispatch_op_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][11:0]                   dispatch_imm12_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dispatch_A_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_A_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_A_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dispatch_B_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_B_ready_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0]                         dispatch_B_is_zero_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]       dispatch_dest_PR_by_entry;
    logic [SYSU_DQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]    dispatch_ROB_index_by_entry;

    // incoming dispatch req masks for each of 4 possible dispatch ways
    logic [3:0][SYSU_DQ_ENTRIES-1:0] dispatch_open_mask_by_way;
    logic [3:0][SYSU_DQ_ENTRIES-1:0] dispatch_pe_one_hot_by_way;
    logic [3:0][SYSU_DQ_ENTRIES-1:0] dispatch_one_hot_by_way;

    // launching
    logic A_ready_at_0;
    logic B_ready_at_0;
    logic launching;

    // ----------------------------------------------------------------
    // Launch Logic:

    assign A_ready_at_0 = 
        (op_by_entry[0][1:0] == 2'b00)
        | A_ready_by_entry[0]
        | new_A_ready_by_entry[0]
        | A_is_zero_by_entry[0];

    assign B_ready_at_0 = 
        (op_by_entry[0][1:0] == 2'b00)
        | op_by_entry[0][2]
        | A_ready_by_entry[0]
        | new_A_ready_by_entry[0]
        | A_is_zero_by_entry[0];

    assign launching = 
        valid_by_entry[0]
        & sysu_launch_ready
        & A_ready_at_0
        & B_ready_at_0;

    // new ready and killed checks
    always_comb begin
        for (int i = 0; i < SYSU_DQ_ENTRIES; i++) begin
            new_A_ready_by_entry[i] = 
                (A_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) 
                & WB_bus_valid_by_bank[A_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];
            new_B_ready_by_entry[i] = 
                (B_PR_by_entry[i][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT] == WB_bus_upper_PR_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]]) 
                & WB_bus_valid_by_bank[B_PR_by_entry[i][LOG_PRF_BANK_COUNT-1:0]];

            new_killed_by_entry[i] = rob_kill_valid & 
                (ROB_index_by_entry[i] - rob_kill_abs_head_index) >= rob_kill_rel_kill_younger_index;
        end
    end

    // launch from lowest DQ entry
    always_comb begin
        sysu_launch_valid = launching;
        sysu_launch_killed = killed_by_entry[0] | new_killed_by_entry[0];
        sysu_launch_op = op_by_entry[0];
        sysu_launch_imm12 = imm12_by_entry[0];
        sysu_launch_A_PR = A_PR_by_entry[0];
        sysu_launch_A_is_zero = A_is_zero_by_entry[0];
        sysu_launch_B_PR = B_PR_by_entry[0];
        sysu_launch_B_is_zero = B_is_zero_by_entry[0];
        sysu_launch_dest_PR = dest_PR_by_entry[0];
        sysu_launch_ROB_index = ROB_index_by_entry[0];
    end

    // ----------------------------------------------------------------
    // Dispatch Logic:

    // way 0
    assign dispatch_open_mask_by_way[0] = ~valid_by_entry;
    pe_lsb #(.WIDTH(SYSU_DQ_ENTRIES)) DISPATCH_WAY0_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[0]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[0]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[0] = dispatch_pe_one_hot_by_way[0] & {SYSU_DQ_ENTRIES{dispatch_attempt_by_way[0]}};

    // way 1
    assign dispatch_open_mask_by_way[1] = dispatch_open_mask_by_way[0] & ~dispatch_one_hot_by_way[0];
    pe_lsb #(.WIDTH(SYSU_DQ_ENTRIES)) DISPATCH_WAY1_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[1]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[1]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[1] = dispatch_pe_one_hot_by_way[1] & {SYSU_DQ_ENTRIES{dispatch_attempt_by_way[1]}};
    
    assign dispatch_open_mask_by_way[2] = dispatch_open_mask_by_way[1] & ~dispatch_one_hot_by_way[1];
    pe_lsb #(.WIDTH(SYSU_DQ_ENTRIES)) DISPATCH_WAY2_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[2]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[2]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[2] = dispatch_pe_one_hot_by_way[2] & {SYSU_DQ_ENTRIES{dispatch_attempt_by_way[2]}};
    
    assign dispatch_open_mask_by_way[3] = dispatch_open_mask_by_way[2] & ~dispatch_one_hot_by_way[2];
    pe_lsb #(.WIDTH(SYSU_DQ_ENTRIES)) DISPATCH_WAY3_PE_LSB (
        .req_vec(dispatch_open_mask_by_way[3]),
        .ack_one_hot(dispatch_pe_one_hot_by_way[3]),
        .ack_mask() // unused
    );
    assign dispatch_one_hot_by_way[3] = dispatch_pe_one_hot_by_way[3] & {SYSU_DQ_ENTRIES{dispatch_attempt_by_way[3]}};

    // give dispatch feedback
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            dispatch_ack_by_way[way] = |(dispatch_open_mask_by_way[way] & {SYSU_DQ_ENTRIES{dispatch_attempt_by_way[way]}});
        end
    end

    // route PE'd dispatch to entries
    always_comb begin

        dispatch_valid_by_entry = '0;
        dispatch_op_by_entry = '0;
        dispatch_imm12_by_entry = '0;
        dispatch_A_PR_by_entry = '0;
        dispatch_A_ready_by_entry = '0;
        dispatch_A_is_zero_by_entry = '0;
        dispatch_B_PR_by_entry = '0;
        dispatch_B_ready_by_entry = '0;
        dispatch_B_is_zero_by_entry = '0;
        dispatch_dest_PR_by_entry = '0;
        dispatch_ROB_index_by_entry = '0;

        // one-hot mux selecting among ways at each entry
        for (int entry = 0; entry < SYSU_DQ_ENTRIES; entry++) begin

            for (int way = 0; way < 4; way++) begin

                if (dispatch_one_hot_by_way[way][entry]) begin

                    dispatch_valid_by_entry[entry] |= dispatch_valid_by_way[way];
                    dispatch_op_by_entry[entry] |= dispatch_op_by_way[way];
                    dispatch_imm12_by_entry[entry] |= dispatch_imm12_by_way[way];
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
            killed_by_entry <= '0;
            op_by_entry <= '0;
            imm12_by_entry <= '0;
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
                // self: [SYSU_DQ_ENTRIES-1]

            // check launch -> clear entry
            if (launching) begin
                valid_by_entry[SYSU_DQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[SYSU_DQ_ENTRIES-1]) begin
                    valid_by_entry[SYSU_DQ_ENTRIES-1] <= 1'b1;
                    killed_by_entry[SYSU_DQ_ENTRIES-1] <= killed_by_entry[SYSU_DQ_ENTRIES-1];
                    op_by_entry[SYSU_DQ_ENTRIES-1] <= op_by_entry[SYSU_DQ_ENTRIES-1];
                    imm12_by_entry[SYSU_DQ_ENTRIES-1] <= imm12_by_entry[SYSU_DQ_ENTRIES-1];
                    A_PR_by_entry[SYSU_DQ_ENTRIES-1] <= A_PR_by_entry[SYSU_DQ_ENTRIES-1];
                    A_ready_by_entry[SYSU_DQ_ENTRIES-1] <= A_ready_by_entry[SYSU_DQ_ENTRIES-1];
                    A_is_zero_by_entry[SYSU_DQ_ENTRIES-1] <= A_is_zero_by_entry[SYSU_DQ_ENTRIES-1];
                    B_PR_by_entry[SYSU_DQ_ENTRIES-1] <= B_PR_by_entry[SYSU_DQ_ENTRIES-1];
                    B_ready_by_entry[SYSU_DQ_ENTRIES-1] <= B_ready_by_entry[SYSU_DQ_ENTRIES-1];
                    B_is_zero_by_entry[SYSU_DQ_ENTRIES-1] <= B_is_zero_by_entry[SYSU_DQ_ENTRIES-1];
                    dest_PR_by_entry[SYSU_DQ_ENTRIES-1] <= dest_PR_by_entry[SYSU_DQ_ENTRIES-1];
                    ROB_index_by_entry[SYSU_DQ_ENTRIES-1] <= ROB_index_by_entry[SYSU_DQ_ENTRIES-1];
                end

                // take self dispatch
                else begin
                    valid_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_valid_by_entry[SYSU_DQ_ENTRIES-1];
                    killed_by_entry[SYSU_DQ_ENTRIES-1] <= 1'b0;
                    op_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_op_by_entry[SYSU_DQ_ENTRIES-1];
                    imm12_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_imm12_by_entry[SYSU_DQ_ENTRIES-1];
                    A_PR_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_A_PR_by_entry[SYSU_DQ_ENTRIES-1];
                    A_ready_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_A_ready_by_entry[SYSU_DQ_ENTRIES-1];
                    A_is_zero_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_A_is_zero_by_entry[SYSU_DQ_ENTRIES-1];
                    B_PR_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_B_PR_by_entry[SYSU_DQ_ENTRIES-1];
                    B_ready_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_B_ready_by_entry[SYSU_DQ_ENTRIES-1];
                    B_is_zero_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_B_is_zero_by_entry[SYSU_DQ_ENTRIES-1];
                    dest_PR_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_dest_PR_by_entry[SYSU_DQ_ENTRIES-1];
                    ROB_index_by_entry[SYSU_DQ_ENTRIES-1] <= dispatch_ROB_index_by_entry[SYSU_DQ_ENTRIES-1];
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
            for (int i = 0; i <= SYSU_DQ_ENTRIES-2; i++) begin

                // check launch -> take above
                if (launching) begin
                    
                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= 1'b1;
                        killed_by_entry[i] <= killed_by_entry[i+1] | new_killed_by_entry[i+1];
                        op_by_entry[i] <= op_by_entry[i+1];
                        imm12_by_entry[i] <= imm12_by_entry[i+1];
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
                        killed_by_entry[i] <= 1'b0;
                        op_by_entry[i] <= dispatch_op_by_entry[i+1];
                        imm12_by_entry[i] <= dispatch_imm12_by_entry[i+1];
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
                        killed_by_entry[i] <= killed_by_entry[i] | new_killed_by_entry[i];
                        op_by_entry[i] <= op_by_entry[i];
                        imm12_by_entry[i] <= imm12_by_entry[i];
                        A_PR_by_entry[i] <= A_PR_by_entry[i];
                        A_ready_by_entry[i] <= A_ready_by_entry[i] | new_A_ready_by_entry[i];
                        A_is_zero_by_entry[i] <= A_is_zero_by_entry[i];
                        B_PR_by_entry[i] <= B_PR_by_entry[i];
                        B_ready_by_entry[i] <= B_ready_by_entry[i] | new_B_ready_by_entry[i];
                        B_is_zero_by_entry[i] <= B_is_zero_by_entry[i];
                        dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];
                    end

                    // take dispatch above
                    else begin
                        valid_by_entry[i] <= dispatch_valid_by_entry[i];
                        killed_by_entry[i] <= 1'b0;
                        op_by_entry[i] <= dispatch_op_by_entry[i];
                        imm12_by_entry[i] <= dispatch_imm12_by_entry[i];
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