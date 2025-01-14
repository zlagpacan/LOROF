/*
    Filename: alu_imm_dq.sv
    Author: zlagpacan
    Description: RTL for ALU Register-Immediate Dispatch Queue
    Spec: LOROF/spec/design/alu_imm_dq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_dq (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU op 4-wide enQ array
    input logic [3:0]                       enQ_valid_array,
    input logic [3:0][3:0]                  enQ_op_array,
    input logic [3:0][31:0]                 enQ_imm_array,
    input logic [3:0][LOG_PR_COUNT-1:0]     enQ_A_PR_array,
    input logic [3:0]                       enQ_A_unneeded_array,
    input logic [3:0][LOG_PR_COUNT-1:0]     enQ_dest_PR_array,
    input logic [3:0][LOG_ROB_ENTRIES-1:0]  enQ_ROB_index_array,

    // ALU op 4-wide enQ feedback array
    output logic [3:0] enQ_ready_array,

    // ALU op 4-wide deQ array
    output logic [3:0]                          deQ_valid_array,
    output logic [3:0][3:0]                     deQ_op_array,
    output logic [3:0][31:0]                    deQ_imm_array,
    output logic [3:0]                          deQ_A_unneeded_array,
    output logic [3:0][LOG_PR_COUNT-1:0]        deQ_A_PR_array,
    output logic [3:0][LOG_PR_COUNT-1:0]        deQ_dest_PR_array,
    output logic [3:0][LOG_ROB_ENTRIES-1:0]     deQ_ROB_index_array,

    // ALU op 4-wide deQ feedback array
    input logic [3:0] deQ_ready_array
);

    // ----------------------------------------------------------------
    // Signals:

    // DQ entries
    logic [DQ_ENTRIES-1:0]                          valid_by_entry;
    logic [DQ_ENTRIES-1:0][3:0]                     op_by_entry;
    logic [DQ_ENTRIES-1:0][31:0]                    imm_by_entry;
    logic [DQ_ENTRIES-1:0]                          A_unneeded_by_entry;
    logic [DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        A_PR_by_entry;
    logic [DQ_ENTRIES-1:0][LOG_PR_COUNT-1:0]        dest_PR_by_entry;
    logic [DQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]     ROB_index_by_entry;

    // DQ ptr's
    typedef logic [LOG_DQ_ENTRIES-1:0] DQ_idx_t;

    // DQ array helper signals
    DQ_idx_t [3:0] enQ_idx_array, next_enQ_idx_array;
    DQ_idx_t [3:0] deQ_idx_array, next_deQ_idx_array;

    logic [3:0] enQ_accepted_array;
    logic [2:0] enQ_idx_delta;
    logic [3:0] deQ_accepted_array;
    logic [2:0] deQ_idx_delta;

    // ----------------------------------------------------------------
    // Logic:

    always_comb begin

        // advertised enQ ready
        for (int i = 0; i < 4; i++) begin
            enQ_ready_array[i] = ~valid_by_entry[enQ_idx_array[i]];
        end

        // advertised deQ
        for (int i = 0; i < 4; i++) begin
            deQ_valid_array[i] = valid_by_entry[deQ_idx_array[i]];
            deQ_op_array[i] = op_by_entry[deQ_idx_array[i]];
            deQ_imm_array[i] = imm_by_entry[deQ_idx_array[i]];
            deQ_A_unneeded_array[i] = A_unneeded_by_entry[deQ_idx_array[i]];
            deQ_A_PR_array[i] = A_PR_by_entry[deQ_idx_array[i]];
            deQ_dest_PR_array[i] = dest_PR_by_entry[deQ_idx_array[i]];
            deQ_ROB_index_array[i] = ROB_index_by_entry[deQ_idx_array[i]];
        end

        // accept enQ's
        enQ_accepted_array = enQ_ready_array & enQ_valid_array;

        // calculate next enQ idx
        if (enQ_accepted_array[3]) begin
            enQ_idx_delta = 4;
        end
        else if (enQ_accepted_array[2]) begin
            enQ_idx_delta = 3;
        end
        else if (enQ_accepted_array[1]) begin
            enQ_idx_delta = 2;
        end
        else if (enQ_accepted_array[0]) begin
            enQ_idx_delta = 1;
        end
        else begin
            enQ_idx_delta = 0;
        end
        for (int i = 0; i < 4; i++) begin
            next_enQ_idx_array[i] = enQ_idx_array[i] + enQ_idx_delta;
        end

        // accept deQ's
        deQ_accepted_array = deQ_ready_array & deQ_valid_array;

        // calculate next deQ idx
        if (deQ_accepted_array[3]) begin
            deQ_idx_delta = 4;
        end
        else if (deQ_accepted_array[2]) begin
            deQ_idx_delta = 3;
        end
        else if (deQ_accepted_array[1]) begin
            deQ_idx_delta = 2;
        end
        else if (deQ_accepted_array[0]) begin
            deQ_idx_delta = 1;
        end
        else begin
            deQ_idx_delta = 0;
        end
        for (int i = 0; i < 4; i++) begin
            next_deQ_idx_array[i] = deQ_idx_array[i] + deQ_idx_delta;
        end
    end

    // DQ entry reg logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_by_entry <= '0;
            op_by_entry <= '0;
            imm_by_entry <= '0;
            A_unneeded_by_entry <= '0;
            A_PR_by_entry <= '0;
            dest_PR_by_entry <= '0;
            ROB_index_by_entry <= '0;
        end
        else begin
            // perform enQ's
            for (int i = 0; i < 4; i++) begin
                if (enQ_ready_array[i]) begin
                    valid_by_entry[enQ_idx_array[i]] <= enQ_valid_array[i];
                    op_by_entry[enQ_idx_array[i]] <= enQ_op_array[i];
                    imm_by_entry[enQ_idx_array[i]] <= enQ_imm_array[i];
                    A_unneeded_by_entry[enQ_idx_array[i]] <= enQ_A_unneeded_array[i];
                    A_PR_by_entry[enQ_idx_array[i]] <= enQ_A_PR_array[i];
                    dest_PR_by_entry[enQ_idx_array[i]] <= enQ_dest_PR_array[i];
                    ROB_index_by_entry[enQ_idx_array[i]] <= enQ_ROB_index_array[i];
                end
            end
            for (int i = 0; i < 4; i++) begin
                if (deQ_accepted_array[i]) begin
                    valid_by_entry[enQ_idx_array[i]] <= 1'b0;
                end
            end
        end
    end

    // idx reg logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            for (int i = 0; i < 4; i++) begin
                enQ_idx_array[i] <= i;
                deQ_idx_array[i] <= i;
            end
        end
        else begin
            enQ_idx_array <= next_enQ_idx_array;
            deQ_idx_array <= next_deQ_idx_array;
        end
    end

endmodule