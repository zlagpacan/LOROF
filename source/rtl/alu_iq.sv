/*
    Filename: alu_iq.sv
    Author: zlagpacan
    Description: RTL for ALU Issue Queue
    Spec: LOROF/spec/design/alu_iq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_iq (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU op dispatch by entry
    input logic [3:0]                       dispatch_valid_by_entry,
    input logic [3:0][3:0]                  dispatch_op_by_entry,
    input logic [3:0][31:0]                 dispatch_imm_by_entry,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_A_PR_by_entry,
    input logic [3:0]                       dispatch_A_unneeded_by_entry,
    input logic [3:0]                       dispatch_A_ready_by_entry,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_B_PR_by_entry,
    input logic [3:0]                       dispatch_is_imm_by_entry,
    input logic [3:0]                       dispatch_B_ready_by_entry,
    input logic [3:0][LOG_PR_COUNT-1:0]     dispatch_dest_PR_by_entry,

    // writeback bus
    input logic [LOG_PRF_BANK_COUNT-1:0]                                        WB_valid_by_bank,
    input logic [LOG_PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_upper_PR_by_bank,
    input logic [LOG_PRF_BANK_COUNT-1:0][31:0]                                  WB_data_by_bank,

    // ALU op issue to ALU pipeline
    output logic                            issue_valid,
    output logic [3:0]                      issue_op,
    output logic                            issue_is_imm,
    output logic [31:0]                     issue_imm,
    output logic                            issue_A_unneeded,
    output logic                            issue_A_forward,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_A_bank,
    output logic                            issue_B_forward,
    output logic [LOG_PRF_BANK_COUNT-1:0]   issue_B_bank,
    output logic [LOG_PR_COUNT-1:0]         issue_dest_PR,

    // reg read req to PRF
    output logic                        PRF_req_A_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_A_PR,
    output logic                        PRF_req_B_valid,
    output logic [LOG_PR_COUNT-1:0]     PRF_req_B_PR
);

    // ----------------------------------------------------------------
    // Signals:

    // IQ entries
    logic [3:0]                     valid_by_entry;
    logic [3:0][3:0]                op_by_entry;
    logic [3:0][31:0]               imm_by_entry;
    logic [3:0][LOG_PR_COUNT-1:0]   A_PR_by_entry;
    logic [3:0]                     A_unneeded_by_entry;
    logic [3:0]                     A_ready_by_entry;
    logic [3:0][LOG_PR_COUNT-1:0]   B_PR_by_entry;
    logic [3:0]                     is_imm_by_entry;
    logic [3:0]                     B_ready_by_entry;
    logic [3:0][LOG_PR_COUNT-1:0]   dest_PR_by_entry;

    // issue logic helper signals
    logic [3:0] A_forward_by_entry;
    logic [3:0] B_forward_by_entry;
    logic [3:0] op_ready_by_entry;
    logic [3:0] issue_mask;
    logic [3:0] take_self_mask;
    logic [3:0] take_above_mask;

    // ----------------------------------------------------------------
    // Logic: 

    //////////////////
    // issue logic: //
    //////////////////

    always_comb begin
        for (int i = 0; i < 4; i++) begin
            A_forward_by_entry[i] = (A_PR_by_entry[i][5:2] == WB_upper_PR_by_bank[A_PR_by_entry[i][1:0]]) & WB_valid_by_bank[A_PR_by_entry[i][1:0]];
            B_forward_by_entry[i] = (B_PR_by_entry[i][5:2] == WB_upper_PR_by_bank[B_PR_by_entry[i][1:0]]) & WB_valid_by_bank[B_PR_by_entry[i][1:0]];
        end
    end

    assign op_ready_by_entry = 
        valid_by_entry 
        &
        (A_unneeded_by_entry | A_ready_by_entry | A_forward_by_entry)
        &
        (is_imm_by_entry | B_ready_by_entry | B_forward_by_entry)
    ;

    always_comb begin

        issue_mask = 4'b0000;

        issue_valid = 1'b0;
        issue_op = op_by_entry[0];
        issue_is_imm = is_imm_by_entry[0];
        issue_imm = imm_by_entry[0];
        issue_A_unneeded = A_unneeded_by_entry[0];
        issue_A_forward = A_forward_by_entry[0];
        issue_A_bank = A_PR_by_entry[0][1:0];
        issue_B_forward = B_forward_by_entry[0];
        issue_B_bank = B_PR_by_entry[0][1:0];
        issue_dest_PR = dest_PR_by_entry[0];

        if (op_ready_by_entry[0]) begin

            issue_mask = 4'b1111;

            issue_valid = 1'b1;
            issue_op = op_by_entry[0];
            issue_is_imm = is_imm_by_entry[0];
            issue_imm = imm_by_entry[0];
            issue_A_unneeded = A_unneeded_by_entry[0];
            issue_A_forward = A_forward_by_entry[0];
            issue_A_bank = A_PR_by_entry[0][1:0];
            issue_B_forward = B_forward_by_entry[0];
            issue_B_bank = B_PR_by_entry[0][1:0];
            issue_dest_PR = dest_PR_by_entry[0];
        end
        else if (op_ready_by_entry[1]) begin
            
            issue_mask = 4'b1110;
            
            issue_valid = 1'b1;
            issue_op = op_by_entry[1];
            issue_is_imm = is_imm_by_entry[1];
            issue_imm = imm_by_entry[1];
            issue_A_unneeded = A_unneeded_by_entry[1];
            issue_A_forward = A_forward_by_entry[1];
            issue_A_bank = A_PR_by_entry[1][1:0];
            issue_B_forward = B_forward_by_entry[1];
            issue_B_bank = B_PR_by_entry[1][1:0];
            issue_dest_PR = dest_PR_by_entry[1];
        end
        else if (op_ready_by_entry[2]) begin

            issue_mask = 4'b1100;
            
            issue_valid = 1'b1;
            issue_op = op_by_entry[2];
            issue_is_imm = is_imm_by_entry[2];
            issue_imm = imm_by_entry[2];
            issue_A_unneeded = A_unneeded_by_entry[2];
            issue_A_forward = A_forward_by_entry[2];
            issue_A_bank = A_PR_by_entry[2][1:0];
            issue_B_forward = B_forward_by_entry[2];
            issue_B_bank = B_PR_by_entry[2][1:0];
            issue_dest_PR = dest_PR_by_entry[2];
        end
        else if (op_ready_by_entry[3]) begin

            issue_mask = 4'b1000;
            
            issue_valid = 1'b1;
            issue_op = op_by_entry[3];
            issue_is_imm = is_imm_by_entry[3];
            issue_imm = imm_by_entry[3];
            issue_A_unneeded = A_unneeded_by_entry[3];
            issue_A_forward = A_forward_by_entry[3];
            issue_A_bank = A_PR_by_entry[3][1:0];
            issue_B_forward = B_forward_by_entry[3];
            issue_B_bank = B_PR_by_entry[3][1:0];
            issue_dest_PR = dest_PR_by_entry[3];
        end
    end

    assign take_self_mask = valid_by_entry & ~issue_mask;

    always_comb begin
        take_above_mask[3] = 1'b0;
        for (int i = 0; i < 3; i++) begin
            take_above_mask[i] = valid_by_entry[i+1] & issue_mask[i];
        end
    end

    ////////////////////////////////
    // IQ entry next state logic: //
    ////////////////////////////////

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_by_entry <= 1'b0;
            op_by_entry <= 4'b0000;
            imm_by_entry <= 32'h0;
            A_PR_by_entry <= '0;
            A_unneeded_by_entry <= 1'b0;
            A_ready_by_entry <= 1'b0;
            B_PR_by_entry <= '0;
            is_imm_by_entry <= 1'b0;
            B_ready_by_entry <= 1'b0;
            dest_PR_by_entry <= '0;
        end
        else begin

            // 0:2 can take above
            for (int i = 0; i < 3; i++) begin
                if (take_above_mask[i]) begin
                    valid_by_entry[i] <= valid_by_entry[i+1];
                    op_by_entry[i] <= op_by_entry[i+1];
                    imm_by_entry[i] <= imm_by_entry[i+1];
                    A_PR_by_entry[i] <= A_PR_by_entry[i+1];
                    A_unneeded_by_entry[i] <= A_unneeded_by_entry[i+1];
                    A_ready_by_entry[i] <= A_ready_by_entry[i+1] | A_forward_by_entry[i+1];
                    B_PR_by_entry[i] <= B_PR_by_entry[i+1];
                    is_imm_by_entry[i] <= is_imm_by_entry[i+1];
                    B_ready_by_entry[i] <= B_ready_by_entry[i+1] | B_forward_by_entry[i+1];
                    dest_PR_by_entry[i] <= dest_PR_by_entry[i+1];
                end
                else if (take_self_mask[i]) begin
                    valid_by_entry[i] <= valid_by_entry[i];
                    op_by_entry[i] <= op_by_entry[i];
                    imm_by_entry[i] <= imm_by_entry[i];
                    A_PR_by_entry[i] <= A_PR_by_entry[i];
                    A_unneeded_by_entry[i] <= A_unneeded_by_entry[i];
                    A_ready_by_entry[i] <= A_ready_by_entry[i] | A_forward_by_entry[i];
                    B_PR_by_entry[i] <= B_PR_by_entry[i];
                    is_imm_by_entry[i] <= is_imm_by_entry[i];
                    B_ready_by_entry[i] <= B_ready_by_entry[i] | B_forward_by_entry[i];
                    dest_PR_by_entry[i] <= dest_PR_by_entry[i];
                end
                else begin
                    valid_by_entry[i] <= dispatch_valid_by_entry[i];
                    op_by_entry[i] <= dispatch_op_by_entry[i];
                    imm_by_entry[i] <= dispatch_imm_by_entry[i];
                    A_PR_by_entry[i] <= dispatch_A_PR_by_entry[i];
                    A_unneeded_by_entry[i] <= dispatch_A_unneeded_by_entry[i];
                    A_ready_by_entry[i] <= dispatch_A_ready_by_entry[i];
                    B_PR_by_entry[i] <= dispatch_B_PR_by_entry[i];
                    is_imm_by_entry[i] <= dispatch_is_imm_by_entry[i];
                    B_ready_by_entry[i] <= dispatch_B_ready_by_entry[i];
                    dest_PR_by_entry[i] <= dispatch_dest_PR_by_entry[i];
                end
            end

            // 3 can't take above
                // don't want to infer unused connection (this one loops around the IQ which will be bad)
            if (take_self_mask[3]) begin
                valid_by_entry[3] <= valid_by_entry[3];
                op_by_entry[3] <= op_by_entry[3];
                imm_by_entry[3] <= imm_by_entry[3];
                A_PR_by_entry[3] <= A_PR_by_entry[3];
                A_unneeded_by_entry[3] <= A_unneeded_by_entry[3];
                A_ready_by_entry[3] <= A_ready_by_entry[3] | A_forward_by_entry[3];
                B_PR_by_entry[3] <= B_PR_by_entry[3];
                is_imm_by_entry[3] <= is_imm_by_entry[3];
                B_ready_by_entry[3] <= B_ready_by_entry[3] | B_forward_by_entry[3];
                dest_PR_by_entry[3] <= dest_PR_by_entry[3];
            end
            else begin
                valid_by_entry[3] <= dispatch_valid_by_entry[3];
                op_by_entry[3] <= dispatch_op_by_entry[3];
                imm_by_entry[3] <= dispatch_imm_by_entry[3];
                A_PR_by_entry[3] <= dispatch_A_PR_by_entry[3];
                A_unneeded_by_entry[3] <= dispatch_A_unneeded_by_entry[3];
                A_ready_by_entry[3] <= dispatch_A_ready_by_entry[3];
                B_PR_by_entry[3] <= dispatch_B_PR_by_entry[3];
                is_imm_by_entry[3] <= dispatch_is_imm_by_entry[3];
                B_ready_by_entry[3] <= dispatch_B_ready_by_entry[3];
                dest_PR_by_entry[3] <= dispatch_dest_PR_by_entry[3];
            end
        end
    end

endmodule