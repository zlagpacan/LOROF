/*
    Filename: bru_pred_info_updater.sv
    Author: zlagpacan
    Description: RTL for Branch Prediction Info Updater for the Branch Resolution Unit
    Spec: LOROF/spec/design/bru_pred_info_updater.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pred_info_updater (
    
    // inputs
    input logic [3:0]                       op,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   start_pred_info,
    input logic                             is_link_ra,
    input logic                             is_ret_ra,
    input logic                             is_taken,
    input logic                             is_mispredict,
    input logic                             is_out_of_range,

    // outputs
    output logic [BTB_PRED_INFO_WIDTH-1:0]  updated_pred_info
); 

    logic [3:0] accuracy_4b;
    logic [4:0] accuracy_minus_penalty_5b;
    logic [3:0] accuracy_plus_1_4b;
    logic [3:0] accuracy_minus_1_4b;
    logic [1:0] simple_branch_state_machine_update;

    assign accuracy_4b = start_pred_info[3:0];
    assign accuracy_minus_penalty_5b = {1'b0, accuracy_4b} - SIMPLE_BRANCH_INACCURACY_PENALTY[4:0];
    assign accuracy_plus_1_4b = accuracy_4b + 4'h1;
    assign accuracy_minus_1_4b = accuracy_4b - 4'h1;

    // simple branch 2bc state machine
    always_comb begin
        case ({start_pred_info[5:4], is_taken})
            3'b000: simple_branch_state_machine_update = 2'b00; // SN -> N -> SN
            3'b001: simple_branch_state_machine_update = 2'b01; // SN -> T -> WN
            3'b010: simple_branch_state_machine_update = 2'b00; // WN -> N -> SN
            3'b011: simple_branch_state_machine_update = 2'b11; // WN -> T -> ST
            3'b100: simple_branch_state_machine_update = 2'b00; // WT -> N -> SN
            3'b101: simple_branch_state_machine_update = 2'b11; // WT -> T -> ST
            3'b110: simple_branch_state_machine_update = 2'b10; // ST -> N -> WT
            3'b111: simple_branch_state_machine_update = 2'b11; // ST -> T -> ST
        endcase
    end
    
    always_comb begin
        
        casez (op)

            // --------------------------------------------------------
            // jumps have unique static behavior regardless of start pred info

            4'b0000, 4'b0001: // JALR, C.JALR
            begin
                updated_pred_info[7:6] = 2'b01;
                updated_pred_info[5] = is_ret_ra; // can be ret
                updated_pred_info[4] = is_link_ra; // can be link
                updated_pred_info[3:0] = 4'b0000; // don't care
            end

            4'b0010, 4'b0011: // JAL, C.JAL
            begin
                updated_pred_info[7:6] = 2'b01;
                updated_pred_info[5] = 1'b0; // not ret
                updated_pred_info[4] = is_link_ra; // can be link
                updated_pred_info[3:0] = 4'b0000; // don't care
            end

            4'b0100: // C.J
            begin
                updated_pred_info[7:6] = 2'b01;
                updated_pred_info[5:4] = 2'b00; // not ret nor link
                updated_pred_info[3:0] = 4'b0000; // don't care
            end

            4'b0101: // C.JR
            begin
                updated_pred_info[7:6] = 2'b01;
                updated_pred_info[5] = is_ret_ra; // can be ret
                updated_pred_info[4] = 1'b0; // not link
                updated_pred_info[3:0] = 4'b000; // don't care
            end

            4'b0110: // LUI
            begin
                updated_pred_info = 8'h0; // don't care
            end

            4'b0111: // AUIPC
            begin
                updated_pred_info = 8'h0; // don't care
            end

            // --------------------------------------------------------
            // branches share same dynamic behavior

            4'b1???: // BEQ
            begin
                // check for non-complex branch and out-of-range -> init complex branch
                if (start_pred_info[7:6] != 2'b11 & is_out_of_range) begin
                    updated_pred_info[7:6] = 2'b11; // complex branch
                    updated_pred_info[5:4] = 2'b01; // start slightly favoring local
                    updated_pred_info[3:0] = 4'b0000; // don't care
                end

                // check for invalid or jump -> init simple branch
                else if (~start_pred_info[7]) begin
                    updated_pred_info[7:6] = 2'b10; // simple branch
                    // start strongly favoring based on this taken
                    if (is_taken)   updated_pred_info[5:4] = 2'b11; // ST
                    else            updated_pred_info[5:4] = 2'b00; // SN
                    updated_pred_info[3:0] = SIMPLE_BRANCH_INIT_ACCURACY;
                end

                // otherwise, branch: check simple branch
                else if (~start_pred_info[6]) begin

                    // check above threshold
                    if (accuracy_4b > SIMPLE_BRANCH_ACCURACY_THRESHOLD) begin
                        updated_pred_info[7:6] = 2'b10; // simple branch
                        updated_pred_info[5:4] = simple_branch_state_machine_update; // 2bc update
                        updated_pred_info[3:0] = accuracy_minus_1_4b; // decrement accuracy
                    end

                    // otherwise, at or below threshold
                    else begin

                        // check for mispredict and below 0 -> init complex branch
                        if (is_mispredict & accuracy_minus_penalty_5b[4]) begin
                            updated_pred_info[7:6] = 2'b11; // complex branch
                            updated_pred_info[5:4] = 2'b01; // start slightly favoring local
                            updated_pred_info[3:0] = 4'b0000; // don't care
                        end

                        // check for mispredict -> subtract threshold
                        else if (is_mispredict) begin
                            updated_pred_info[7:6] = 2'b10; // simple branch
                            updated_pred_info[5:4] = simple_branch_state_machine_update; // 2bc update
                            updated_pred_info[3:0] = accuracy_minus_penalty_5b; // give penalty
                        end

                        // otherwise, good prediction, increment or saturate at threshold
                        else begin
                            if (accuracy_4b == SIMPLE_BRANCH_ACCURACY_THRESHOLD) begin
                                updated_pred_info[7:6] = 2'b10; // simple branch
                                updated_pred_info[5:4] = simple_branch_state_machine_update; // 2bc update
                                updated_pred_info[3:0] = SIMPLE_BRANCH_ACCURACY_THRESHOLD;
                            end else begin
                                updated_pred_info[7:6] = 2'b10; // simple branch
                                updated_pred_info[5:4] = simple_branch_state_machine_update; // 2bc update
                                updated_pred_info[3:0] = accuracy_plus_1_4b;
                            end
                        end
                    end
                end

                // otherwise, complex branch
                else begin
                    updated_pred_info[7:6] = 2'b11; // complex branch
                    updated_pred_info[5:4] = start_pred_info[5:4]; // propagate 2bc to frontend for update there
                    updated_pred_info[3:0] = 4'b0000; // don't care
                end
            end

        endcase
    end

endmodule