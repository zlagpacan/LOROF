/*
    Filename: alu_pipeline.sv
    Author: zlagpacan
    Description: RTL for ALU Pipeline
    Spec: LOROF/spec/design/alu_pipeline.md
    RTL Diagram: 
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_pipeline #() (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU op issue from ALU IQ
    input logic valid_in,
    input logic [3:0] op_in,
    input logic is_imm_in,
    input logic [31:0] imm_in,
    input logic A_unneeded_in,
    input logic A_forward_in,
    input logic [LOG_PRF_BANK_COUNT-1:0] A_bank_in,
    input logic B_forward_in,
    input logic [LOG_PRF_BANK_COUNT-1:0] B_bank_in,
    input logic [LOG_PR_COUNT-1:0] dest_PR_in,

    // reg read info and data from PRF
    input logic A_reg_read_valid_in,
    input logic B_reg_read_valid_in,
    input logic [PRF_BANK_COUNT-1:0][31:0] reg_read_data_by_bank_in,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank_in,

    // ready feedback to ALU IQ
    output logic ready_out,

    // writeback data to PRF
    output logic WB_valid_out,
    output logic [31:0] WB_data_out,
    output logic [LOG_PR_COUNT-1:0] WB_PR_out
);

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic valid_OC;
    logic [3:0] op_OC;
    logic is_imm_OC;
    logic [31:0] imm_OC;
    logic A_unneeded_OC;
    logic A_saved_OC;
    logic A_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0] A_bank_OC;
    logic B_saved_OC;
    logic B_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0] B_bank_OC;
    logic [LOG_PR_COUNT-1:0] dest_PR_OC;

    logic launch_ready_OC;
    logic stall_OC;

    logic next_valid_EX;
    logic [3:0] next_op_EX;
    logic [31:0] next_A_EX;
    logic [31:0] next_B_EX;
    logic [LOG_PR_COUNT-1:0] next_dest_PR_EX;

    // ----------------------------------------------------------------
    // EX Stage Signals:

    logic valid_EX;
    logic [3:0] op_EX;
    logic [31:0] A_EX;
    logic [31:0] B_EX;
    logic [LOG_PR_COUNT-1:0] dest_PR_EX;

    logic next_WB_valid_out;
    logic [31:0] next_WB_data_out;
    logic [LOG_PR_COUNT-1:0] next_WB_PR_out;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    // ----------------------------------------------------------------
    // OC Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_OC <= 1'b0;
            op_OC <= 4'b0000;
            is_imm_OC <= 1'b0;
            imm_OC <= 32'h0;
            A_unneeded_OC <= 1'b0;
            A_saved_OC <= 1'b0;
            A_forward_OC <= 1'b0;
            A_bank_OC <= '0;
            B_saved_OC <= 1'b0;
            B_forward_OC <= 1'b0;
            B_bank_OC <= '0;
            dest_PR_OC <= '0;
        end
        else if (stall_OC) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            is_imm_OC <= is_imm_OC;
            imm_OC <= imm_OC;
            A_unneeded_OC <= A_unneeded_OC;
            A_saved_OC <= A_saved_OC | A_forward_OC | A_reg_read_valid_in;
            A_forward_OC <= 1'b0;
            A_bank_OC <= A_bank_OC;
            B_saved_OC <= B_saved_OC | B_forward_OC | B_reg_read_valid_in;
            B_forward_OC <= 1'b0;
            B_bank_OC <= B_bank_OC;
            dest_PR_OC <= dest_PR_OC;
        end
        else begin
            valid_OC <= valid_in;
            op_OC <= op_in;
            is_imm_OC <= is_imm_in;
            imm_OC <= imm_in;
            A_unneeded_OC <= A_unneeded_in;
            A_forward_OC <= A_forward_in;
            A_bank_OC <= A_bank_in;
            B_forward_OC <= B_forward_in;
            B_bank_OC <= B_bank_in;
            dest_PR_OC <= dest_PR_in;
        end
    end

    assign launch_ready_OC = 
        (A_unneeded_OC | A_saved_OC | A_forward_OC | A_reg_read_valid_in)
        & 
        (is_imm_OC | B_saved_OC | B_forward_OC | B_reg_read_valid_in)
    ;
    assign ready_out = ~valid_OC | launch_ready_OC;
    assign stall_OC = ~ready_out;

    assign next_valid_EX = valid_OC & launch_ready_OC;
    assign next_op_EX = op_OC;
    assign next_dest_PR_EX = dest_PR_OC;

    always_comb begin
        if (A_saved_OC)
            next_A_EX = A_EX;
        else if (A_forward_OC)
            next_A_EX = forward_data_by_bank_in[A_bank_OC];
        else 
            next_A_EX = reg_read_data_by_bank_in[A_bank_OC];

        if (B_saved_OC)
            next_B_EX = B_EX;
        else if (is_imm_OC)
            next_B_EX = imm_OC;
        else if (B_forward_OC)
            next_B_EX = forward_data_by_bank_in[B_bank_OC];
        else 
            next_B_EX = reg_read_data_by_bank_in[B_bank_OC];
    end

    // ----------------------------------------------------------------
    // EX Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_EX <= 1'b0;
            op_EX <= 4'b0000;
            A_EX <= 32'h0;
            B_EX <= 32'h0;
            dest_PR_EX <= '0;
        end
        else begin
            valid_EX <= next_valid_EX;
            op_EX <= next_op_EX;
            A_EX <= next_A_EX;
            B_EX <= next_B_EX;
            dest_PR_EX <= next_dest_PR_EX;
        end
    end

    assign next_WB_valid_out = valid_EX;
    assign next_WB_PR_out = dest_PR_EX;

    // actual ALU
    always_comb begin
        case (op_EX)
            4'b0000:    next_WB_data_out = A_EX + B_EX;
            4'b0001:    next_WB_data_out = A_EX << B_EX[4:0];
            4'b0010:    next_WB_data_out = $signed(A_EX) < $signed(B_EX);
            4'b0011:    next_WB_data_out = A_EX < B_EX;
            4'b0100:    next_WB_data_out = A_EX ^ B_EX;
            4'b0101:    next_WB_data_out = A_EX >> B_EX[4:0];
            4'b0110:    next_WB_data_out = A_EX | B_EX;
            4'b0111:    next_WB_data_out = A_EX & B_EX;
            4'b1000:    next_WB_data_out = A_EX - B_EX;
            4'b1101:    next_WB_data_out = $signed(A_EX) >>> B_EX[4:0];
            4'b1111:    next_WB_data_out = B_EX;
            default:    next_WB_data_out = B_EX;
        endcase
    end

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            WB_valid_out <= 1'b0;
            WB_data_out <= 32'h0;
            WB_PR_out <= '0;
        end
        else begin
            WB_valid_out <= next_WB_valid_out;
            WB_data_out <= next_WB_data_out;
            WB_PR_out <= next_WB_PR_out;
        end
    end

endmodule