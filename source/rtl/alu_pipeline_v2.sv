/*
    Filename: alu_pipeline_v2.sv
    Author: zlagpacan
    Description: RTL for ALU Pipeline v2
    Spec: LOROF/spec/design/alu_pipeline_v2.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_pipeline_v2 (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU op issue from ALU IQ
    input logic                             issue_valid,
    input logic [3:0]                       issue_op,
    input logic                             issue_is_imm,
    input logic [31:0]                      issue_imm,
    input logic                             issue_A_unneeded,
    input logic                             issue_A_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_bank,
    input logic                             issue_B_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_B_bank,
    input logic [LOG_PR_COUNT-1:0]          issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       issue_ROB_index,

    // ready feedback to ALU IQ
    output logic issue_ready,

    // reg read info and data from PRF
    input logic                                     A_reg_read_valid,
    input logic                                     A_reg_read_port,
    input logic                                     B_reg_read_valid,
    input logic                                     B_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0]     reg_read_data_by_bank_by_port,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // writeback backpressure from PRF
    input logic WB_ready
);
    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_WB;
    logic stall_EX;
    logic stall_OC;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                           valid_OC;
    logic [3:0]                     op_OC;
    logic                           is_imm_OC;
    logic [31:0]                    imm_OC;
    logic                           A_unneeded_OC;
    logic                           A_saved_OC;
    logic                           A_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]  A_bank_OC;
    logic                           B_saved_OC;
    logic                           B_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]  B_bank_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

    logic [31:0] A_saved_data_OC;
    logic [31:0] B_saved_data_OC;

    logic launch_ready_OC;

    logic                           next_valid_EX;
    logic [3:0]                     next_op_EX;
    logic [31:0]                    next_A_EX;
    logic [31:0]                    next_B_EX;
    logic [LOG_PR_COUNT-1:0]        next_dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]     next_ROB_index_EX;

    // ----------------------------------------------------------------
    // EX Stage Signals:

    logic                           valid_EX;
    logic [3:0]                     op_EX;
    logic [31:0]                    A_EX;
    logic [31:0]                    B_EX;
    logic [LOG_PR_COUNT-1:0]        dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_EX;

    logic                           next_WB_valid;
    logic [31:0]                    next_WB_data;
    logic [LOG_PR_COUNT-1:0]        next_WB_PR;
    logic [LOG_ROB_ENTRIES-1:0]     next_WB_ROB_index;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    // ----------------------------------------------------------------
    // Control Logic: 

    assign stall_WB = WB_valid & ~WB_ready;
    assign stall_EX = valid_EX & stall_WB;
        // stall_WB shouldn't happen with WB_valid anyway
    assign stall_OC = stall_EX & valid_OC;
        // this stall doesn't strictly "stall" OC
        // indicates that should stall values in OC if OC valid

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
            ROB_index_OC <= '0;
        end
        // stall OC stage when have valid op which can't move on: issue_ready == 1'b0
        else if (~issue_ready) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            is_imm_OC <= is_imm_OC;
            imm_OC <= imm_OC;
            A_unneeded_OC <= A_unneeded_OC;
            A_saved_OC <= A_saved_OC | A_forward_OC | A_reg_read_valid;
            A_forward_OC <= 1'b0;
            A_bank_OC <= A_bank_OC;
            B_saved_OC <= B_saved_OC | B_forward_OC | B_reg_read_valid;
            B_forward_OC <= 1'b0;
            B_bank_OC <= B_bank_OC;
            dest_PR_OC <= dest_PR_OC;
            ROB_index_OC <= ROB_index_OC;
        end
        // pass input issue to OC
        else begin
            valid_OC <= issue_valid;
            op_OC <= issue_op;
            is_imm_OC <= issue_is_imm;
            imm_OC <= issue_imm;
            A_unneeded_OC <= issue_A_unneeded;
            A_saved_OC <= 1'b0;
            A_forward_OC <= issue_A_forward;
            A_bank_OC <= issue_A_bank;
            B_saved_OC <= 1'b0;
            B_forward_OC <= issue_B_forward;
            B_bank_OC <= issue_B_bank;
            dest_PR_OC <= issue_dest_PR;
            ROB_index_OC <= issue_ROB_index;
        end
    end

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            A_saved_data_OC <= 32'h0;
            B_saved_data_OC <= 32'h0;
        end
        else begin
            A_saved_data_OC <= next_A_EX;
            B_saved_data_OC <= next_B_EX;
        end
    end

    assign launch_ready_OC = 
        // no backpressure
        ~stall_OC
        &
        // A operand present
        (A_unneeded_OC | A_saved_OC | A_forward_OC | A_reg_read_valid)
        &
        // B operand present
        (is_imm_OC | B_saved_OC | B_forward_OC | B_reg_read_valid)
    ;
    assign issue_ready = ~valid_OC | launch_ready_OC;
    
    assign next_valid_EX = valid_OC & launch_ready_OC;
    assign next_op_EX = op_OC;
    assign next_dest_PR_EX = dest_PR_OC;
    assign next_ROB_index_EX = ROB_index_OC;

    always_comb begin

        // collect A value to save OR pass to EX
        if (A_saved_OC) begin
            next_A_EX = A_saved_data_OC;
        end
        else if (A_forward_OC) begin
            next_A_EX = forward_data_by_bank[A_bank_OC];
        end
        else begin
            next_A_EX = reg_read_data_by_bank_by_port[A_bank_OC][A_reg_read_port];
        end

        // collect B value to save OR pass to EX
        if (B_saved_OC) begin
            next_B_EX = B_saved_data_OC;
        end
        else if (is_imm_OC) begin
            next_B_EX = imm_OC;
        end
        else if (B_forward_OC) begin
            next_B_EX = forward_data_by_bank[B_bank_OC];
        end
        else begin
            next_B_EX = reg_read_data_by_bank_by_port[B_bank_OC][B_reg_read_port];
        end
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
            ROB_index_EX <= '0;
        end
        else if (stall_EX) begin
            valid_EX <= valid_EX;
            op_EX <= op_EX;
            A_EX <= A_EX;
            B_EX <= B_EX;
            dest_PR_EX <= dest_PR_EX;
            ROB_index_EX <= ROB_index_EX;
        end
        else begin
            valid_EX <= next_valid_EX;
            op_EX <= next_op_EX;
            A_EX <= next_A_EX;
            B_EX <= next_B_EX;
            dest_PR_EX <= next_dest_PR_EX;
            ROB_index_EX <= next_ROB_index_EX;
        end
    end

    assign next_WB_valid = valid_EX;
    assign next_WB_PR = dest_PR_EX;
    assign next_WB_ROB_index = ROB_index_EX;

    // actual ALU
    always_comb begin
        case (op_EX)
            4'b0000:    next_WB_data = A_EX + B_EX;
            4'b0001:    next_WB_data = A_EX << B_EX[4:0];
            4'b0010:    next_WB_data = $signed(A_EX) < $signed(B_EX);
            4'b0011:    next_WB_data = A_EX < B_EX;
            4'b0100:    next_WB_data = A_EX ^ B_EX;
            4'b0101:    next_WB_data = A_EX >> B_EX[4:0];
            4'b0110:    next_WB_data = A_EX | B_EX;
            4'b0111:    next_WB_data = A_EX & B_EX;
            4'b1000:    next_WB_data = A_EX - B_EX;
            4'b1101:    next_WB_data = $signed(A_EX) >>> B_EX[4:0];
            4'b1111:    next_WB_data = B_EX;
            default:    next_WB_data = B_EX;
        endcase
    end

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            WB_valid <= 1'b0;
            WB_data <= 32'h0;
            WB_PR <= '0;
            WB_ROB_index <= '0;
        end
        else if (stall_WB) begin
            WB_valid <= WB_valid;
            WB_data <= WB_data;
            WB_PR <= WB_PR;
            WB_ROB_index <= WB_ROB_index;
        end
        else begin
            WB_valid <= next_WB_valid;
            WB_data <= next_WB_data;
            WB_PR <= next_WB_PR;
            WB_ROB_index <= next_WB_ROB_index;
        end
    end

endmodule