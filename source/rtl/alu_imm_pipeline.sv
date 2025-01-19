/*
    Filename: alu_imm_pipeline.sv
    Author: zlagpacan
    Description: RTL for ALU Register-Immediate Pipeline
    Spec: LOROF/spec/design/alu_imm_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU op issue from ALU Imm IQ
    input logic                             issue_valid,
    input logic [3:0]                       issue_op,
    input logic [11:0]                      issue_imm12,
    input logic                             issue_A_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_bank,
    input logic [LOG_PR_COUNT-1:0]          issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       issue_ROB_index,

    // ready feedback to ALU Imm IQ
    output logic issue_ready,

    // reg read info and data from PRF
    input logic                                     A_reg_read_ack,
    input logic                                     A_reg_read_port,
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
    logic [11:0]                    imm12_OC;
    logic                           A_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]  A_bank_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

    logic launch_ready_OC;

    logic                           next_valid_EX;
    logic [3:0]                     next_op_EX;
    logic [31:0]                    next_A_EX;
    logic [11:0]                    next_imm12_EX;
    logic [LOG_PR_COUNT-1:0]        next_dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]     next_ROB_index_EX;

    // ----------------------------------------------------------------
    // EX Stage Signals:

    logic                           valid_EX;
    logic [3:0]                     op_EX;
    logic [31:0]                    A_EX;
    logic [11:0]                    imm12_EX;
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
            imm12_OC <= 12'h0;
            A_forward_OC <= 1'b0;
            A_bank_OC <= '0;
            dest_PR_OC <= '0;
            ROB_index_OC <= '0;
        end
        // stall OC stage when have valid op which can't move on: issue_ready == 1'b0
        else if (~issue_ready) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            imm12_OC <= imm12_OC;
            A_forward_OC <= 1'b0;
            A_bank_OC <= A_bank_OC;
            dest_PR_OC <= dest_PR_OC;
            ROB_index_OC <= ROB_index_OC;
        end
        // pass input issue to OC
        else begin
            valid_OC <= issue_valid;
            op_OC <= issue_op;
            imm12_OC <= issue_imm12;
            A_forward_OC <= issue_A_forward;
            A_bank_OC <= issue_A_bank;
            dest_PR_OC <= issue_dest_PR;
            ROB_index_OC <= issue_ROB_index;
        end
    end

    assign launch_ready_OC = 
        // no backpressure
        ~stall_OC
        &
        // A operand present
        (A_forward_OC | A_reg_read_ack)
    ;

    assign issue_ready = ~valid_OC | launch_ready_OC;
    
    assign next_valid_EX = valid_OC & launch_ready_OC;
    assign next_op_EX = op_OC;
    assign next_dest_PR_EX = dest_PR_OC;
    assign next_ROB_index_EX = ROB_index_OC;

    always_comb begin

        // collect A value to pass to EX
        if (A_forward_OC) begin
            next_A_EX = forward_data_by_bank[A_bank_OC];
        end
        else begin
            next_A_EX = reg_read_data_by_bank_by_port[A_bank_OC][A_reg_read_port];
        end

        // collect B value to save OR pass to EX
        next_imm12_EX = imm12_OC;
    end

    // ----------------------------------------------------------------
    // EX Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_EX <= 1'b0;
            op_EX <= 4'b0000;
            A_EX <= 32'h0;
            imm12_EX <= 12'h0;
            dest_PR_EX <= '0;
            ROB_index_EX <= '0;
        end
        else if (stall_EX) begin
            valid_EX <= valid_EX;
            op_EX <= op_EX;
            A_EX <= A_EX;
            imm12_EX <= imm12_EX;
            dest_PR_EX <= dest_PR_EX;
            ROB_index_EX <= ROB_index_EX;
        end
        else begin
            valid_EX <= next_valid_EX;
            op_EX <= next_op_EX;
            A_EX <= next_A_EX;
            imm12_EX <= next_imm12_EX;
            dest_PR_EX <= next_dest_PR_EX;
            ROB_index_EX <= next_ROB_index_EX;
        end
    end

    assign next_WB_valid = valid_EX;
    assign next_WB_PR = dest_PR_EX;
    assign next_WB_ROB_index = ROB_index_EX;

    assign B_EX = {{20{imm12_EX[11]}}, imm12_EX};

    // actual ALU
    alu ALU (
        .op(op_EX),
        .A(A_EX),
        .B(B_EX),
        .out(next_WB_data)
    );

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