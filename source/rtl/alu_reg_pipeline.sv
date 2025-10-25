/*
    Filename: alu_reg_pipeline.sv
    Author: zlagpacan
    Description: RTL for ALU Register-Register Pipeline
    Spec: LOROF/spec/design/alu_reg_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU reg op issue from IQ
    input logic                             issue_valid,
    input logic [3:0]                       issue_op,
    input logic                             issue_A_forward,
    input logic                             issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_bank,
    input logic                             issue_B_forward,
    input logic                             issue_B_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_B_bank,
    input logic [LOG_PR_COUNT-1:0]          issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       issue_ROB_index,

    // ready feedback to IQ
    output logic issue_ready,

    // reg read info and data from PRF
    input logic                                     A_reg_read_ack,
    input logic                                     A_reg_read_port,
    input logic                                     B_reg_read_ack,
    input logic                                     B_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0]     reg_read_data_by_bank_by_port,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // writeback feedback from PRF
    input logic WB_ready
);
    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_WB;
    logic stall_OC;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                           valid_OC;
    logic [3:0]                     op_OC;
    logic                           A_saved_OC;
    logic                           A_forward_OC;
    logic                           A_is_zero_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]  A_bank_OC;
    logic                           B_saved_OC;
    logic                           B_forward_OC;
    logic                           B_is_zero_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]  B_bank_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

    logic [31:0] A_saved_data_OC;
    logic [31:0] B_saved_data_OC;

    logic launch_ready_OC;

    logic                           next_WB_valid;
    logic [3:0]                     next_WB_op;
    logic [31:0]                    next_WB_A;
    logic [31:0]                    next_WB_B;
    logic [LOG_PR_COUNT-1:0]        next_WB_PR;
    logic [LOG_ROB_ENTRIES-1:0]     next_WB_ROB_index;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    logic [3:0]     WB_op;
    logic [31:0]    WB_A;
    logic [31:0]    WB_B;

    // ----------------------------------------------------------------
    // Control Logic: 

    assign stall_WB = WB_valid & ~WB_ready;
    assign stall_OC = stall_WB & valid_OC;
        // this stall doesn't strictly "stall" OC
        // indicates that should stall values in OC if OC valid

    // ----------------------------------------------------------------
    // OC Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_OC <= 1'b0;
            op_OC <= 4'b0000;
            A_saved_OC <= 1'b0;
            A_forward_OC <= 1'b0;
            A_is_zero_OC <= 1'b0;
            A_bank_OC <= '0;
            B_saved_OC <= 1'b0;
            B_forward_OC <= 1'b0;
            B_is_zero_OC <= 1'b0;
            B_bank_OC <= '0;
            dest_PR_OC <= '0;
            ROB_index_OC <= '0;
        end
        // stall OC stage when have valid op which can't move on: issue_ready == 1'b0
        else if (~issue_ready) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            A_saved_OC <= A_saved_OC | A_forward_OC | A_reg_read_ack;
            A_forward_OC <= 1'b0;
            A_is_zero_OC <= A_is_zero_OC;
            A_bank_OC <= A_bank_OC;
            B_saved_OC <= B_saved_OC | B_forward_OC | B_reg_read_ack;
            B_forward_OC <= 1'b0;
            B_is_zero_OC <= B_is_zero_OC;
            B_bank_OC <= B_bank_OC;
            dest_PR_OC <= dest_PR_OC;
            ROB_index_OC <= ROB_index_OC;
        end
        // pass input issue to OC
        else begin
            valid_OC <= issue_valid;
            op_OC <= issue_op;
            A_saved_OC <= 1'b0;
            A_forward_OC <= issue_A_forward;
            A_is_zero_OC <= issue_A_is_zero;
            A_bank_OC <= issue_A_bank;
            B_saved_OC <= 1'b0;
            B_forward_OC <= issue_B_forward;
            B_is_zero_OC <= issue_B_is_zero;
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
            A_saved_data_OC <= next_WB_A;
            B_saved_data_OC <= next_WB_B;
        end
    end

    assign launch_ready_OC = 
        // no backpressure
        ~stall_OC
        &
        // A operand present
        (A_saved_OC | A_forward_OC | A_reg_read_ack | A_is_zero_OC)
        &
        // B operand present
        (B_saved_OC | B_forward_OC | B_reg_read_ack | B_is_zero_OC)
    ;

    assign issue_ready = ~valid_OC | launch_ready_OC;
    
    assign next_WB_valid = valid_OC & launch_ready_OC;
    assign next_WB_op = op_OC;
    assign next_WB_PR = dest_PR_OC;
    assign next_WB_ROB_index = ROB_index_OC;

    always_comb begin

        // collect A value to save OR pass to EX
        if (A_is_zero_OC) begin
            next_WB_A = 32'h0;
        end
        else if (A_saved_OC) begin
            next_WB_A = A_saved_data_OC;
        end
        else if (A_forward_OC) begin
            next_WB_A = forward_data_by_bank[A_bank_OC];
        end
        else begin
            next_WB_A = reg_read_data_by_bank_by_port[A_bank_OC][A_reg_read_port];
        end

        // collect B value to save OR pass to EX
        if (B_is_zero_OC) begin
            next_WB_B = 32'h0;
        end
        else if (B_saved_OC) begin
            next_WB_B = B_saved_data_OC;
        end
        else if (B_forward_OC) begin
            next_WB_B = forward_data_by_bank[B_bank_OC];
        end
        else begin
            next_WB_B = reg_read_data_by_bank_by_port[B_bank_OC][B_reg_read_port];
        end
    end

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            WB_valid <= 1'b0;
            WB_op <= 4'b0000;
            WB_A <= 32'h0;
            WB_B <= 32'h0;
            WB_PR <= '0;
            WB_ROB_index <= '0;
        end
        else if (stall_WB) begin
            WB_valid <= WB_valid;
            WB_op <= WB_op;
            WB_A <= WB_A;
            WB_B <= WB_B;
            WB_PR <= WB_PR;
            WB_ROB_index <= WB_ROB_index;
        end
        else begin
            WB_valid <= next_WB_valid;
            WB_op <= next_WB_op;
            WB_A <= next_WB_A;
            WB_B <= next_WB_B;
            WB_PR <= next_WB_PR;
            WB_ROB_index <= next_WB_ROB_index;
        end
    end

    // actual ALU
    alu ALU (
        .op(WB_op),
        .A(WB_A),
        .B(WB_B),
        .out(WB_data)
    );

endmodule