/*
    Filename: mdu_pipeline.sv
    Author: zlagpacan
    Description: RTL for Mul-Div Unit Pipeline
    Spec: LOROF/spec/design/mdu_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module mdu_pipeline #(
    parameter IS_OC_BUFFER_SIZE = 2,
    parameter OC_ENTRIES = IS_OC_BUFFER_SIZE + 1,
    parameter FAST_FORWARD_PIPE_COUNT = 4,
    parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT),
    parameter MDU_RESULT_CACHE_ENTRIES = 4,
    parameter LOG_MDU_RESULT_CACHE_ENTRIES = $clog2(MDU_RESULT_CACHE_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // MDU pipeline issue
    input logic                                     issue_valid,
    input logic [2:0]                               issue_op,
    input logic                                     issue_A_is_reg,
    input logic                                     issue_A_is_bus_forward,
    input logic                                     issue_A_is_fast_forward,
    input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]   issue_A_fast_forward_pipe,
    input logic [LOG_PR_COUNT-1:0]                  issue_A_PR,
    input logic                                     issue_B_is_reg,
    input logic                                     issue_B_is_bus_forward,
    input logic                                     issue_B_is_fast_forward,
    input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]   issue_B_fast_forward_pipe,
    input logic [LOG_PR_COUNT-1:0]                  issue_B_PR,
    input logic [LOG_PR_COUNT-1:0]                  issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]               issue_ROB_index,

    // MDU pipeline feedback to IQ
    output logic                        issue_ready,

    // reg read data from PRF
    input logic         A_reg_read_resp_valid,
    input logic [31:0]  A_reg_read_resp_data,
    input logic         B_reg_read_resp_valid,
    input logic [31:0]  B_reg_read_resp_data,

    // bus forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] bus_forward_data_by_bank,

    // fast forward data
    input logic [FAST_FORWARD_PIPE_COUNT-1:0]           fast_forward_data_valid_by_pipe,
    input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0]     fast_forward_data_by_pipe,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // writeback backpressure from PRF
    input logic                         WB_ready
);
    // ----------------------------------------------------------------
    // Control Signals:

    logic stall_MUL_WB;
    logic stall_DIV_WB;
    logic stall_EX;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                           valid_OC;
    logic [2:0]                     op_OC;
    logic [LOG_PR_COUNT-1:0]        A_PR_OC;
    logic [LOG_PR_COUNT-1:0]        B_PR_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

    logic A_collected_OC;
    logic B_collected_OC;
    logic operands_collected_OC;

    logic                           next_valid_EX;
    logic [2:0]                     next_op_EX;
    logic [LOG_PR_COUNT-1:0]        next_A_PR_EX;
    logic [LOG_PR_COUNT-1:0]        next_B_PR_EX;
    logic [LOG_PR_COUNT-1:0]        next_dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]     next_ROB_index_EX;

    // ----------------------------------------------------------------
    // EX Stage Signals:

    logic                           valid_EX;
    logic [2:0]                     op_EX;
    logic [LOG_PR_COUNT-1:0]        A_PR_EX;
    logic [LOG_PR_COUNT-1:0]        B_PR_EX;
    logic [LOG_PR_COUNT-1:0]        dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_EX;
    
    logic [31:0]                    A_data_EX;
    logic                           A_msb_EX;
    
    logic [31:0]                    B_data_EX;
    logic                           B_msb_EX;

    logic                           next_valid_WB;
    logic [2:0]                     next_op_WB;
    logic [LOG_PR_COUNT-1:0]        next_A_PR_WB;
    logic [31:0]                    next_A_data_WB;
    logic [LOG_PR_COUNT-1:0]        next_B_PR_WB;
    logic [31:0]                    next_B_data_WB;
    logic [LOG_PR_COUNT-1:0]        next_dest_PR_WB;
    logic [LOG_ROB_ENTRIES-1:0]     next_ROB_index_WB;

    logic                           next_divider_hit_valid_WB;
    logic [31:0]                    next_divider_hit_data_WB;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    // separate MUL_WB and DIV_WB paths:
    logic                           valid_MUL_WB;
    logic [1:0]                     op_MUL_WB;
    logic [LOG_PR_COUNT-1:0]        dest_PR_MUL_WB;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_MUL_WB;

    logic                           valid_DIV_WB;
    logic [1:0]                     op_DIV_WB;
    logic [LOG_PR_COUNT-1:0]        A_PR_DIV_WB;
    logic [31:0]                    A_data_DIV_WB;
    logic [LOG_PR_COUNT-1:0]        B_PR_DIV_WB;
    logic [31:0]                    B_data_DIV_WB;
    logic [LOG_PR_COUNT-1:0]        dest_PR_DIV_WB;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_DIV_WB;

    logic                           divider_hit_valid_WB;
    logic [31:0]                    divider_hit_data_WB;

    logic mul_selected_WB;
    logic div_selected_WB;

    // ----------------------------------------------------------------
    // Multiplier Signals:

    logic [32:0] multiplier_A33;
    logic [32:0] multiplier_B33;
    logic [63:0] multiplier_immediate;
    logic [63:0] multiplier_result;

    // ----------------------------------------------------------------
    // Divider Signals:

    logic divider_clear;
    logic divider_is_signed;
    logic divider_done;

    logic [31:0] divider_quotient;
    logic [31:0] divider_remainder;

    // ----------------------------------------------------------------
    // Control Logic: 

    assign stall_MUL_WB = valid_MUL_WB & (~WB_ready | ~mul_selected_WB);
    assign stall_DIV_WB = valid_DIV_WB & (~WB_ready | ~div_selected_WB);
    assign stall_EX = valid_EX & (~op_OC[2] & stall_MUL_WB | op_OC[2] & stall_DIV_WB);

    // ----------------------------------------------------------------
    // IS -> OC Buffer Logic:

    q_fast_ready #(
        .DATA_WIDTH(3 + LOG_PR_COUNT + LOG_PR_COUNT + LOG_PR_COUNT + LOG_ROB_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_op,
            issue_A_PR,
            issue_B_PR,
            issue_dest_PR,
            issue_ROB_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            op_OC,
            A_PR_OC,
            B_PR_OC,
            dest_PR_OC,
            ROB_index_OC
        }),
        .deq_ready(~stall_EX & operands_collected_OC)
    );

    // ----------------------------------------------------------------
    // OC Stage Logic:

    assign operands_collected_OC = A_collected_OC & B_collected_OC;
    
    operand_collector #(
        .OC_ENTRIES(OC_ENTRIES),
        .FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT)
    ) A_OPERAND_COLLECTOR (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid & issue_ready),
        .enq_is_reg(issue_A_is_reg),
        .enq_is_bus_forward(issue_A_is_bus_forward),
        .enq_is_fast_forward(issue_A_is_fast_forward),
        .enq_fast_forward_pipe(issue_A_fast_forward_pipe),
        .enq_bank(issue_A_PR[LOG_PRF_BANK_COUNT-1:0]),
        .reg_read_resp_valid(A_reg_read_resp_valid),
        .reg_read_resp_data(A_reg_read_resp_data),
        .bus_forward_data_by_bank(bus_forward_data_by_bank),
        .fast_forward_data_valid_by_pipe(fast_forward_data_valid_by_pipe),
        .fast_forward_data_by_pipe(fast_forward_data_by_pipe),
        .operand_collected(A_collected_OC),
        .operand_collected_ack(next_valid_EX & ~stall_EX),
        .operand_data(A_data_EX),
        .operand_data_ack(valid_EX & ~stall_EX)
    );
    
    operand_collector #(
        .OC_ENTRIES(OC_ENTRIES),
        .FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT)
    ) B_OPERAND_COLLECTOR (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid & issue_ready),
        .enq_is_reg(issue_B_is_reg),
        .enq_is_bus_forward(issue_B_is_bus_forward),
        .enq_is_fast_forward(issue_B_is_fast_forward),
        .enq_fast_forward_pipe(issue_B_fast_forward_pipe),
        .enq_bank(issue_B_PR[LOG_PRF_BANK_COUNT-1:0]),
        .reg_read_resp_valid(B_reg_read_resp_valid),
        .reg_read_resp_data(B_reg_read_resp_data),
        .bus_forward_data_by_bank(bus_forward_data_by_bank),
        .fast_forward_data_valid_by_pipe(fast_forward_data_valid_by_pipe),
        .fast_forward_data_by_pipe(fast_forward_data_by_pipe),
        .operand_collected(B_collected_OC),
        .operand_collected_ack(next_valid_EX & ~stall_EX),
        .operand_data(B_data_EX),
        .operand_data_ack(valid_EX & ~stall_EX)
    );

    always_comb begin
        next_valid_EX = valid_OC & operands_collected_OC;
        next_op_EX = op_OC;
        next_A_PR_EX = A_PR_OC;
        next_B_PR_EX = B_PR_OC;
        next_dest_PR_EX = dest_PR_OC;
        next_ROB_index_EX = ROB_index_OC;
    end

    // ----------------------------------------------------------------
    // EX Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            valid_EX <= 1'b0;
            op_EX <= '0;
            A_PR_EX <= '0;
            B_PR_EX <= '0;
            dest_PR_EX <= '0;
            ROB_index_EX <= '0;
        end
        else if (~stall_EX) begin
            valid_EX <= next_valid_EX;
            op_EX <= next_op_EX;
            A_PR_EX <= next_A_PR_EX;
            B_PR_EX <= next_B_PR_EX;
            dest_PR_EX <= next_dest_PR_EX;
            ROB_index_EX <= next_ROB_index_EX;
        end
    end

    // data gathering
    always_comb begin

        // get bit 32 for signed 33b mul:

        // MULHU
        if (op_EX[1] & op_EX[0]) begin
            A_msb_EX = 1'b0;
            B_msb_EX = 1'b0;
        end
        // MULHSU
        else if (op_EX[1]) begin
            A_msb_EX = A_data_EX[31];
            B_msb_EX = 1'b0;
        end
        // MUL/MULHU
        else begin
            A_msb_EX = A_data_EX[31];
            B_msb_EX = B_data_EX[31];
        end
    end

    always_comb begin
        next_valid_WB = valid_EX;
        next_op_WB = op_EX;
        next_A_PR_WB = A_PR_EX;
        next_A_data_WB = A_data_EX;
        next_B_PR_WB = B_PR_EX;
        next_B_data_WB = B_data_EX;
        next_dest_PR_WB = dest_PR_EX;
        next_ROB_index_WB = ROB_index_EX;
    end

    always_comb begin
        next_divider_hit_valid_WB = 
            // EX is {DIV, DIVU, REM, REMU} and have a DIV_WB
            valid_EX & op_EX[2] & valid_DIV_WB
            // same signedness
            & (op_EX[0] == op_DIV_WB[0])
            // same operands
            & (A_PR_EX == A_PR_DIV_WB)
            & (B_PR_EX == B_PR_DIV_WB);

        // DIV[U]
        if (~op_EX[1]) begin
            next_divider_hit_data_WB = divider_quotient;
        end
        // REM[U]
        else begin
            next_divider_hit_data_WB = divider_remainder;
        end
    end

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            valid_MUL_WB <= 1'b0;
            op_MUL_WB <= 2'b00;
            dest_PR_MUL_WB <= 7'h00;
            ROB_index_MUL_WB <= 7'h00;

            valid_DIV_WB <= 1'b0;
            op_DIV_WB <= 2'b00;
            A_PR_DIV_WB <= 7'h00;
            A_data_DIV_WB <= 32'h00000000;
            B_PR_DIV_WB <= 7'h00;
            B_data_DIV_WB <= 32'h00000000;
            dest_PR_DIV_WB <= 7'h00;
            ROB_index_DIV_WB <= 7'h00;

            divider_hit_valid_WB <= 1'b0;
            divider_hit_data_WB <= 32'h00000000;
        end
        else begin
            if (~stall_MUL_WB) begin
                valid_MUL_WB <= next_valid_WB & ~next_op_WB[2];
                op_MUL_WB <= next_op_WB;
                dest_PR_MUL_WB <= next_dest_PR_WB;
                ROB_index_MUL_WB <= next_ROB_index_WB;
            end

            if (~stall_DIV_WB) begin
                valid_DIV_WB <= next_valid_WB & next_op_WB[2];
                op_DIV_WB <= next_op_WB;
                A_PR_DIV_WB <= next_A_PR_WB;
                A_data_DIV_WB <= next_A_data_WB;
                B_PR_DIV_WB <= next_B_PR_WB;
                B_data_DIV_WB <= next_B_data_WB;
                dest_PR_DIV_WB <= next_dest_PR_WB;
                ROB_index_DIV_WB <= next_ROB_index_WB;

                divider_hit_valid_WB <= next_divider_hit_valid_WB;
                divider_hit_data_WB <= next_divider_hit_data_WB;
            end
        end
    end

    // round-robing arbiter between MUL and DIV paths
    arbiter_rr #(
        .REQUESTOR_COUNT(2)
    ) MUL_DIV_ARBITER_RR (
        .CLK(CLK),
        .nRST(nRST),
        .req_vec({
            valid_MUL_WB & WB_ready,
            valid_DIV_WB & WB_ready & (divider_done | divider_hit_valid_WB)
        }),
        .req_present(),
        .ack_ready(WB_ready),
        .ack_one_hot({
            mul_selected_WB,
            div_selected_WB
        }),
        .ack_index()
    );

    always_comb begin
        WB_valid = valid_MUL_WB | (valid_DIV_WB & (divider_done | divider_hit_valid_WB));

        // mul
        if (mul_selected_WB) begin
            // MUL
            if (op_MUL_WB[1:0] == 2'b00) begin
                WB_data = multiplier_result[31:0];
            end
            // MULH*
            else begin
                WB_data = multiplier_result[63:32];
            end

            WB_PR = dest_PR_MUL_WB;
            WB_ROB_index = ROB_index_MUL_WB;
        end
        // div
        else begin
            // result cache
            if (divider_hit_valid_WB) begin
                WB_data = divider_hit_data_WB;
            end
            // divider
            else begin
                // DIV[U]
                if (~op_DIV_WB[1]) begin
                    WB_data = divider_quotient;
                end
                // REM[U]
                else begin
                    WB_data = divider_remainder;
                end
            end

            WB_PR = dest_PR_DIV_WB;
            WB_ROB_index = ROB_index_DIV_WB;
        end
    end

    // ----------------------------------------------------------------
    // Multiplier Logic:

    assign multiplier_A33 = {A_msb_EX, A_data_EX};
    assign multiplier_B33 = {B_msb_EX, B_data_EX};

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            multiplier_immediate <= 64'h0;
        end
        else if (~stall_EX) begin
            multiplier_immediate <= $signed(multiplier_A33) * $signed(multiplier_B33);
        end
    end
    // want to allow retiming along path multiplier_A33, multplier_B33 -> multiplier_immediate -> multiplier_result
    always_comb begin
        multiplier_result = multiplier_immediate;
    end
    
    // ----------------------------------------------------------------
    // Divider Logic:

    assign divider_clear = ~valid_DIV_WB | ~stall_DIV_WB | divider_hit_valid_WB;
    assign divider_is_signed = ~op_DIV_WB[0];

    div32_nonrestoring_skip DIVIDER (
        .CLK(CLK),
        .nRST(nRST),

        .clear(divider_clear),
        .is_signed(divider_is_signed),
        .done(divider_done),
        .stall_if_done(stall_DIV_WB),

        .A32_in(A_data_DIV_WB),
        .B32_in(B_data_DIV_WB),
        
        .quotient_out(divider_quotient),
        .remainder_out(divider_remainder)
    );

endmodule