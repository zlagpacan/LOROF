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
    parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3,
    parameter MDU_RESULT_CACHE_ENTRIES = 4,
    parameter LOG_MDU_RESULT_CACHE_ENTRIES = $clog2(MDU_RESULT_CACHE_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // MDU pipeline issue
    input logic                         issue_valid,
    input logic [2:0]                   issue_op,
    input logic                         issue_A_forward,
    input logic                         issue_A_is_zero,
    input logic [LOG_PR_COUNT-1:0]      issue_A_PR,
    input logic                         issue_B_forward,
    input logic                         issue_B_is_zero,
    input logic [LOG_PR_COUNT-1:0]      issue_B_PR,
    input logic [LOG_PR_COUNT-1:0]      issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]   issue_ROB_index,

    // MDU pipeline feedback to IQ
    output logic                        issue_ready,

    // reg read data from PRF
    input logic         A_reg_read_resp_valid,
    input logic [31:0]  A_reg_read_resp_data,
    input logic         B_reg_read_resp_valid,
    input logic [31:0]  B_reg_read_resp_data,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // writeback feedback from
    input logic                         WB_ready
);
    // ----------------------------------------------------------------
    // Control Signals:

    logic stall_WB;
    logic stall_EX;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                           valid_OC;
    logic [2:0]                     op_OC;
    logic                           A_forward_OC;
    logic                           A_is_reg_OC;
    logic [LOG_PR_COUNT-1:0]        A_PR_OC;
    logic                           B_forward_OC;
    logic                           B_is_reg_OC;
    logic [LOG_PR_COUNT-1:0]        B_PR_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

    logic operands_ready_OC;

    logic           enq_A_reg_valid;
    logic [31:0]    enq_A_reg_data;
    // logic           enq_A_reg_ready; // should always be 1
    logic           deq_A_reg_valid;
    logic [31:0]    deq_A_reg_data;
    logic           deq_A_reg_ready;

    logic           enq_B_reg_valid;
    logic [31:0]    enq_B_reg_data;
    // logic           enq_B_reg_ready; // should always be 1
    logic           deq_B_reg_valid;
    logic [31:0]    deq_B_reg_data;
    logic           deq_B_reg_ready;

    logic [LOG_PRF_BANK_COUNT-1:0]  enq_A_forward_bank;
    logic [LOG_PRF_BANK_COUNT-1:0]  enq_B_forward_bank;

    logic           enq_A_forward_valid;
    logic [31:0]    enq_A_forward_data;
    // logic           enq_A_forward_ready; // should always be 1
    logic           deq_A_forward_valid;
    logic [31:0]    deq_A_forward_data;
    logic           deq_A_forward_ready;

    logic           enq_B_forward_valid;
    logic [31:0]    enq_B_forward_data;
    // logic           enq_B_forward_ready; // should always be 1
    logic           deq_B_forward_valid;
    logic [31:0]    deq_B_forward_data;
    logic           deq_B_forward_ready;

    logic                           next_valid_EX;
    logic [2:0]                     next_op_EX;
    logic                           next_A_forward_EX;
    logic                           next_A_is_reg_EX;
    logic [LOG_PR_COUNT-1:0]        next_A_PR_EX;
    logic                           next_B_forward_EX;
    logic                           next_B_is_reg_EX;
    logic [LOG_PR_COUNT-1:0]        next_B_PR_EX;
    logic [LOG_PR_COUNT-1:0]        next_dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]     next_ROB_index_EX;

    // ----------------------------------------------------------------
    // EX Stage Signals:

    logic                           valid_EX;
    logic [2:0]                     op_EX;
    logic                           A_forward_EX;
    logic                           A_is_reg_EX;
    logic [LOG_PR_COUNT-1:0]        A_PR_EX;
    logic                           B_forward_EX;
    logic                           B_is_reg_EX;
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

    logic                           valid_WB;
    logic [2:0]                     op_WB;
    logic [LOG_PR_COUNT-1:0]        A_PR_WB;
    logic [31:0]                    A_data_WB;
    logic [LOG_PR_COUNT-1:0]        B_PR_WB;
    logic [31:0]                    B_data_WB;
    logic [LOG_PR_COUNT-1:0]        dest_PR_WB;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_WB;

    logic                           divider_hit_valid_WB;
    logic [31:0]                    divider_hit_data_WB;

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

    assign stall_WB = valid_WB & (~WB_ready | (op_WB[2] & ~(divider_done | divider_hit_valid_WB)));
    assign stall_EX = valid_EX & stall_WB;

    // ----------------------------------------------------------------
    // IS -> OC Buffer Logic:

    q_fast_ready #(
        .DATA_WIDTH(3 + 1 + 1 + LOG_PR_COUNT + 1 + 1 + LOG_PR_COUNT + LOG_PR_COUNT + LOG_ROB_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_op,
            issue_A_forward,
            ~(issue_A_forward | issue_A_is_zero),
            issue_A_PR,
            issue_B_forward,
            ~(issue_B_forward | issue_B_is_zero),
            issue_B_PR,
            issue_dest_PR,
            issue_ROB_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            op_OC,
            A_forward_OC,
            A_is_reg_OC,
            A_PR_OC,
            B_forward_OC,
            B_is_reg_OC,
            B_PR_OC,
            dest_PR_OC,
            ROB_index_OC
        }),
        .deq_ready(~stall_EX & operands_ready_OC)
    );

    // ----------------------------------------------------------------
    // OC Stage Logic:

    assign operands_ready_OC = 
        // A operand present
        (~A_is_reg_OC | A_reg_read_resp_valid | deq_A_reg_valid)
        &
        // B operand present
        (~B_is_reg_OC | B_reg_read_resp_valid | deq_B_reg_valid)
    ;

    // reg read data buffers:

    always_comb begin
        enq_A_reg_valid = A_reg_read_resp_valid;
        enq_A_reg_data = A_reg_read_resp_data;

        enq_B_reg_valid = B_reg_read_resp_valid;
        enq_B_reg_data = B_reg_read_resp_data;
    end

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) A_REG_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_A_reg_valid),
        .enq_data(enq_A_reg_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_A_reg_valid),
        .deq_data(deq_A_reg_data),
        .deq_ready(deq_A_reg_ready)
    );

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) B_REG_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_B_reg_valid),
        .enq_data(enq_B_reg_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_B_reg_valid),
        .deq_data(deq_B_reg_data),
        .deq_ready(deq_B_reg_ready)
    );

    // forward data buffers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            enq_A_forward_valid <= 1'b0;
            enq_A_forward_bank <= 0;
            enq_B_forward_valid <= 1'b0;
            enq_B_forward_bank <= 0;
        end
        else begin
            enq_A_forward_valid <= issue_valid & issue_ready & issue_A_forward;
            enq_A_forward_bank <= issue_A_PR[LOG_PRF_BANK_COUNT-1:0];
            enq_B_forward_valid <= issue_valid & issue_ready & issue_B_forward;
            enq_B_forward_bank <= issue_B_PR[LOG_PRF_BANK_COUNT-1:0];
        end
    end

    always_comb begin
        enq_A_forward_data = forward_data_by_bank[enq_A_forward_bank];
        enq_B_forward_data = forward_data_by_bank[enq_B_forward_bank];
    end

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) A_FORWARD_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_A_forward_valid),
        .enq_data(enq_A_forward_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_A_forward_valid),
        .deq_data(deq_A_forward_data),
        .deq_ready(deq_A_forward_ready)
    );

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) B_FORWARD_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_B_forward_valid),
        .enq_data(enq_B_forward_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_B_forward_valid),
        .deq_data(deq_B_forward_data),
        .deq_ready(deq_B_forward_ready)
    );

    always_comb begin
        next_valid_EX = valid_OC & operands_ready_OC;
        next_op_EX = op_OC;
        next_A_forward_EX = A_forward_OC;
        next_A_is_reg_EX = A_is_reg_OC;
        next_A_PR_EX = A_PR_OC;
        next_B_forward_EX = B_forward_OC;
        next_B_is_reg_EX = B_is_reg_OC;
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
            A_forward_EX <= 1'b0;
            A_is_reg_EX <= 1'b0;
            A_PR_EX <= '0;
            B_forward_EX <= 1'b0;
            B_is_reg_EX <= 1'b0;
            B_PR_EX <= '0;
            dest_PR_EX <= '0;
            ROB_index_EX <= '0;
        end
        else if (~stall_EX) begin
            valid_EX <= next_valid_EX;
            op_EX <= next_op_EX;
            A_forward_EX <= next_A_forward_EX;
            A_is_reg_EX <= next_A_is_reg_EX;
            A_PR_EX <= next_A_PR_EX;
            B_forward_EX <= next_B_forward_EX;
            B_is_reg_EX <= next_B_is_reg_EX;
            B_PR_EX <= next_B_PR_EX;
            dest_PR_EX <= next_dest_PR_EX;
            ROB_index_EX <= next_ROB_index_EX;
        end
    end

    // data gathering
    always_comb begin
        A_data_EX = ({32{A_is_reg_EX}} & deq_A_reg_data) | ({32{A_forward_EX}} & deq_A_forward_data);

        B_data_EX = ({32{B_is_reg_EX}} & deq_B_reg_data) | ({32{B_forward_EX}} & deq_B_forward_data);

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

        deq_A_reg_ready = valid_EX & A_is_reg_EX & ~stall_EX;
        deq_A_forward_ready = valid_EX & A_forward_EX & ~stall_EX;

        deq_B_reg_ready = valid_EX & B_is_reg_EX & ~stall_EX;
        deq_B_forward_ready = valid_EX & B_forward_EX & ~stall_EX;
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
            // both {DIV, DIVU, REM, REMU}
            valid_EX & op_EX[2] & valid_WB & op_WB[2]
            // same signedness
            & (op_EX[0] == op_WB[0])
            // same operands
            & (A_PR_EX == A_PR_WB)
            & (B_PR_EX == B_PR_WB);

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
            valid_WB <= 1'b0;
            op_WB <= '0;
            A_PR_WB <= '0;
            A_data_WB <= '0;
            B_PR_WB <= '0;
            B_data_WB <= '0;
            dest_PR_WB <= '0;
            ROB_index_WB <= '0;

            divider_hit_valid_WB <= 1'b0;
            divider_hit_data_WB <= '0;
        end
        else if (~stall_WB) begin
            valid_WB <= next_valid_WB;
            op_WB <= next_op_WB;
            A_PR_WB <= next_A_PR_WB;
            A_data_WB <= next_A_data_WB;
            B_PR_WB <= next_B_PR_WB;
            B_data_WB <= next_B_data_WB;
            dest_PR_WB <= next_dest_PR_WB;
            ROB_index_WB <= next_ROB_index_WB;

            divider_hit_valid_WB <= next_divider_hit_valid_WB;
            divider_hit_data_WB <= next_divider_hit_data_WB;
        end
    end

    always_comb begin
        WB_valid = valid_WB & (~op_WB[2] | divider_done | divider_hit_valid_WB);

        // mul
        if (~op_WB[2]) begin
            // MUL
            if (op_WB[1:0] == 2'b00) begin
                WB_data = multiplier_result[31:0];
            end
            // MULH*
            else begin
                WB_data = multiplier_result[63:32];
            end
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
                if (~op_WB[1]) begin
                    WB_data = divider_quotient;
                end
                // REM[U]
                else begin
                    WB_data = divider_remainder;
                end
            end
        end

        WB_PR = dest_PR_WB;
        WB_ROB_index = ROB_index_WB;
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
        else begin
            if (~stall_EX) begin
                multiplier_immediate <= $signed(multiplier_A33) * $signed(multiplier_B33);
            end
        end
    end
    // want to allow retiming along path multiplier_A33, multplier_B33 -> multiplier_immediate -> multiplier_result
    always_comb begin
        multiplier_result = multiplier_immediate;
    end
    
    // ----------------------------------------------------------------
    // Divider Logic:

    assign divider_clear = ~valid_WB | ~op_WB[2] | ~stall_WB | divider_hit_valid_WB;
    assign divider_is_signed = ~op_WB[0];

    div32_nonrestoring_skip DIVIDER (
        .CLK(CLK),
        .nRST(nRST),

        .clear(divider_clear),
        .is_signed(divider_is_signed),
        .done(divider_done),
        .stall_if_done(stall_WB),

        .A32_in(A_data_WB),
        .B32_in(B_data_WB),
        
        .quotient_out(divider_quotient),
        .remainder_out(divider_remainder)
    );

endmodule