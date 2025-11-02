/*
    Filename: div32_nonrestoring_skip.sv
    Author: zlagpacan
    Description: RTL for 32-bit Non-Restoring Divider with msb Iteration Skipping
    Spec: LOROF/spec/design/div32_nonrestoring_skip.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module div32_nonrestoring_skip (

    // seq
    input logic CLK,
    input logic nRST,

    // fsm control
    input logic     clear,
    input logic     is_signed,
    output logic    done,

    // inputs
    input logic [31:0]  A32_in,
    input logic [31:0]  B32_in,

    // outputs
    output logic [31:0] quotient_out,
    output logic [31:0] remainder_out
);

    // ----------------------------------------------------------------
    // Signals:

    typedef enum logic [1:0] {
        DIV_INIT,
        DIV_ITERS,
        DIV_CORRECTION,
        DIV_DONE
    } div_fsm_t;

    div_fsm_t state, next_state;

    logic A_is_neg;
    logic B_is_neg;

    logic B_is_zero;

    logic [32:0] A_abs, next_A_abs;

    logic [32:0] B_abs;
    logic [32:0] B_abs_neg;

    logic [4:0] msb_index, next_msb_index;
    logic [31:0] msb_mask, next_msb_mask;

    logic [32:0] accumulator_reg, next_accumulator_reg;
    logic [31:0] quotient_reg, next_quotient_reg;
    
    // ----------------------------------------------------------------
    // Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            state <= DIV_INIT;
            A_is_neg <= 1'b0;
            B_is_neg <= 1'b0;
            B_is_zero <= 1'b0;
            A_abs <= 33'h0;
            B_abs <= 33'h0;
            B_abs_neg <= 33'h0;
            msb_index <= 5'h0;
            msb_mask <= '0;
            accumulator_reg <= 33'h0;
            quotient_reg <= 32'h0;
        end
        else begin
            if (clear) begin
                state <= DIV_INIT;
            end
            else begin
                state <= next_state;
            end

            A_is_neg <= is_signed & A32_in[31];
            B_is_neg <= is_signed & B32_in[31];
            B_is_zero <= (B32_in == 0);

            A_abs <= next_A_abs;
            if (is_signed & B32_in[31]) begin
                B_abs <= -B32_in;
                B_abs_neg <= B32_in;
            end
            else begin
                B_abs <= B32_in;
                B_abs_neg <= -B32_in;
            end

            if (state == DIV_INIT) begin
                msb_index <= next_msb_index;
                msb_mask <= next_msb_mask;
            end
            else begin
                msb_index <= msb_index - 1;
            end

            accumulator_reg <= next_accumulator_reg;
            quotient_reg <= next_quotient_reg;
        end
    end

    pe_msb #(
        .WIDTH(32), .USE_ONE_HOT(0), .USE_COLD(0), .USE_INDEX(1)
    ) PE_MSB (
        .req_vec(next_A_abs),
        .ack_mask(next_msb_mask),
        .ack_index(next_msb_index)
    );

    always_comb begin
        if (is_signed & A32_in[31]) begin
            next_A_abs = -A32_in;
        end
        else begin
            next_A_abs = A32_in;
        end

        case (state)

            default: begin // DIV_INIT
                done = 1'b0;

                next_state = DIV_ITERS;
                next_accumulator_reg = 33'h0;
                next_quotient_reg = next_A_abs;
            end

            DIV_ITERS: begin
                done = 1'b0;

                if (B_is_zero) begin
                    next_state = DIV_DONE;
                    next_accumulator_reg = A32_in;
                    next_quotient_reg = 32'hFFFFFFFF;
                end
                else if (A_abs < B_abs) begin
                    next_state = DIV_DONE;
                    next_accumulator_reg = A32_in;
                    next_quotient_reg = 32'h0;
                end
                else begin
                    if (msb_index == 0) begin
                        next_state = DIV_DONE;
                    end
                    else begin
                        next_state = DIV_ITERS;
                    end

                    if (accumulator_reg[32]) begin
                        next_accumulator_reg = {accumulator_reg[31:0], quotient_reg[msb_index]} + B_abs;
                    end
                    else begin
                        next_accumulator_reg = {accumulator_reg[31:0], quotient_reg[msb_index]} + B_abs_neg;
                    end
                    next_quotient_reg = {quotient_reg[30:0], ~next_accumulator_reg[32]} & msb_mask;
                end
            end

            DIV_CORRECTION: begin
                done = 1'b0;

                next_state = DIV_DONE;

                next_accumulator_reg = accumulator_reg + (B_abs & {33{accumulator_reg[32]}});
                if (A_is_neg) begin
                    next_accumulator_reg = -next_accumulator_reg;
                end

                if (A_is_neg ^ B_is_neg) begin
                    next_quotient_reg = -quotient_reg; 
                end
                else begin
                    next_quotient_reg = quotient_reg; 
                end
            end

            DIV_DONE: begin
                done = 1'b1;

                next_state = DIV_INIT;

                // don't cares (reg's already have values)
                next_accumulator_reg = 33'h0;
                next_quotient_reg = next_A_abs;
            end

        endcase

        quotient_out = quotient_reg;
        remainder_out = accumulator_reg[31:0];
    end

endmodule