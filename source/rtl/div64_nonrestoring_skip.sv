/*
    Filename: div64_nonrestoring_skip.sv
    Author: zlagpacan
    Description: RTL for 64-bit Non-Restoring Divider with msb Iteration Skipping
    Spec: LOROF/spec/design/div64_nonrestoring_skip.md
*/

module div64_nonrestoring_skip (

    // seq
    input logic CLK,
    input logic nRST,

    // fsm control
    input logic     clear,
    input logic     is_signed,
    output logic    done,
    input logic     stall_if_done,

    // inputs
    input logic [63:0]  A64_in,
    input logic [63:0]  B64_in,

    // outputs
    output logic [63:0] quotient_out,
    output logic [63:0] remainder_out
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

    logic [64:0] A_abs, next_A_abs;

    logic [64:0] B_abs;
    logic [64:0] B_abs_neg;

    logic [5:0] msb_index, next_msb_index;
    logic [63:0] msb_mask, next_msb_mask;

    logic [5:0] counter_index, next_counter_index;

    logic [64:0] accumulator_reg, next_accumulator_reg;
    logic [63:0] quotient_reg, next_quotient_reg;
    
    // ----------------------------------------------------------------
    // Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            state <= DIV_INIT;
            A_is_neg <= 1'b0;
            B_is_neg <= 1'b0;
            B_is_zero <= 1'b0;
            A_abs <= 65'h0;
            B_abs <= 65'h0;
            B_abs_neg <= 65'h0;
            msb_index <= 6'h0;
            msb_mask <= '0;
            counter_index <= 6'h0;
            accumulator_reg <= 65'h0;
            quotient_reg <= 64'h0;
        end
        else begin
            if (clear) begin
                state <= DIV_INIT;
            end
            else begin
                state <= next_state;
            end

            A_is_neg <= is_signed & A64_in[63];
            B_is_neg <= is_signed & B64_in[63];
            B_is_zero <= (B64_in == 0);

            A_abs <= next_A_abs;
            if (is_signed & B64_in[63]) begin
                B_abs <= -{1'b1, B64_in};
                B_abs_neg <= {1'b1, B64_in};
            end
            else begin
                B_abs <= {1'b0, B64_in};
                B_abs_neg <= -{1'b0, B64_in};
            end

            if (state == DIV_INIT) begin
                msb_index <= next_msb_index;
                msb_mask <= next_msb_mask;
                counter_index <= next_msb_index;
            end
            else begin
                counter_index <= counter_index - 1;
            end

            accumulator_reg <= next_accumulator_reg;
            quotient_reg <= next_quotient_reg;
        end
    end

    pe_msb #(
        .WIDTH(64), .USE_ONE_HOT(0), .USE_COLD(0), .USE_INDEX(1)
    ) PE_MSB (
        .req_vec(next_A_abs[63:0]),
        .ack_mask(next_msb_mask),
        .ack_index(next_msb_index)
    );

    always_comb begin
        if (is_signed & A64_in[63]) begin
            next_A_abs = -{1'b1, A64_in};
        end
        else begin
            next_A_abs = A64_in;
        end

        case (state)

            default: begin // DIV_INIT
                done = 1'b0;

                next_state = DIV_ITERS;
                next_accumulator_reg = 65'h0;
                next_quotient_reg = next_A_abs;
            end

            DIV_ITERS: begin
                done = 1'b0;

                if (B_is_zero) begin
                    next_state = DIV_DONE;
                    next_accumulator_reg = A64_in;
                    next_quotient_reg = 64'hFFFF_FFFF_FFFF_FFFF;
                end
                else if (A_abs < B_abs) begin
                    next_state = DIV_DONE;
                    next_accumulator_reg = A64_in;
                    next_quotient_reg = 64'h0;
                end
                else begin
                    if (counter_index == 0) begin
                        next_state = DIV_CORRECTION;
                    end
                    else begin
                        next_state = DIV_ITERS;
                    end

                    if (accumulator_reg[64]) begin
                        next_accumulator_reg = {accumulator_reg[63:0], quotient_reg[msb_index]} + B_abs;
                    end
                    else begin
                        next_accumulator_reg = {accumulator_reg[63:0], quotient_reg[msb_index]} + B_abs_neg;
                    end
                    next_quotient_reg = {quotient_reg[62:0], ~next_accumulator_reg[64]} & msb_mask;
                end
            end

            DIV_CORRECTION: begin
                done = 1'b0;

                next_state = DIV_DONE;

                next_accumulator_reg = accumulator_reg + (B_abs & {65{accumulator_reg[64]}});
                if (A_is_neg) begin
                    next_accumulator_reg = -$signed(next_accumulator_reg);
                end

                if (A_is_neg ^ B_is_neg) begin
                    next_quotient_reg = -$signed(quotient_reg);
                end
                else begin
                    next_quotient_reg = quotient_reg;
                end
            end

            DIV_DONE: begin
                done = 1'b1;

                if (stall_if_done) begin
                    next_state = DIV_DONE;
                end else begin
                    next_state = DIV_INIT;
                end

                // don't cares (reg's already have values)
                next_accumulator_reg = 65'h0;
                next_quotient_reg = next_A_abs;
            end

        endcase

        quotient_out = quotient_reg;
        remainder_out = accumulator_reg[63:0];
    end

endmodule