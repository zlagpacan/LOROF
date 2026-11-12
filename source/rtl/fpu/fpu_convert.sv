/*
    Filename: fpu_convert.sv
    Author: zlagpacan
    Description: FPU Conversion Instructions
    Spec: LOROF/spec/design/fpu_convert.md
*/

`include "fpp.vh"
`include "corep.vh"

module fpu_convert #(

) (
    // seq
    input logic CLK,
    input logic nRST,

    // input control
    input logic             in_valid,
    input corep::pr_t       in_dest_pr,
    input corep::rob_idx_t  in_rob_idx,

    output logic            in_ready,

    // instr components
    input logic [6:0]       in_funct7,
    input logic [4:0]       in_funct5,
    input logic [2:0]       in_instr_rm,
    input logic [2:0]       in_fcsr_rm,

    // fp input
    input fpp::double_t     in_A_d,
    input fpp::single_t     in_A_s_boxed, // post NaN-box check

    // output control
    output logic                out_valid,
    output corep::pr_t          out_dest_pr,
    output corep::rob_idx_t     out_rob_idx,

    input logic                 out_ready,

    // fp output
    output fpp::double_t        out_result_d,
    output fpp::fpu_except_t    out_except
);

    // 1x reg in middle

    // possible exceptions
        // fp -> int
            // NV, NX

        // int -> fp
            // OF, NX

        // fp -> fp
            // NV, OF, UF, NX
            // only double -> single
            // single -> double is always exact

    // ----------------------------------------------------------------
    // Signals:

    // reg signals
    logic pass_reg;

    fpp::double_t        next_out_result_d;
    fpp::fpu_except_t    next_out_except;

    // helper signals
    logic in_A_is_nan_s;
    logic in_A_nan_is_snan_s;
    logic in_A_is_inf_s;
    logic [23-1:0] in_A_mant_reversed_s;
    logic [$clog2(23)-1:0] in_A_first_trailing_1_s;

    logic in_A_is_nan_d;
    logic in_A_nan_is_snan_d;
    logic in_A_is_inf_d;
    logic [52-1:0] in_A_mant_reversed_d;
    logic [$clog2(52)-1:0] in_A_first_trailing_1_d;

    // ----------------------------------------------------------------
    // Logic:

    // control logic
    always_comb begin
        pass_reg = ~out_valid | out_ready;
        in_ready = pass_reg;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            out_valid <= 1'b0;
            out_dest_pr <= 0;
            out_dest_rob_idx <= 0;

            out_result_d <= 64'h0;
            out_except <= 5'h0;
        end
        else if (pass_reg) begin
            out_valid <= in_valid;
            out_dest_pr <= in_dest_pr;
            out_rob_idx <= in_rob_idx;

            out_result_d <= next_out_result_d;
            out_except <= next_out_except;
        end
    end

    // helper logic
    always_comb begin
        in_A_is_nan_s = fpp::is_nan_s(in_A_s_boxed);
        in_A_nan_is_snan_s = fpp::nan_is_snan_s(in_A_s_boxed);
        in_A_is_inf_s = fpp::is_inf_s(in_A_s_boxed);
        in_A_mant_reversed_s = fpp::mant_reverse_s(in_A_s_boxed.mant);
        
        in_A_is_nan_d = fpp::is_nan_d(in_A_d);
        in_A_nan_is_snan_d = fpp::nan_is_snan_d(in_A_d);
        in_A_is_inf_d = fpp::is_inf_d(in_A_d);
        in_A_mant_reversed_d = fpp::mant_reverse_d(in_A_d.mant);
    end
    pe_lsb_tree #(
        .WIDTH(23)
    ) IN_A_FIRST_TRAILING_1_S_PE (
        .req_vec(in_A_mant_reversed_s),
        .ack_valid(),
        .ack_index(in_A_first_trailing_1_s)
    );
    pe_lsb_tree #(
        .WIDTH(52)
    ) IN_A_FIRST_TRAILING_1_D_PE (
        .req_vec(in_A_mant_reversed_d),
        .ack_valid(),
        .ack_index(in_A_first_trailing_1_d)
    );

    // conversion logic
    always_comb begin

        // activate exception flags where relevant in case
        next_out_except.NV = 1'b0;
        next_out_except.DZ = 1'b0;
        next_out_except.OF = 1'b0;
        next_out_except.UF = 1'b0;
        next_out_except.NX = 1'b0;

        casez (funct7)

            7'b0100000: begin
                // double -> single
                // FCVT.S.D

                // funct5 = 5'b00001 but don't care


            end

            7'b0100001: begin
                // single -> double
                // FCVT.D.S

                // funct5 = 5'b00000 but don't care

                // special case NaN -> sNaN NV, output cNaN
                if (in_A_is_nan_s) begin
                    next_out_result_d = fpp::CNAN_S;
                    next_out_except.NV = in_A_nan_is_snan_s;
                end

                // special case inf
                else if (in_A_is_inf_s) begin
                    next_out_result_d.sign = in_A_s_boxed.sign;
                    next_out_result_d.exp = 11'h7FF;
                    next_out_result_d.mant = 52'h0_0000_0000_0000;
                end

                // special case zero or subnormal
                else if (in_A_s_boxed.exp == 8'h00) begin
                    if (in_A_s_boxed.mant == 23'h000000) begin
                        // special case zero
                        next_out_result_d.sign = in_A_s_boxed.sign;
                        next_out_result_d.exp = 11'h000;
                        next_out_result_d.mant = 52'h0_0000_0000_0000;
                    end
                    else begin
                        // special case subnormal
                        next_out_result_d.sign = in_A_s_boxed.sign;
                        next_out_result_d.exp = 11'b011_1000_0000 - in_A_first_trailing_1_s;
                        next_out_result_d.mant = in_A_s_boxed.mant << (52-23+1 + in_A_first_trailing_1_s);
                    end
                end

                // standard case single -> double
                else begin
                    next_out_result_d.sign = in_A_s_boxed.sign;
                    next_out_result_d.exp = in_A_s_boxed.exp + 11'b011_1000_0000;
                    next_out_result_d.mant = {in_A_s_boxed.mant, 29'h0};
                end
            end

            7'b1100000: begin
                // single -> int
            end

            7'b1101000: begin
                // int -> single
            end

            7'b1100001: begin
                // double -> int
            end

            7'b1101001: begin
                // int -> double
            end

            default: begin
                // default to cNaN
                next_out_result_d = fpp::CNAN_D;
            end

        endcase
    end

endmodule