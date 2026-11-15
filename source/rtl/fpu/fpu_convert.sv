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

    // 2x elastic pipeline registers

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

    // Two-stage elastic pipeline control
    logic stage1_ready;
    logic stage2_ready;
    logic stage1_valid;
    logic stage1_int_to_fp;
    logic stage1_int_single;
    logic stage1_int_sign;
    logic stage1_int_nonzero;
    logic [63:0] stage1_int_magnitude;
    logic [5:0] stage1_int_msb_index;
    logic [2:0] stage1_int_rm;
    logic stage1_fp_to_int;
    logic stage1_fp_to_single;
    logic stage1_single_sign;
    logic stage1_single_subnormal;
    logic stage1_single_overflow_exact;
    logic [7:0] stage1_single_exp;
    logic [55:0] stage1_single_shifted_sig;
    logic [2:0] stage1_single_rm;
    logic stage1_fp_sign;
    logic stage1_fp_nan;
    logic stage1_fp_inf;
    logic stage1_fp_signed;
    logic stage1_fp_is_32;
    logic stage1_fp_overflow;
    logic stage1_fp_guard;
    logic stage1_fp_round;
    logic stage1_fp_sticky;
    logic [63:0] stage1_fp_magnitude;
    logic [2:0] stage1_fp_rm;
    logic stage1_int_to_fp_next;
    logic stage1_int_single_next;
    logic stage1_int_sign_next;
    logic stage1_int_nonzero_next;
    logic [63:0] stage1_int_magnitude_next;
    logic [5:0] stage1_int_msb_index_next;
    logic [2:0] stage1_int_rm_next;
    logic stage1_fp_to_int_next;
    logic stage1_fp_to_single_next;
    logic stage1_single_sign_next;
    logic stage1_single_subnormal_next;
    logic stage1_single_overflow_exact_next;
    logic [7:0] stage1_single_exp_next;
    logic [55:0] stage1_single_shifted_sig_next;
    logic [2:0] stage1_single_rm_next;
    logic stage1_fp_sign_next;
    logic stage1_fp_nan_next;
    logic stage1_fp_inf_next;
    logic stage1_fp_signed_next;
    logic stage1_fp_is_32_next;
    logic stage1_fp_overflow_next;
    logic stage1_fp_guard_next;
    logic stage1_fp_round_next;
    logic stage1_fp_sticky_next;
    logic [63:0] stage1_fp_magnitude_next;
    logic [2:0] stage1_fp_rm_next;
    logic [63:0] stage1_result;
    fpp::fpu_except_t stage1_except;
    corep::pr_t stage1_dest_pr;
    corep::rob_idx_t stage1_rob_idx;

    logic [63:0] stage2_normalized_integer;
    logic [24:0] stage2_rounded_sig_s;
    logic [53:0] stage2_rounded_sig_d;
    logic [63:0] stage2_integer_result;
    logic stage2_guard;
    logic stage2_round;
    logic stage2_sticky;
    logic stage2_inexact;
    logic stage2_round_up;
    fpp::double_t stage2_result;
    fpp::fpu_except_t stage2_except;

    fpp::double_t        next_out_result_d;
    fpp::fpu_except_t    next_out_except;

    // helper signals
    logic in_A_is_nan_s;
    logic in_A_nan_is_snan_s;
    logic in_A_is_inf_s;
    logic [23-1:0] in_A_mant_reversed_s;
    logic [31:0] in_A_mant_reversed_s_padded;
    logic [$clog2(23)-1:0] in_A_first_trailing_1_s;

    logic in_A_is_nan_d;
    logic in_A_nan_is_snan_d;
    logic in_A_is_inf_d;

    logic [2:0] final_rm;

    // Shared conversion datapath temporaries. Keep these at module scope so
    // the combinational block remains compatible with the project tool flow.
    logic [55:0] shifted_sig;
    logic [4:0] shift_amt;

    logic [63:0] integer_input;
    logic [63:0] integer_magnitude;
    logic [63:0] integer_magnitude_msb_first;
    logic integer_magnitude_nonzero;
    logic [$clog2(64)-1:0] integer_magnitude_msb_index;
    logic integer_signed;
    logic integer_is_32;
    logic integer_sign;
    integer bit_index;
    logic [52:0] fp_significand;
    logic [63:0] fp_to_int_magnitude;
    logic fp_to_int_overflow;
    logic fp_to_int_guard;
    logic fp_to_int_round;
    logic fp_to_int_sticky;
    // The largest finite double exponent is 1023 and the smallest
    // subnormal exponent is -1022, so an 11-bit signed value is sufficient.
    logic signed [10:0] fp_unbiased_exp;
    logic [5:0] fp_shift;
    logic fp_src_sign;
    logic fp_src_is_nan;
    logic fp_src_is_inf;

    // ----------------------------------------------------------------
    // Logic:

    // Control logic
    always_comb begin
        stage2_ready = ~out_valid | out_ready;
        stage1_ready = ~stage1_valid | stage2_ready;
        in_ready = stage1_ready;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            out_valid <= 1'b0;
            out_dest_pr <= 0;
            out_rob_idx <= 0;
            out_result_d <= 64'h0;
            out_except <= 5'h0;
        end
        else if (stage2_ready) begin
            out_valid <= stage1_valid;
            if (stage1_valid) begin
                out_dest_pr <= stage1_dest_pr;
                out_rob_idx <= stage1_rob_idx;
                out_result_d <= stage2_result;
                out_except <= stage2_except;
            end
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            stage1_valid <= 1'b0;
            stage1_int_to_fp <= 1'b0;
            stage1_int_single <= 1'b0;
            stage1_int_sign <= 1'b0;
            stage1_int_nonzero <= 1'b0;
            stage1_int_magnitude <= '0;
            stage1_int_msb_index <= '0;
            stage1_int_rm <= '0;
            stage1_fp_to_int <= 1'b0;
            stage1_fp_to_single <= 1'b0;
            stage1_single_sign <= 1'b0;
            stage1_single_subnormal <= 1'b0;
            stage1_single_overflow_exact <= 1'b0;
            stage1_single_exp <= '0;
            stage1_single_shifted_sig <= '0;
            stage1_single_rm <= '0;
            stage1_fp_sign <= 1'b0;
            stage1_fp_nan <= 1'b0;
            stage1_fp_inf <= 1'b0;
            stage1_fp_signed <= 1'b0;
            stage1_fp_is_32 <= 1'b0;
            stage1_fp_overflow <= 1'b0;
            stage1_fp_guard <= 1'b0;
            stage1_fp_round <= 1'b0;
            stage1_fp_sticky <= 1'b0;
            stage1_fp_magnitude <= '0;
            stage1_fp_rm <= '0;
            stage1_result <= '0;
            stage1_except <= '0;
            stage1_dest_pr <= '0;
            stage1_rob_idx <= '0;
        end
        else if (stage1_ready) begin
            stage1_valid <= in_valid;
            if (in_valid) begin
                stage1_int_to_fp <= stage1_int_to_fp_next;
                stage1_int_single <= stage1_int_single_next;
                stage1_int_sign <= stage1_int_sign_next;
                stage1_int_nonzero <= stage1_int_nonzero_next;
                stage1_int_magnitude <= stage1_int_magnitude_next;
                stage1_int_msb_index <= stage1_int_msb_index_next;
                stage1_int_rm <= stage1_int_rm_next;
                stage1_fp_to_int <= stage1_fp_to_int_next;
                stage1_fp_to_single <= stage1_fp_to_single_next;
                stage1_single_sign <= stage1_single_sign_next;
                stage1_single_subnormal <= stage1_single_subnormal_next;
                stage1_single_overflow_exact <= stage1_single_overflow_exact_next;
                stage1_single_exp <= stage1_single_exp_next;
                stage1_single_shifted_sig <= stage1_single_shifted_sig_next;
                stage1_single_rm <= stage1_single_rm_next;
                stage1_fp_sign <= stage1_fp_sign_next;
                stage1_fp_nan <= stage1_fp_nan_next;
                stage1_fp_inf <= stage1_fp_inf_next;
                stage1_fp_signed <= stage1_fp_signed_next;
                stage1_fp_is_32 <= stage1_fp_is_32_next;
                stage1_fp_overflow <= stage1_fp_overflow_next;
                stage1_fp_guard <= stage1_fp_guard_next;
                stage1_fp_round <= stage1_fp_round_next;
                stage1_fp_sticky <= stage1_fp_sticky_next;
                stage1_fp_magnitude <= stage1_fp_magnitude_next;
                stage1_fp_rm <= stage1_fp_rm_next;
                stage1_result <= next_out_result_d;
                stage1_except <= next_out_except;
                stage1_dest_pr <= in_dest_pr;
                stage1_rob_idx <= in_rob_idx;
            end
        end
    end

    always_comb begin
        stage2_result = stage1_result;
        stage2_except = stage1_except;
        stage2_normalized_integer = '0;
        stage2_rounded_sig_s = '0;
        stage2_rounded_sig_d = '0;
        stage2_integer_result = '0;
        stage2_guard = 1'b0;
        stage2_round = 1'b0;
        stage2_sticky = 1'b0;
        stage2_inexact = 1'b0;
        stage2_round_up = 1'b0;

        if (stage1_fp_to_int) begin
            stage2_except = '0;
            stage2_inexact = stage1_fp_guard | stage1_fp_round | stage1_fp_sticky;
            case (stage1_fp_rm)
                fpp::RM_RNE: stage2_round_up = stage1_fp_guard & (stage1_fp_round | stage1_fp_sticky | stage1_fp_magnitude[0]);
                fpp::RM_RTZ: stage2_round_up = 1'b0;
                fpp::RM_RDN: stage2_round_up = stage1_fp_sign & stage2_inexact;
                fpp::RM_RUP: stage2_round_up = ~stage1_fp_sign & stage2_inexact;
                fpp::RM_RMM: stage2_round_up = stage1_fp_guard;
                default: stage2_round_up = 1'b0;
            endcase
            stage2_integer_result = stage1_fp_magnitude + stage2_round_up;

            if (stage1_fp_nan) begin
                stage2_except.NV = 1'b1;
                stage2_integer_result = stage1_fp_is_32
                    ? (stage1_fp_signed ? 64'h0000_0000_7FFF_FFFF : 64'h0000_0000_FFFF_FFFF)
                    : (stage1_fp_signed ? 64'h7FFF_FFFF_FFFF_FFFF : 64'hFFFF_FFFF_FFFF_FFFF);
            end
            else if (stage1_fp_inf) begin
                stage2_except.NV = 1'b1;
                if (!stage1_fp_signed) stage2_integer_result = stage1_fp_sign ? 64'b0 : (stage1_fp_is_32 ? 64'h0000_0000_FFFF_FFFF : 64'hFFFF_FFFF_FFFF_FFFF);
                else if (stage1_fp_sign) stage2_integer_result = stage1_fp_is_32 ? 64'hFFFF_FFFF_8000_0000 : 64'h8000_0000_0000_0000;
                else stage2_integer_result = stage1_fp_is_32 ? 64'h0000_0000_7FFF_FFFF : 64'h7FFF_FFFF_FFFF_FFFF;
            end
            else if (!stage1_fp_signed && stage1_fp_sign && (stage1_fp_overflow || (stage2_integer_result != 0))) begin
                stage2_except.NV = 1'b1;
                stage2_integer_result = 64'b0;
            end
            else if (!stage1_fp_signed && (stage1_fp_overflow || (stage1_fp_is_32 && (|stage2_integer_result[63:32])))) begin
                stage2_except.NV = 1'b1;
                stage2_integer_result = stage1_fp_is_32 ? 64'h0000_0000_FFFF_FFFF : 64'hFFFF_FFFF_FFFF_FFFF;
            end
            else if (stage1_fp_signed && stage1_fp_sign) begin
                if (stage1_fp_overflow || (stage1_fp_is_32 && (stage2_integer_result > 64'h0000_0000_8000_0000)) || (!stage1_fp_is_32 && (stage2_integer_result > 64'h8000_0000_0000_0000))) begin
                    stage2_except.NV = 1'b1;
                    stage2_integer_result = stage1_fp_is_32 ? 64'hFFFF_FFFF_8000_0000 : 64'h8000_0000_0000_0000;
                end
                else stage2_integer_result = -stage2_integer_result;
            end
            else if (stage1_fp_signed && ((stage1_fp_is_32 && (stage1_fp_overflow || (stage2_integer_result >= 64'h0000_0000_8000_0000))) || (!stage1_fp_is_32 && (stage1_fp_overflow || (stage2_integer_result >= 64'h8000_0000_0000_0000))))) begin
                stage2_except.NV = 1'b1;
                stage2_integer_result = stage1_fp_is_32 ? 64'h0000_0000_7FFF_FFFF : 64'h7FFF_FFFF_FFFF_FFFF;
            end

            stage2_except.NX = stage2_inexact & ~stage2_except.NV;
            if (stage1_fp_is_32) stage2_integer_result = {{32{stage2_integer_result[31]}}, stage2_integer_result[31:0]};
            stage2_result = fpp::double_t'(stage2_integer_result);
        end
        else if (stage1_fp_to_single) begin
            stage2_except = '0;
            stage2_result.sign = 1'b1;
            stage2_result.exp = 11'h7FF;
            stage2_result.mant.upper = 20'hFFFFF;
            stage2_result.mant.single.sign = stage1_single_sign;
            stage2_guard = stage1_single_shifted_sig[31];
            stage2_round = stage1_single_shifted_sig[30];
            stage2_sticky = |stage1_single_shifted_sig[29:0];
            stage2_inexact = stage2_guard | stage2_round | stage2_sticky;
            case (stage1_single_rm)
                fpp::RM_RNE: stage2_round_up = stage2_guard & (stage2_round | stage2_sticky | stage1_single_shifted_sig[32]);
                fpp::RM_RTZ: stage2_round_up = 1'b0;
                fpp::RM_RDN: stage2_round_up = stage1_single_sign & stage2_inexact;
                fpp::RM_RUP: stage2_round_up = ~stage1_single_sign & stage2_inexact;
                fpp::RM_RMM: stage2_round_up = stage2_guard;
                default: stage2_round_up = 1'b0;
            endcase
            stage2_rounded_sig_s = {1'b0, stage1_single_shifted_sig[55:32]} + stage2_round_up;
            stage2_except.NX = stage2_inexact;
            if (stage1_single_subnormal) begin
                if (stage2_rounded_sig_s[23]) begin
                    stage2_result.mant.single.exp = 8'h01;
                    stage2_result.mant.single.mant = 23'b0;
                end
                else begin
                    stage2_result.mant.single.exp = 8'h00;
                    stage2_result.mant.single.mant = stage2_rounded_sig_s[22:0];
                    stage2_except.UF = stage2_inexact;
                end
            end
            else if (stage2_rounded_sig_s[24]) begin
                if (stage1_single_exp == 8'd254) begin
                    stage2_result.mant.single.exp = 8'hFF;
                    stage2_result.mant.single.mant = 23'b0;
                    stage2_except.OF = 1'b1;
                    stage2_except.NX = 1'b1;
                end
                else begin
                    stage2_result.mant.single.exp = stage1_single_exp + 1'b1;
                    stage2_result.mant.single.mant = stage2_rounded_sig_s[23:1];
                end
            end
            else begin
                stage2_result.mant.single.exp = stage1_single_exp;
                stage2_result.mant.single.mant = stage2_rounded_sig_s[22:0];
            end
            if (stage1_single_overflow_exact) begin
                stage2_except.OF = 1'b1;
                stage2_except.NX = 1'b1;
            end
        end
        else if (stage1_int_to_fp) begin
            stage2_except = '0;
            if (stage1_int_single) begin
                stage2_result.sign = 1'b1;
                stage2_result.exp = 11'h7FF;
                stage2_result.mant.upper = 20'hFFFFF;
                stage2_result.mant.single.sign = stage1_int_sign;
                if (stage1_int_nonzero) begin
                    stage2_normalized_integer = stage1_int_magnitude << (63-stage1_int_msb_index);
                    stage2_guard = stage2_normalized_integer[39];
                    stage2_round = stage2_normalized_integer[38];
                    stage2_sticky = |stage2_normalized_integer[37:0];
                    stage2_inexact = stage2_guard | stage2_round | stage2_sticky;
                    case (stage1_int_rm)
                        fpp::RM_RNE: stage2_round_up = stage2_guard & (stage2_round | stage2_sticky | stage2_normalized_integer[40]);
                        fpp::RM_RTZ: stage2_round_up = 1'b0;
                        fpp::RM_RDN: stage2_round_up = stage1_int_sign & stage2_inexact;
                        fpp::RM_RUP: stage2_round_up = ~stage1_int_sign & stage2_inexact;
                        fpp::RM_RMM: stage2_round_up = stage2_guard;
                        default: stage2_round_up = 1'b0;
                    endcase
                    stage2_rounded_sig_s = {1'b0, stage2_normalized_integer[63:40]} + stage2_round_up;
                    stage2_result.mant.single.exp = stage2_rounded_sig_s[24]
                        ? stage1_int_msb_index + 8'd128
                        : stage1_int_msb_index + 8'd127;
                    stage2_result.mant.single.mant = stage2_rounded_sig_s[24]
                        ? stage2_rounded_sig_s[23:1]
                        : stage2_rounded_sig_s[22:0];
                    stage2_except.NX = stage2_inexact;
                end
                else begin
                    stage2_result.mant.single.exp = 8'h00;
                    stage2_result.mant.single.mant = 23'b0;
                end
            end
            else begin
                stage2_result.sign = stage1_int_sign;
                if (stage1_int_nonzero) begin
                    stage2_normalized_integer = stage1_int_magnitude << (63-stage1_int_msb_index);
                    stage2_guard = stage2_normalized_integer[10];
                    stage2_round = stage2_normalized_integer[9];
                    stage2_sticky = |stage2_normalized_integer[8:0];
                    stage2_inexact = stage2_guard | stage2_round | stage2_sticky;
                    case (stage1_int_rm)
                        fpp::RM_RNE: stage2_round_up = stage2_guard & (stage2_round | stage2_sticky | stage2_normalized_integer[11]);
                        fpp::RM_RTZ: stage2_round_up = 1'b0;
                        fpp::RM_RDN: stage2_round_up = stage1_int_sign & stage2_inexact;
                        fpp::RM_RUP: stage2_round_up = ~stage1_int_sign & stage2_inexact;
                        fpp::RM_RMM: stage2_round_up = stage2_guard;
                        default: stage2_round_up = 1'b0;
                    endcase
                    stage2_rounded_sig_d = {1'b0, stage2_normalized_integer[63:11]} + stage2_round_up;
                    stage2_result.exp = stage1_int_msb_index + 11'd1023 + stage2_rounded_sig_d[53];
                    stage2_result.mant = stage2_rounded_sig_d[53] ? 52'b0 : stage2_rounded_sig_d[51:0];
                    stage2_except.NX = stage2_inexact;
                end
                else begin
                    stage2_result.exp = '0;
                    stage2_result.mant = '0;
                end
            end
        end
    end

    // rounding mode select
    always_comb begin
        if (in_instr_rm == fpp::RM_DYN) begin
            final_rm = in_fcsr_rm;
        end
        else begin
            final_rm = in_instr_rm;
        end
    end

    // helper logic
    always_comb begin
        in_A_is_nan_s = fpp::is_nan_s(in_A_s_boxed);
        in_A_nan_is_snan_s = fpp::nan_is_snan_s(in_A_s_boxed);
        in_A_is_inf_s = fpp::is_inf_s(in_A_s_boxed);
        in_A_mant_reversed_s = fpp::mant_reverse_s(in_A_s_boxed.mant);
        in_A_mant_reversed_s_padded = {9'b0, in_A_mant_reversed_s};
        
        in_A_is_nan_d = fpp::is_nan_d(in_A_d);
        in_A_nan_is_snan_d = fpp::nan_is_snan_d(in_A_d);
        in_A_is_inf_d = fpp::is_inf_d(in_A_d);
    end
    pe_lsb_tree #(
        .WIDTH(32)
    ) IN_A_FIRST_TRAILING_1_S_PE (
        .req_vec(in_A_mant_reversed_s_padded),
        .ack_valid(),
        .ack_index(in_A_first_trailing_1_s)
    );
    for (genvar g = 0; g < 64; g++) begin : REVERSE_INTEGER_MAGNITUDE
        assign integer_magnitude_msb_first[g] = integer_magnitude[63-g];
    end
    pe_lsb_tree #(
        .WIDTH(64)
    ) INTEGER_MAGNITUDE_MSB_PE (
        .req_vec(integer_magnitude_msb_first),
        .ack_valid(integer_magnitude_nonzero),
        .ack_index(integer_magnitude_msb_index)
    );

    // conversion logic
    always_comb begin

        // activate exception flags where relevant in case
        next_out_result_d = fpp::CNAN_D;
        shifted_sig = '0;
        shift_amt = 5'd0;
        integer_input = '0;
        integer_magnitude = '0;
        integer_signed = 1'b0;
        integer_is_32 = 1'b0;
        integer_sign = 1'b0;
        bit_index = 0;
        fp_significand = '0;
        fp_to_int_magnitude = '0;
        fp_to_int_overflow = 1'b0;
        fp_to_int_guard = 1'b0;
        fp_to_int_round = 1'b0;
        fp_to_int_sticky = 1'b0;
        fp_unbiased_exp = 0;
        fp_shift = 0;
        fp_src_sign = 1'b0;
        fp_src_is_nan = 1'b0;
        fp_src_is_inf = 1'b0;
        stage1_int_to_fp_next = 1'b0;
        stage1_int_single_next = 1'b0;
        stage1_int_sign_next = 1'b0;
        stage1_int_nonzero_next = 1'b0;
        stage1_int_magnitude_next = '0;
        stage1_int_msb_index_next = '0;
        stage1_int_rm_next = '0;
        stage1_fp_to_int_next = 1'b0;
        stage1_fp_to_single_next = 1'b0;
        stage1_single_sign_next = 1'b0;
        stage1_single_subnormal_next = 1'b0;
        stage1_single_overflow_exact_next = 1'b0;
        stage1_single_exp_next = '0;
        stage1_single_shifted_sig_next = '0;
        stage1_single_rm_next = '0;
        stage1_fp_sign_next = 1'b0;
        stage1_fp_nan_next = 1'b0;
        stage1_fp_inf_next = 1'b0;
        stage1_fp_signed_next = 1'b0;
        stage1_fp_is_32_next = 1'b0;
        stage1_fp_overflow_next = 1'b0;
        stage1_fp_guard_next = 1'b0;
        stage1_fp_round_next = 1'b0;
        stage1_fp_sticky_next = 1'b0;
        stage1_fp_magnitude_next = '0;
        stage1_fp_rm_next = '0;
        next_out_except.NV = 1'b0;
        next_out_except.DZ = 1'b0;
        next_out_except.OF = 1'b0;
        next_out_except.UF = 1'b0;
        next_out_except.NX = 1'b0;

        if ((in_funct7 == 7'b1100000) | (in_funct7 == 7'b1100001)) begin
            integer_signed = (in_funct5 == 5'b00000) | (in_funct5 == 5'b00010);
            integer_is_32 = (in_funct5 == 5'b00000) | (in_funct5 == 5'b00001);
            if (in_funct7 == 7'b1100000) begin
                fp_src_sign = in_A_s_boxed.sign;
                fp_src_is_nan = in_A_is_nan_s;
                fp_src_is_inf = in_A_is_inf_s;
                fp_unbiased_exp = (in_A_s_boxed.exp == 0)
                    ? -11'sd126
                    : $signed({4'b0, in_A_s_boxed.exp}) - 11'sd127;
                fp_significand = (in_A_s_boxed.exp == 0)
                    ? {1'b0, in_A_s_boxed.mant, 29'b0}
                    : {1'b1, in_A_s_boxed.mant, 29'b0};
            end
            else begin
                fp_src_sign = in_A_d.sign;
                fp_src_is_nan = in_A_is_nan_d;
                fp_src_is_inf = in_A_is_inf_d;
                fp_unbiased_exp = (in_A_d.exp == 0)
                    ? -11'sd1022
                    : $signed({1'b0, in_A_d.exp}) - 11'sd1023;
                fp_significand = (in_A_d.exp == 0) ? {1'b0, in_A_d.mant} : {1'b1, in_A_d.mant};
            end

            fp_to_int_overflow = fp_unbiased_exp > (integer_is_32 ? 11'sd31 : 11'sd63);

            if (fp_unbiased_exp >= 52) begin
                if (fp_unbiased_exp <= 11'sd63)
                    fp_to_int_magnitude = fp_significand << (fp_unbiased_exp[3:0] - 4'd4);
            end
            else if (fp_unbiased_exp >= -11'sd1) begin
                fp_shift = 6'd52 - fp_unbiased_exp[5:0];
                fp_to_int_magnitude = fp_significand >> fp_shift;
                fp_to_int_guard = fp_significand[fp_shift-1];
                fp_to_int_round = (fp_shift >= 2) ? fp_significand[fp_shift-2] : 1'b0;
                if (fp_shift >= 3) begin
                    for (bit_index = 0; bit_index < 53; bit_index = bit_index + 1)
                        if (bit_index < fp_shift-2) fp_to_int_sticky = fp_to_int_sticky | fp_significand[bit_index];
                end
            end
            else fp_to_int_sticky = |fp_significand;
            stage1_fp_to_int_next = 1'b1;
            stage1_fp_sign_next = fp_src_sign;
            stage1_fp_nan_next = fp_src_is_nan;
            stage1_fp_inf_next = fp_src_is_inf;
            stage1_fp_signed_next = integer_signed;
            stage1_fp_is_32_next = integer_is_32;
            stage1_fp_overflow_next = fp_to_int_overflow;
            stage1_fp_guard_next = fp_to_int_guard;
            stage1_fp_round_next = fp_to_int_round;
            stage1_fp_sticky_next = fp_to_int_sticky;
            stage1_fp_magnitude_next = fp_to_int_magnitude;
            stage1_fp_rm_next = final_rm;
        end
        else begin
        casez (in_funct7)

            7'b0100000: begin
                // double -> single
                // FCVT.S.D

                // funct5 = 5'b00001 but don't care

                // start w/ NaN box
                next_out_result_d.sign = 1'b1;
                next_out_result_d.exp = 11'h7FF;
                next_out_result_d.mant.upper = 20'hFFFFF;

                // special case NaN -> sNaN NV, output cNaN
                if (in_A_is_nan_d) begin
                    next_out_result_d.mant.single = fpp::CNAN_S;
                    next_out_except.NV = in_A_nan_is_snan_d;
                end

                // special case inf
                else if (in_A_is_inf_d) begin
                    next_out_result_d.mant.single.sign = in_A_d.sign;
                    next_out_result_d.mant.single.exp = 8'hFF;
                    next_out_result_d.mant.single.mant = 23'h000000;
                end

                // special case zero or subnormal
                else if (in_A_d.exp == 11'h000) begin

                    // special case zero
                    if (in_A_d.mant == 52'h0_0000_0000_0000) begin
                        next_out_result_d.mant.single.sign = in_A_d.sign;
                        next_out_result_d.mant.single.exp = 8'h00;
                        next_out_result_d.mant.single.mant = 23'h000000;
                    end

                    // special case subnormal
                    else begin
                        // automatic underflow
                        next_out_result_d.mant.single.sign = in_A_d.sign;
                        next_out_except.UF = 1'b1;
                        next_out_except.NX = 1'b1;

                        if (
                            (final_rm == fpp::RM_RDN) & (in_A_d.sign == 1'b1)
                            | (final_rm == fpp::RM_RUP) & (in_A_d.sign == 1'b0)
                        ) begin
                            // min subnormal single
                            next_out_result_d.mant.single.exp = 8'h00;
                            next_out_result_d.mant.single.mant = 23'h000001;
                        end
                        else begin
                            // zero
                            next_out_result_d.mant.single.exp = 8'h00;
                            next_out_result_d.mant.single.mant = 23'h000000;
                        end
                    end
                end

                // too small for singles
                    // smallest subnormal single: 2^-149
                    // -1023 + 874 = -149
                    // 11'd874 = 11'h36A
                else if (in_A_d.exp < 11'h36A) begin
                    // automatic underflow
                    next_out_result_d.mant.single.sign = in_A_d.sign;
                    next_out_except.UF = 1'b1;
                    next_out_except.NX = 1'b1;

                    if (
                        (final_rm == fpp::RM_RDN) & (in_A_d.sign == 1'b1)
                        | (final_rm == fpp::RM_RUP) & (in_A_d.sign == 1'b0)
                        | (in_A_d.exp == 11'h369) & (
                            (final_rm == fpp::RM_RNE) & (in_A_d.mant != 52'h0_0000_0000_0000)
                            | (final_rm == fpp::RM_RMM)
                        )
                    ) begin
                        // min subnormal single
                        next_out_result_d.mant.single.exp = 8'h00;
                        next_out_result_d.mant.single.mant = 23'h000001;
                    end
                    else begin
                        // zero
                        next_out_result_d.mant.single.exp = 8'h00;
                        next_out_result_d.mant.single.mant = 23'h000000;
                    end
                end

                // too big for singles
                    // largest normal single: 2^127
                    // -1023 + 1150 = 127
                    // 11'd1150 = 11'h47E
                else if (in_A_d.exp > 11'h47E) begin
                    // automatic overflow
                    next_out_result_d.mant.single.sign = in_A_d.sign;
                    next_out_except.OF = 1'b1;
                    next_out_except.NX = 1'b1;

                    if (
                        (final_rm == fpp::RM_RTZ)
                        | (final_rm == fpp::RM_RDN) & (in_A_d.sign == 1'b0)
                        | (final_rm == fpp::RM_RUP) & (in_A_d.sign == 1'b1)
                    ) begin
                        // max normal single
                        next_out_result_d.mant.single.exp = 8'hFE;
                        next_out_result_d.mant.single.mant = 23'h7FFFFF;
                    end
                    else begin
                        // inf
                        next_out_result_d.mant.single.exp = 8'hFF;
                        next_out_result_d.mant.single.mant = 23'h000000;
                    end
                end
                
                // normals and subnormals
                else begin : fcvt_remaining

                    // Determine shift for single subnormal conversion
                    // Single normal boundary: unbiased exponent = -126
                    // Double exponent field = 897
                    shift_amt = (in_A_d.exp < 11'd897)
                        ? (11'd897 - in_A_d.exp)
                        : 0;

                    // 53-bit significand with three rounding bits
                    shifted_sig = {1'b1, in_A_d.mant, 3'b000} >> shift_amt;

                    // Defer rounding and result formatting to the second stage.
                    stage1_fp_to_single_next = 1'b1;
                    stage1_single_sign_next = in_A_d.sign;
                    stage1_single_subnormal_next = in_A_d.exp < 11'd897;
                    stage1_single_exp_next = in_A_d.exp - 11'd896;
                    stage1_single_overflow_exact_next =
                        (in_A_d.exp == 11'h47E) &
                        (in_A_d.mant[51:29] == 23'h7FFFFF) &
                        (|in_A_d.mant[28:0]);
                    stage1_single_shifted_sig_next = shifted_sig;
                    stage1_single_rm_next = final_rm;
                end
            end

            7'b0100001: begin
                // single -> double
                // FCVT.D.S

                // funct5 = 5'b00000 but don't care

                // special case NaN -> sNaN NV, output cNaN
                if (in_A_is_nan_s) begin
                    next_out_result_d = fpp::CNAN_D;
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

                    // special case zero
                    if (in_A_s_boxed.mant == 23'h000000) begin
                        next_out_result_d.sign = in_A_s_boxed.sign;
                        next_out_result_d.exp = 11'h000;
                        next_out_result_d.mant = 52'h0_0000_0000_0000;
                    end

                    // special case subnormal
                    else begin
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

            7'b1101000, 7'b1101001: begin
                // Register the absolute value and its leading-one index here.
                // Normalization, rounding, and result formatting happen after
                // the pipeline register.
                integer_signed = (in_funct5 == 5'b00000) | (in_funct5 == 5'b00010);
                integer_is_32 = (in_funct5 == 5'b00000) | (in_funct5 == 5'b00001);
                integer_input = in_A_d;
                if (integer_is_32)
                    integer_input = integer_signed
                        ? {{32{in_A_d[31]}}, in_A_d[31:0]}
                        : {32'b0, in_A_d[31:0]};
                integer_magnitude = (integer_signed && integer_input[63])
                    ? -integer_input
                    : integer_input;
                integer_sign = integer_signed && integer_input[63];

                stage1_int_to_fp_next = 1'b1;
                stage1_int_single_next = (in_funct7 == 7'b1101000);
                stage1_int_sign_next = integer_sign;
                stage1_int_nonzero_next = integer_magnitude_nonzero;
                stage1_int_magnitude_next = integer_magnitude;
                stage1_int_msb_index_next = 6'd63 - integer_magnitude_msb_index;
                stage1_int_rm_next = final_rm;
            end

            default: begin
                // default to cNaN
                next_out_result_d = fpp::CNAN_D;
            end

        endcase
        end
    end

endmodule
