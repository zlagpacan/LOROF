/*
    Filename: fpu_arithmetic.sv
    Author: zlagpacan
    Description: FPU Arithmetic Instructions
    Spec: LOROF/spec/design/fpu_arithmetic.md
*/

`include "fpp.vh"
`include "corep.vh"

module fpu_arithmetic #(

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
    input fpp::double_t     in_B_d,
    input fpp::single_t     in_B_s_boxed, // post NaN-box check

    // output control
    output logic                out_valid,
    output corep::pr_t          out_dest_pr,
    output corep::rob_idx_t     out_rob_idx,
    input logic                 out_ready,

    // fp output
    output fpp::double_t        out_result_d,
    output fpp::fpu_except_t    out_except
);

    typedef enum logic [2:0] {OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_SQRT, OP_BAD} op_t;
    typedef enum logic [3:0] {SLOW_IDLE, SLOW_NORM_COUNT, SLOW_NORM_SHIFT, SLOW_START, SLOW_DIV, SLOW_SQRT, SLOW_PACK_PREP, SLOW_PACK_FINISH} slow_state_t;

    typedef struct packed {
        fpp::double_t result;
        fpp::fpu_except_t except;
    } packet_t;

    typedef struct packed {
        logic sign;
        logic [55:0] sig;
        logic signed [12:0] exp;
        logic single;
        logic subnormal;
        logic inexact;
        logic increment;
        logic overflow_to_inf;
    } round_pre_t;

    typedef struct packed {
        logic sign;
        logic zero;
        logic inf;
        logic nan;
        logic snan;
        logic [52:0] sig;
        logic signed [12:0] exp;
    } operand_t;

    // Fast elastic pipeline: decode, normalize-count, arithmetic/round, output.
    logic p0_valid, p0_ready;
    logic f0_valid, f0_ready;
    logic s1_valid, s2_valid, s3_valid, s4_valid, s5_valid, s6_valid, s7_valid;
    logic s1_ready, s2_ready, s3_ready, s4_ready, s5_ready, s6_ready, s7_ready, out_slot_ready;
    op_t s1_op;
    op_t p0_op;
    op_t f0_op;
    logic s1_single;
    logic p0_single;
    logic f0_single;
    logic [2:0] s1_rm;
    logic [2:0] p0_rm;
    logic [2:0] f0_rm;
    operand_t s1_A_norm, s1_B_norm;
    operand_t p0_A_decoded, p0_B_decoded;
    operand_t f0_A_decoded, f0_B_decoded, f0_A_norm, f0_B_norm;
    logic [5:0] p0_A_norm_count, p0_B_norm_count;
    logic [5:0] f0_A_norm_count, f0_B_norm_count;
    corep::pr_t p0_dest_pr;
    corep::rob_idx_t p0_rob_idx;
    corep::pr_t f0_dest_pr;
    corep::rob_idx_t f0_rob_idx;
    corep::pr_t s1_dest_pr;
    corep::rob_idx_t s1_rob_idx;
    packet_t s2_special_packet, s3_special_packet, s4_special_packet, s5_special_packet, s6_special_packet, s7_packet, fast_packet;
    round_pre_t s6_round_pre;
    logic s2_round_needed, s3_round_needed, s3_normalize, s4_round_needed, s4_normalize, s5_round_needed, s6_round_needed;
    logic fast_round_needed, s2_single, s3_single, s4_single, s5_single;
    logic [2:0] s2_rm;
    logic [2:0] s3_rm, s4_rm, s5_rm;
    logic s2_sign, s3_sign, s4_sign, s5_sign;
    logic signed [12:0] s2_exp, s3_exp, s4_exp, s5_exp;
    logic [55:0] s2_sig, s3_sig, s4_sig, s5_sig;
    corep::pr_t s2_dest_pr, s3_dest_pr, s4_dest_pr, s5_dest_pr, s6_dest_pr, s7_dest_pr;
    corep::rob_idx_t s2_rob_idx, s3_rob_idx, s4_rob_idx, s5_rob_idx, s6_rob_idx, s7_rob_idx;
    logic [5:0] s4_norm_count;
    logic s2_add_work, fast_add_work, fast_add_sign_a, fast_add_sign_b;
    logic s2_mul_work, s3_mul_work, fast_mul_work;
    logic s2_add_sign_a, s2_add_sign_b;
    logic [55:0] s2_add_a, s2_add_b;
    logic [35:0] s2_mul_p00, s2_mul_p01, s2_mul_p02;
    logic [35:0] s2_mul_p10, s2_mul_p11, s2_mul_p12;
    logic [35:0] s2_mul_p20, s2_mul_p21, s2_mul_p22;
    logic [71:0] s3_mul_row0;
    logic [71:0] s3_mul_row1, s3_mul_row2;
    logic [71:0] s2_mul_row0_comb;
    logic [71:0] s2_mul_row1_comb, s2_mul_row2_comb;
    logic [105:0] s4_mul_product;
    logic [35:0] mul_p00, mul_p01, mul_p02;
    logic [35:0] mul_p10, mul_p11, mul_p12;
    logic [35:0] mul_p20, mul_p21, mul_p22;
    logic [56:0] s2_add_sum;
    logic [55:0] s2_result_sig;
    logic signed [12:0] s2_result_exp;
    logic s2_result_sign, s2_result_round_needed;
    packet_t s2_result_packet;
    logic [5:0] normalize_count;
    logic signed [12:0] s5_norm_exp;
    logic [55:0] s5_norm_sig;

    // One independent iterative engine is shared by divide and square root.
    slow_state_t slow_state;
    logic slow_pending;
    op_t slow_op;
    operand_t slow_A_norm, slow_B_norm;
    logic [5:0] slow_A_norm_count, slow_B_norm_count;
    logic [5:0] slow_A_norm_count_comb, slow_B_norm_count_comb;
    packet_t slow_packet;
    logic [55:0] slow_pack_sig;
    round_pre_t slow_round_pre;
    corep::pr_t slow_dest_pr;
    corep::rob_idx_t slow_rob_idx;
    logic slow_single, slow_sign;
    logic [2:0] slow_rm;
    logic signed [12:0] slow_exp;
    logic [52:0] slow_divisor;
    logic [53:0] slow_remainder;
    logic [55:0] slow_quotient, slow_root;
    logic [111:0] slow_radicand;
    logic [57:0] slow_sqrt_remainder;
    logic [57:0] sqrt_trial, sqrt_remainder_next;
    logic [55:0] sqrt_root_next;
    logic [5:0] slow_count;

    op_t in_op;
    logic in_single, in_slow;
    logic in_slow_special;
    logic [2:0] in_rm;
    operand_t in_A_decoded, in_B_decoded;
    logic signed [12:0] calc_exp;
    logic [55:0] calc_sig;
    logic calc_sign, calc_zero;
    logic [55:0] add_A_ext, add_B_ext, add_ext;
    logic [56:0] add_sum;
    logic [12:0] align_shift;
    logic add_sign_b;
    logic [55:0] shifted_value;
    logic [52:0] div_num_initial;
    logic [53:0] div_rem_initial, div_remainder_next;
    logic [55:0] div_quotient_next;
    logic signed [12:0] div_exp_initial;
    logic [111:0] sqrt_rad_initial;
    logic signed [12:0] sqrt_exp_initial;
    logic [57:0] sqrt_trial_comb;
    logic [55:0] round_sig;
    logic [2:0] round_grs;
    logic [24:0] round_s;
    logic [53:0] round_d;
    logic round_lost, round_inexact, round_inc, round_subnormal;
    logic signed [12:0] round_exp;

    function automatic op_t decode_op(input logic [4:0] funct5);
        case (funct5)
            5'b00000: return OP_ADD;
            5'b00001: return OP_SUB;
            5'b00010: return OP_MUL;
            5'b00011: return OP_DIV;
            5'b01011: return OP_SQRT;
            default: return OP_BAD;
        endcase
    endfunction

    // Balanced leading-zero detection avoids a serial chain of shifts and
    // exponent decrements during normalization.
    function automatic logic [5:0] leading_zeros_53(input logic [52:0] value);
        logic [51:0] x;
        logic [5:0] count;
        begin
            // The implicit bit is exponent-derived and used to feed the
            // significand LZC through a deep priority chain.  Count the
            // fraction independently, then select the normalized count.
            if (value == '0) count = 6'd53;
            else if (value[52]) count = '0;
            else begin
                x = value[51:0];
                count = 6'd1;
                if (x[51:26] == 26'b0) begin count = count + 6'd26; x = x << 26; end
                if (x[51:39] == 13'b0) begin count = count + 6'd13; x = x << 13; end
                if (x[51:45] == 7'b0)  begin count = count + 6'd7;  x = x << 7;  end
                if (x[51:48] == 4'b0)  begin count = count + 6'd4;  x = x << 4;  end
                if (x[51:50] == 2'b0)  begin count = count + 6'd2;  x = x << 2;  end
                if (!x[51])            count = count + 6'd1;
            end
            return count;
        end
    endfunction

    function automatic logic [5:0] leading_zeros_56(input logic [55:0] value);
        logic [55:0] x;
        logic [5:0] count;
        begin
            x = value;
            count = '0;
            if (x[55:28] == 28'b0) begin count = count + 6'd28; x = x << 28; end
            if (x[55:42] == 14'b0) begin count = count + 6'd14; x = x << 14; end
            if (x[55:49] == 7'b0)  begin count = count + 6'd7;  x = x << 7;  end
            if (x[55:52] == 4'b0)  begin count = count + 6'd4;  x = x << 4;  end
            if (x[55:54] == 2'b0)  begin count = count + 6'd2;  x = x << 2;  end
            if (!x[55])            begin count = count + 6'd1;  x = x << 1;  end
            return count;
        end
    endfunction

    // Logarithmic shift-right with sticky-bit collection for significand
    // alignment.
    function automatic logic [55:0] shift_right_jam56(
        input logic [55:0] value,
        input logic [12:0] amount
    );
        logic [55:0] x;
        logic sticky;
        begin
            x = value;
            sticky = 1'b0;
            if (amount >= 13'd56) begin
                x = '0;
                sticky = |value;
            end
            else begin
                if (amount[0]) begin sticky = sticky | x[0];       x = x >> 1;  end
                if (amount[1]) begin sticky = sticky | (|x[1:0]);  x = x >> 2;  end
                if (amount[2]) begin sticky = sticky | (|x[3:0]);  x = x >> 4;  end
                if (amount[3]) begin sticky = sticky | (|x[7:0]);  x = x >> 8;  end
                if (amount[4]) begin sticky = sticky | (|x[15:0]); x = x >> 16; end
                if (amount[5]) begin sticky = sticky | (|x[31:0]); x = x >> 32; end
            end
            x[0] = x[0] | sticky;
            return x;
        end
    endfunction

    function automatic operand_t decode_operand(
        input fpp::double_t d,
        input fpp::single_t s,
        input logic is_single
    );
        operand_t o;
        begin
            o = '0;
            if (is_single) begin
                o.sign = s.sign;
                o.zero = (s.exp == 0) & (s.mant == 0);
                o.inf = fpp::is_inf_s(s);
                o.nan = fpp::is_nan_s(s);
                o.snan = o.nan & fpp::nan_is_snan_s(s);
                if (s.exp == 0) begin
                    o.sig = {1'b0, s.mant, 29'b0};
                    o.exp = -13'sd126;
                end
                else begin
                    o.sig = {1'b1, s.mant, 29'b0};
                    o.exp = $signed({1'b0, s.exp}) - 13'sd127;
                end
            end
            else begin
                o.sign = d.sign;
                o.zero = (d.exp == 0) & (d.mant == 0);
                o.inf = fpp::is_inf_d(d);
                o.nan = fpp::is_nan_d(d);
                o.snan = o.nan & fpp::nan_is_snan_d(d);
                if (d.exp == 0) begin
                    o.sig = {1'b0, d.mant};
                    o.exp = -13'sd1022;
                end
                else begin
                    o.sig = {1'b1, d.mant};
                    o.exp = $signed({1'b0, d.exp}) - 13'sd1023;
                end
            end
            return o;
        end
    endfunction

    function automatic packet_t round_pack(
        input logic sign,
        input logic signed [12:0] exponent,
        input logic [55:0] sig_ext,
        input logic is_single,
        input logic [2:0] rm
    );
        packet_t p;
        logic [55:0] sig;
        logic [2:0] grs;
        logic lost, inexact, increment, subnormal, overflow_to_inf;
        logic [53:0] round_base, round_result;
        logic signed [12:0] exp;
        integer sh;
        begin
            p = '0;
            sig = sig_ext;
            exp = exponent;
            lost = 1'b0;
            subnormal = 1'b0;
            if (is_single ? (exp < -13'sd126) : (exp < -13'sd1022)) begin
                subnormal = 1'b1;
                sh = is_single ? (-13'sd126 - exp) : (-13'sd1022 - exp);
                if (sh >= 56) begin lost = |sig; sig = '0; end
                else begin
                    lost = |(sig & ((56'h1 << sh) - 1'b1));
                    sig = sig >> sh;
                end
                exp = is_single ? -13'sd126 : -13'sd1022;
            end

            grs = is_single
                ? {sig[31], sig[30], (|sig[29:0]) | lost}
                : {sig[2], sig[1], sig[0] | lost};
            inexact = |grs;
            case (rm)
                fpp::RM_RNE: increment = grs[2] & (grs[1] | grs[0] | (is_single ? sig[32] : sig[3]));
                fpp::RM_RTZ: increment = 1'b0;
                fpp::RM_RDN: increment = sign & inexact;
                fpp::RM_RUP: increment = ~sign & inexact;
                fpp::RM_RMM: increment = grs[2];
                default: increment = 1'b0;
            endcase

            round_base = is_single ? {30'b0, sig[55:32]} : {1'b0, sig[55:3]};
            round_result = round_base + increment;
            overflow_to_inf = (rm == fpp::RM_RNE) || (rm == fpp::RM_RMM) ||
                ((rm == fpp::RM_RUP) && !sign) || ((rm == fpp::RM_RDN) && sign);

            if (is_single) begin
                if (!subnormal && ((exp > 127) || ((exp == 127) &&
                    (round_result[24] || ((&sig[55:32]) && inexact))))) begin
                    if (overflow_to_inf)
                        p.result = {1'b1, 11'h7ff, 20'hfffff, sign, 8'hff, 23'h0};
                    else p.result = {1'b1, 11'h7ff, 20'hfffff, sign, 8'hfe, 23'h7fffff};
                    p.except.OF = 1'b1; p.except.NX = 1'b1;
                end
                else if (subnormal && round_result[23]) begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, sign, 8'h01, 23'h0};
                    p.except.NX = inexact;
                end
                else if (subnormal) begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, sign, 8'h00, round_result[22:0]};
                    p.except.NX = inexact; p.except.UF = inexact;
                end
                else if (round_result[24]) begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, sign, 8'(exp + 128), 23'h0};
                    p.except.NX = inexact;
                end
                else begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, sign, 8'(exp + 127), round_result[22:0]};
                    p.except.NX = inexact;
                end
            end
            else begin
                if (!subnormal && ((exp > 1023) || ((exp == 1023) &&
                    (round_result[53] || ((&sig[55:3]) && inexact))))) begin
                    if (overflow_to_inf) p.result = {sign, 11'h7ff, 52'h0};
                    else p.result = {sign, 11'h7fe, 52'hf_ffff_ffff_ffff};
                    p.except.OF = 1'b1; p.except.NX = 1'b1;
                end
                else if (subnormal && round_result[52]) begin
                    p.result = {sign, 11'h001, 52'h0}; p.except.NX = inexact;
                end
                else if (subnormal) begin
                    p.result = {sign, 11'h000, round_result[51:0]};
                    p.except.NX = inexact; p.except.UF = inexact;
                end
                else if (round_result[53]) begin
                    p.result = {sign, 11'(exp + 1024), 52'h0}; p.except.NX = inexact;
                end
                else begin
                    p.result = {sign, 11'(exp + 1023), round_result[51:0]}; p.except.NX = inexact;
                end
            end
            return p;
        end
    endfunction

    // Split the iterative DIV/SQRT completion packer across two cycles.  The
    // subnormal alignment, rounding decision, and final exponent/result mux
    // otherwise form a particularly long path from slow_exp to slow_packet.
    function automatic round_pre_t round_prepare(
        input logic sign,
        input logic signed [12:0] exponent,
        input logic [55:0] sig_ext,
        input logic is_single,
        input logic [2:0] rm
    );
        round_pre_t q;
        logic [2:0] grs;
        logic lost;
        integer sh;
        begin
            q = '0;
            q.sign = sign;
            q.sig = sig_ext;
            q.exp = exponent;
            q.single = is_single;
            q.subnormal = 1'b0;
            lost = 1'b0;
            if (is_single ? (q.exp < -13'sd126) : (q.exp < -13'sd1022)) begin
                q.subnormal = 1'b1;
                sh = is_single ? (-13'sd126 - q.exp) : (-13'sd1022 - q.exp);
                if (sh >= 56) begin lost = |q.sig; q.sig = '0; end
                else begin
                    lost = |(q.sig & ((56'h1 << sh) - 1'b1));
                    q.sig = q.sig >> sh;
                end
                q.exp = is_single ? -13'sd126 : -13'sd1022;
            end

            grs = is_single
                ? {q.sig[31], q.sig[30], (|q.sig[29:0]) | lost}
                : {q.sig[2], q.sig[1], q.sig[0] | lost};
            q.inexact = |grs;
            case (rm)
                fpp::RM_RNE: q.increment = grs[2] & (grs[1] | grs[0] | (is_single ? q.sig[32] : q.sig[3]));
                fpp::RM_RTZ: q.increment = 1'b0;
                fpp::RM_RDN: q.increment = sign & q.inexact;
                fpp::RM_RUP: q.increment = ~sign & q.inexact;
                fpp::RM_RMM: q.increment = grs[2];
                default: q.increment = 1'b0;
            endcase
            q.overflow_to_inf = (rm == fpp::RM_RNE) || (rm == fpp::RM_RMM) ||
                ((rm == fpp::RM_RUP) && !sign) || ((rm == fpp::RM_RDN) && sign);
            return q;
        end
    endfunction

    function automatic packet_t round_finish(input round_pre_t q);
        packet_t p;
        logic [53:0] round_base, round_result;
        begin
            p = '0;
            round_base = q.single ? {30'b0, q.sig[55:32]} : {1'b0, q.sig[55:3]};
            round_result = round_base + q.increment;
            if (q.single) begin
                if (!q.subnormal && ((q.exp > 127) || ((q.exp == 127) &&
                    (round_result[24] || ((&q.sig[55:32]) && q.inexact))))) begin
                    if (q.overflow_to_inf)
                        p.result = {1'b1, 11'h7ff, 20'hfffff, q.sign, 8'hff, 23'h0};
                    else p.result = {1'b1, 11'h7ff, 20'hfffff, q.sign, 8'hfe, 23'h7fffff};
                    p.except.OF = 1'b1; p.except.NX = 1'b1;
                end
                else if (q.subnormal && round_result[23]) begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, q.sign, 8'h01, 23'h0};
                    p.except.NX = q.inexact;
                end
                else if (q.subnormal) begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, q.sign, 8'h00, round_result[22:0]};
                    p.except.NX = q.inexact; p.except.UF = q.inexact;
                end
                else if (round_result[24]) begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, q.sign, 8'(q.exp + 128), 23'h0};
                    p.except.NX = q.inexact;
                end
                else begin
                    p.result = {1'b1, 11'h7ff, 20'hfffff, q.sign, 8'(q.exp + 127), round_result[22:0]};
                    p.except.NX = q.inexact;
                end
            end
            else begin
                if (!q.subnormal && ((q.exp > 1023) || ((q.exp == 1023) &&
                    (round_result[53] || ((&q.sig[55:3]) && q.inexact))))) begin
                    if (q.overflow_to_inf) p.result = {q.sign, 11'h7ff, 52'h0};
                    else p.result = {q.sign, 11'h7fe, 52'hf_ffff_ffff_ffff};
                    p.except.OF = 1'b1; p.except.NX = 1'b1;
                end
                else if (q.subnormal && round_result[52]) begin
                    p.result = {q.sign, 11'h001, 52'h0}; p.except.NX = q.inexact;
                end
                else if (q.subnormal) begin
                    p.result = {q.sign, 11'h000, round_result[51:0]};
                    p.except.NX = q.inexact; p.except.UF = q.inexact;
                end
                else if (round_result[53]) begin
                    p.result = {q.sign, 11'(q.exp + 1024), 52'h0}; p.except.NX = q.inexact;
                end
                else begin
                    p.result = {q.sign, 11'(q.exp + 1023), round_result[51:0]}; p.except.NX = q.inexact;
                end
            end
            return p;
        end
    endfunction

    function automatic packet_t boxed(input fpp::single_t s, input fpp::fpu_except_t e);
        packet_t p;
        begin p.result = {1'b1, 11'h7ff, 20'hfffff, s}; p.except = e; return p; end
    endfunction

    // Decode and shared operand preparation.
    always_comb begin
        in_op = decode_op(in_funct7[6:2]);
        if ((in_op == OP_SQRT) && (in_funct5 != 5'b00000)) in_op = OP_BAD;
        in_single = ~in_funct7[0];
        in_rm = (in_instr_rm == fpp::RM_DYN) ? in_fcsr_rm : in_instr_rm;
        in_slow = (in_op == OP_DIV) | (in_op == OP_SQRT);
        in_A_decoded = decode_operand(in_A_d, in_A_s_boxed, in_single);
        in_B_decoded = decode_operand(in_B_d, in_B_s_boxed, in_single);
        p0_A_norm_count = '0;
        p0_B_norm_count = '0;
        if (!p0_A_decoded.nan && !p0_A_decoded.inf && !p0_A_decoded.zero)
            p0_A_norm_count = leading_zeros_53(p0_A_decoded.sig);
        if (!p0_B_decoded.nan && !p0_B_decoded.inf && !p0_B_decoded.zero)
            p0_B_norm_count = leading_zeros_53(p0_B_decoded.sig);
        f0_A_norm = f0_A_decoded;
        f0_B_norm = f0_B_decoded;
        if (f0_A_norm_count != 0) begin
            f0_A_norm.sig = f0_A_decoded.sig << f0_A_norm_count;
            f0_A_norm.exp = f0_A_decoded.exp - $signed({7'b0,f0_A_norm_count});
        end
        if (f0_B_norm_count != 0) begin
            f0_B_norm.sig = f0_B_decoded.sig << f0_B_norm_count;
            f0_B_norm.exp = f0_B_decoded.exp - $signed({7'b0,f0_B_norm_count});
        end
        if (in_op == OP_DIV)
            in_slow_special = in_A_decoded.nan | in_B_decoded.nan |
                in_A_decoded.zero | in_B_decoded.zero | in_A_decoded.inf | in_B_decoded.inf;
        else
            in_slow_special = in_A_decoded.nan | in_A_decoded.inf | in_A_decoded.zero |
                (in_A_decoded.sign & ~in_A_decoded.zero);
    end

    // Default assignments and finite FADD/FSUB/FMUL datapath.
    always_comb begin
        fast_packet = '0;
        calc_exp = s1_A_norm.exp;
        calc_sig = '0;
        calc_sign = s1_A_norm.sign;
        calc_zero = 1'b0;
        add_A_ext = {s1_A_norm.sig, 3'b0};
        add_B_ext = {s1_B_norm.sig, 3'b0};
        add_ext = '0;
        add_sum = '0;
        align_shift = '0;
        add_sign_b = s1_B_norm.sign ^ (s1_op == OP_SUB);
        shifted_value = '0;
        mul_p00 = '0; mul_p01 = '0; mul_p02 = '0;
        mul_p10 = '0; mul_p11 = '0; mul_p12 = '0;
        mul_p20 = '0; mul_p21 = '0; mul_p22 = '0;
        fast_round_needed = 1'b0;
        round_sig = '0;
        round_grs = '0;
        round_s = '0;
        round_d = '0;
        round_lost = 1'b0;
        round_inexact = 1'b0;
        round_inc = 1'b0;
        round_subnormal = 1'b0;
        round_exp = '0;
        fast_add_work = 1'b0;
        fast_mul_work = 1'b0;
        fast_add_sign_a = s1_A_norm.sign;
        fast_add_sign_b = add_sign_b;

        if (s1_op == OP_ADD || s1_op == OP_SUB || s1_op == OP_MUL) begin
            if (s1_A_norm.nan || s1_B_norm.nan) begin
                if (s1_single) fast_packet = boxed(fpp::CNAN_S, '{NV:(s1_A_norm.snan|s1_B_norm.snan), DZ:1'b0, OF:1'b0, UF:1'b0, NX:1'b0});
                else begin fast_packet.result = fpp::CNAN_D; fast_packet.except.NV = s1_A_norm.snan | s1_B_norm.snan; end
            end
            else if (s1_op == OP_MUL && ((s1_A_norm.inf && s1_B_norm.zero) || (s1_B_norm.inf && s1_A_norm.zero))) begin
                if (s1_single) fast_packet = boxed(fpp::CNAN_S, '{NV:1'b1, DZ:1'b0, OF:1'b0, UF:1'b0, NX:1'b0});
                else begin fast_packet.result = fpp::CNAN_D; fast_packet.except.NV = 1'b1; end
            end
            else if ((s1_op != OP_MUL) && s1_A_norm.inf && s1_B_norm.inf && (s1_A_norm.sign != add_sign_b)) begin
                if (s1_single) fast_packet = boxed(fpp::CNAN_S, '{NV:1'b1, DZ:1'b0, OF:1'b0, UF:1'b0, NX:1'b0});
                else begin fast_packet.result = fpp::CNAN_D; fast_packet.except.NV = 1'b1; end
            end
            else if (s1_A_norm.inf || s1_B_norm.inf) begin
                fast_packet.result = s1_single
                    ? {1'b1, 11'h7ff, 20'hfffff, (s1_op == OP_MUL) ? (s1_A_norm.sign ^ s1_B_norm.sign) : (s1_A_norm.inf ? s1_A_norm.sign : add_sign_b), 8'hff, 23'h0}
                    : {(s1_op == OP_MUL) ? (s1_A_norm.sign ^ s1_B_norm.sign) : (s1_A_norm.inf ? s1_A_norm.sign : add_sign_b), 11'h7ff, 52'h0};
            end
            else if (s1_A_norm.zero && (s1_op != OP_MUL ? s1_B_norm.zero : 1'b0)) begin
                calc_sign = (s1_A_norm.sign == add_sign_b) ? s1_A_norm.sign : (s1_rm == fpp::RM_RDN);
                fast_packet.result = s1_single ? {1'b1, 11'h7ff, 20'hfffff, calc_sign, 31'h0} : {calc_sign, 63'h0};
            end
            else if (s1_op == OP_MUL && (s1_A_norm.zero || s1_B_norm.zero)) begin
                calc_sign = s1_A_norm.sign ^ s1_B_norm.sign;
                fast_packet.result = s1_single ? {1'b1, 11'h7ff, 20'hfffff, calc_sign, 31'h0} : {calc_sign, 63'h0};
            end
            else if (s1_op == OP_MUL) begin
                mul_p00 = s1_A_norm.sig[17:0] * s1_B_norm.sig[17:0];
                mul_p01 = s1_A_norm.sig[17:0] * s1_B_norm.sig[35:18];
                mul_p02 = s1_A_norm.sig[17:0] * s1_B_norm.sig[52:36];
                mul_p10 = s1_A_norm.sig[35:18] * s1_B_norm.sig[17:0];
                mul_p11 = s1_A_norm.sig[35:18] * s1_B_norm.sig[35:18];
                mul_p12 = s1_A_norm.sig[35:18] * s1_B_norm.sig[52:36];
                mul_p20 = s1_A_norm.sig[52:36] * s1_B_norm.sig[17:0];
                mul_p21 = s1_A_norm.sig[52:36] * s1_B_norm.sig[35:18];
                mul_p22 = s1_A_norm.sig[52:36] * s1_B_norm.sig[52:36];
                calc_exp = s1_A_norm.exp + s1_B_norm.exp;
                calc_sign = s1_A_norm.sign ^ s1_B_norm.sign;
                fast_mul_work = 1'b1;
                fast_round_needed = 1'b1;
            end
            else begin
                if (s1_A_norm.exp >= s1_B_norm.exp) begin
                    calc_exp = s1_A_norm.exp; align_shift = s1_A_norm.exp - s1_B_norm.exp;
                    fast_add_sign_a = s1_A_norm.sign;
                    fast_add_sign_b = add_sign_b;
                end
                else begin
                    calc_exp = s1_B_norm.exp; align_shift = s1_B_norm.exp - s1_A_norm.exp;
                    add_A_ext = {s1_B_norm.sig, 3'b0}; add_B_ext = {s1_A_norm.sig, 3'b0};
                    calc_sign = add_sign_b;
                    add_sign_b = s1_A_norm.sign;
                    fast_add_sign_a = calc_sign;
                    fast_add_sign_b = add_sign_b;
                end
                shifted_value = shift_right_jam56(add_B_ext, align_shift);
                calc_sign = fast_add_sign_a;
                fast_add_work = 1'b1;
            end
        end
        else if (s1_op == OP_BAD) begin
            if (s1_single) fast_packet = boxed(fpp::CNAN_S, '0);
            else fast_packet.result = fpp::CNAN_D;
        end
    end

    // Add/subtract after alignment, allowing the wide add/sub to occupy its
    // own pipeline stage.
    always_comb begin
        s2_mul_row0_comb = '0;
        s2_mul_row1_comb = '0;
        s2_mul_row2_comb = '0;
        if (s2_mul_work) begin
            s2_mul_row0_comb = {{36{1'b0}},s2_mul_p00}
                + {18'b0,s2_mul_p01,18'b0} + {1'b0,s2_mul_p02[34:0],36'b0};
            s2_mul_row1_comb = {{36{1'b0}},s2_mul_p10}
                + {18'b0,s2_mul_p11,18'b0} + {1'b0,s2_mul_p12[34:0],36'b0};
            s2_mul_row2_comb = {{36{1'b0}},s2_mul_p20}
                + {18'b0,s2_mul_p21,18'b0} + {2'b0,s2_mul_p22[33:0],36'b0};
        end
        s2_add_sum = '0;
        s2_result_sig = s2_sig;
        s2_result_exp = s2_exp;
        s2_result_sign = s2_sign;
        s2_result_round_needed = s2_round_needed;
        s2_result_packet = s2_special_packet;

        if (s2_add_work) begin
            if (s2_add_sign_a == s2_add_sign_b) begin
                s2_add_sum = {1'b0, s2_add_a} + {1'b0, s2_add_b};
                if (s2_add_sum[56]) begin
                    s2_result_sig = s2_add_sum[56:1];
                    s2_result_sig[0] = s2_result_sig[0] | s2_add_sum[0];
                    s2_result_exp = s2_exp + 1'b1;
                end
                else s2_result_sig = s2_add_sum[55:0];
            end
            else if (s2_add_a >= s2_add_b) begin
                s2_result_sig = s2_add_a - s2_add_b;
                s2_result_sign = s2_add_sign_a;
            end
            else begin
                s2_result_sig = s2_add_b - s2_add_a;
                s2_result_sign = s2_add_sign_b;
            end

            if (s2_result_sig == 0) begin
                s2_result_round_needed = 1'b0;
                s2_result_packet = '0;
                s2_result_sign = (s2_rm == fpp::RM_RDN);
                if (s2_single)
                    s2_result_packet = boxed({s2_result_sign, 8'h00, 23'h0}, '0);
                else s2_result_packet.result = {s2_result_sign, 63'h0};
            end
            else s2_result_round_needed = 1'b1;
        end
    end

    // Normalize in a separate stage, before the rounding/packing stage.
    always_comb begin
        s4_mul_product = {{34{1'b0}}, s3_mul_row0}
            + {{16{1'b0}}, s3_mul_row1, 18'b0}
            + {s3_mul_row2[69:0], 36'b0};
        normalize_count = '0;
        if (s3_normalize && (s3_sig != 0)) begin
            normalize_count = leading_zeros_56(s3_sig);
        end

        s5_norm_sig = s4_sig;
        s5_norm_exp = s4_exp;
        if (s4_normalize && (s4_sig != 0)) begin
            s5_norm_sig = s4_sig << s4_norm_count;
            s5_norm_exp = s4_exp - s4_norm_count;
        end
    end

    // Iterative state-machine combinational next-step calculations.
    always_comb begin
        sqrt_trial_comb = {slow_root, 2'b01};
        sqrt_remainder_next = (slow_sqrt_remainder << 2) | slow_radicand[111:110];
        sqrt_root_next = {slow_root[54:0], 1'b0};
        if (sqrt_remainder_next >= sqrt_trial_comb) begin
            sqrt_remainder_next = sqrt_remainder_next - sqrt_trial_comb;
            sqrt_root_next[0] = 1'b1;
        end
    end

    always_comb begin
        div_remainder_next = {slow_remainder[52:0], 1'b0};
        div_quotient_next = slow_quotient;
        if (slow_count <= 54) begin
            if (div_remainder_next >= {1'b0, slow_divisor}) begin
                div_remainder_next = div_remainder_next - {1'b0, slow_divisor};
                div_quotient_next[54-slow_count] = 1'b1;
            end
            else div_quotient_next[54-slow_count] = 1'b0;
        end

        out_slot_ready = ~out_valid | out_ready;
        s7_ready = ~s7_valid | (out_slot_ready & ~slow_pending);
        s6_ready = ~s6_valid | s7_ready;
        s5_ready = ~s5_valid | s6_ready;
        s4_ready = ~s4_valid | s5_ready;
        s3_ready = ~s3_valid | s4_ready;
        s2_ready = ~s2_valid | s3_ready;
        s1_ready = ~s1_valid | s2_ready;
        f0_ready = ~f0_valid | s1_ready;
        p0_ready = ~p0_valid | f0_ready;
        in_ready = in_slow
            ? ((slow_state == SLOW_IDLE) & ~slow_pending)
            : p0_ready;
        div_rem_initial = '0;
        div_exp_initial = slow_A_norm.exp - slow_B_norm.exp;
        slow_A_norm_count_comb = '0;
        slow_B_norm_count_comb = '0;
        if (slow_A_norm.sig != 0)
            slow_A_norm_count_comb = leading_zeros_53(slow_A_norm.sig);
        if (slow_B_norm.sig != 0)
            slow_B_norm_count_comb = leading_zeros_53(slow_B_norm.sig);
        if (slow_A_norm.sig < slow_B_norm.sig) begin
            div_rem_initial = {slow_A_norm.sig,1'b0} - {1'b0,slow_B_norm.sig};
            div_exp_initial = div_exp_initial - 1'b1;
        end
        else div_rem_initial = {1'b0,slow_A_norm.sig} - {1'b0,slow_B_norm.sig};
        sqrt_rad_initial = {slow_A_norm.sig,58'b0};
        sqrt_exp_initial = slow_A_norm.exp;
        if (slow_A_norm.exp[0]) begin sqrt_rad_initial = {slow_A_norm.sig,59'b0}; sqrt_exp_initial = slow_A_norm.exp - 1'b1; end
    end

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            p0_valid <= 1'b0; p0_op <= OP_BAD; p0_single <= 1'b0; p0_rm <= '0;
            p0_A_decoded <= '0; p0_B_decoded <= '0;
            p0_dest_pr <= '0; p0_rob_idx <= '0;
            f0_valid <= 1'b0; f0_op <= OP_BAD; f0_single <= 1'b0; f0_rm <= '0;
            f0_A_decoded <= '0; f0_B_decoded <= '0;
            f0_A_norm_count <= '0; f0_B_norm_count <= '0;
            f0_dest_pr <= '0; f0_rob_idx <= '0;
            s1_valid <= 1'b0; s2_valid <= 1'b0; s3_valid <= 1'b0;
            s4_valid <= 1'b0; s5_valid <= 1'b0; s6_valid <= 1'b0; s7_valid <= 1'b0;
            s1_op <= OP_BAD; s1_single <= 1'b0; s1_rm <= '0;
            s1_A_norm <= '0; s1_B_norm <= '0;
            s1_dest_pr <= '0; s1_rob_idx <= '0;
            s2_special_packet <= '0; s2_round_needed <= 1'b0; s2_sign <= 1'b0; s2_exp <= '0;
            s2_sig <= '0; s2_single <= 1'b0; s2_rm <= '0; s2_dest_pr <= '0; s2_rob_idx <= '0;
            s2_add_work <= 1'b0; s2_add_a <= '0; s2_add_b <= '0;
            s2_mul_work <= 1'b0;
            s2_mul_p00 <= '0; s2_mul_p01 <= '0; s2_mul_p02 <= '0;
            s2_mul_p10 <= '0; s2_mul_p11 <= '0; s2_mul_p12 <= '0;
            s2_mul_p20 <= '0; s2_mul_p21 <= '0; s2_mul_p22 <= '0;
            s2_add_sign_a <= 1'b0; s2_add_sign_b <= 1'b0;
            s3_special_packet <= '0; s3_round_needed <= 1'b0; s3_normalize <= 1'b0;
            s3_mul_work <= 1'b0;
            s3_mul_row0 <= '0; s3_mul_row1 <= '0; s3_mul_row2 <= '0;
            s3_sign <= 1'b0; s3_exp <= '0; s3_sig <= '0; s3_single <= 1'b0; s3_rm <= '0;
            s3_dest_pr <= '0; s3_rob_idx <= '0;
            s4_special_packet <= '0; s4_round_needed <= 1'b0; s4_normalize <= 1'b0; s4_norm_count <= '0;
            s4_sign <= 1'b0; s4_exp <= '0; s4_sig <= '0; s4_single <= 1'b0; s4_rm <= '0;
            s4_dest_pr <= '0; s4_rob_idx <= '0;
            s5_special_packet <= '0; s5_round_needed <= 1'b0;
            s5_sign <= 1'b0; s5_exp <= '0; s5_sig <= '0; s5_single <= 1'b0; s5_rm <= '0;
            s5_dest_pr <= '0; s5_rob_idx <= '0;
            s6_special_packet <= '0; s6_round_pre <= '0; s6_round_needed <= 1'b0; s6_dest_pr <= '0; s6_rob_idx <= '0;
            s7_packet <= '0; s7_dest_pr <= '0; s7_rob_idx <= '0;
            out_valid <= 1'b0; out_dest_pr <= '0; out_rob_idx <= '0; out_result_d <= '0; out_except <= '0;
            slow_state <= SLOW_IDLE; slow_pending <= 1'b0; slow_packet <= '0; slow_op <= OP_BAD;
            slow_pack_sig <= '0; slow_round_pre <= '0;
            slow_A_norm <= '0; slow_B_norm <= '0;
            slow_A_norm_count <= '0; slow_B_norm_count <= '0;
            slow_dest_pr <= '0; slow_rob_idx <= '0; slow_single <= 1'b0; slow_sign <= 1'b0;
            slow_rm <= '0; slow_exp <= '0; slow_divisor <= '0; slow_remainder <= '0;
            slow_quotient <= '0; slow_root <= '0; slow_radicand <= '0;
            slow_sqrt_remainder <= '0; slow_count <= '0;
        end
        else begin
            if (f0_ready) begin
                f0_valid <= p0_valid;
                if (p0_valid) begin
                    f0_op <= p0_op; f0_single <= p0_single; f0_rm <= p0_rm;
                    f0_A_decoded <= p0_A_decoded; f0_B_decoded <= p0_B_decoded;
                    f0_A_norm_count <= p0_A_norm_count; f0_B_norm_count <= p0_B_norm_count;
                    f0_dest_pr <= p0_dest_pr; f0_rob_idx <= p0_rob_idx;
                end
            end
            if (p0_ready) begin
                p0_valid <= in_valid & in_ready & ~in_slow;
                if (in_valid && in_ready && !in_slow) begin
                    p0_op <= in_op; p0_single <= in_single; p0_rm <= in_rm;
                    p0_A_decoded <= in_A_decoded; p0_B_decoded <= in_B_decoded;
                    p0_dest_pr <= in_dest_pr; p0_rob_idx <= in_rob_idx;
                end
            end
            if (s1_ready) begin
                s1_valid <= f0_valid;
                if (f0_valid) begin
                    s1_op <= f0_op; s1_single <= f0_single; s1_rm <= f0_rm;
                    s1_A_norm <= f0_A_norm; s1_B_norm <= f0_B_norm;
                    s1_dest_pr <= f0_dest_pr; s1_rob_idx <= f0_rob_idx;
                end
            end
            if (s2_ready) begin
                s2_valid <= s1_valid;
                if (s1_valid) begin
                    s2_special_packet <= fast_packet; s2_round_needed <= fast_round_needed;
                    s2_sign <= calc_sign; s2_exp <= calc_exp; s2_sig <= calc_sig;
                    s2_add_work <= fast_add_work; s2_add_a <= add_A_ext; s2_add_b <= shifted_value;
                    s2_mul_work <= fast_mul_work;
                    s2_mul_p00 <= mul_p00; s2_mul_p01 <= mul_p01; s2_mul_p02 <= mul_p02;
                    s2_mul_p10 <= mul_p10; s2_mul_p11 <= mul_p11; s2_mul_p12 <= mul_p12;
                    s2_mul_p20 <= mul_p20; s2_mul_p21 <= mul_p21; s2_mul_p22 <= mul_p22;
                    s2_add_sign_a <= fast_add_sign_a; s2_add_sign_b <= fast_add_sign_b;
                    s2_single <= s1_single; s2_rm <= s1_rm;
                    s2_dest_pr <= s1_dest_pr; s2_rob_idx <= s1_rob_idx;
                end
            end
            if (s3_ready) begin
                s3_valid <= s2_valid;
                if (s2_valid) begin
                    s3_special_packet <= s2_result_packet;
                    s3_round_needed <= s2_result_round_needed;
                    s3_normalize <= s2_add_work & s2_result_round_needed;
                    s3_mul_work <= s2_mul_work;
                    s3_mul_row0 <= s2_mul_row0_comb;
                    s3_mul_row1 <= s2_mul_row1_comb;
                    s3_mul_row2 <= s2_mul_row2_comb;
                    s3_sign <= s2_result_sign; s3_exp <= s2_result_exp; s3_sig <= s2_result_sig;
                    s3_single <= s2_single; s3_rm <= s2_rm;
                    s3_dest_pr <= s2_dest_pr; s3_rob_idx <= s2_rob_idx;
                end
            end
            if (s4_ready) begin
                s4_valid <= s3_valid;
                if (s3_valid) begin
                    s4_special_packet <= s3_special_packet;
                    s4_round_needed <= s3_mul_work ? 1'b1 : s3_round_needed;
                    s4_normalize <= s3_mul_work ? 1'b0 : s3_normalize;
                    s4_norm_count <= normalize_count;
                    s4_sign <= s3_sign;
                    if (s3_mul_work) begin
                        if (s4_mul_product[105]) begin
                            s4_sig <= s4_mul_product[105:50];
                            s4_sig[0] <= s4_mul_product[50] | (|s4_mul_product[49:0]);
                            s4_exp <= s3_exp + 1'b1;
                        end
                        else begin
                            s4_sig <= s4_mul_product[104:49];
                            s4_sig[0] <= s4_mul_product[49] | (|s4_mul_product[48:0]);
                            s4_exp <= s3_exp;
                        end
                    end
                    else begin
                        s4_exp <= s3_exp; s4_sig <= s3_sig;
                    end
                    s4_single <= s3_single; s4_rm <= s3_rm;
                    s4_dest_pr <= s3_dest_pr; s4_rob_idx <= s3_rob_idx;
                end
            end
            if (s5_ready) begin
                s5_valid <= s4_valid;
                if (s4_valid) begin
                    s5_special_packet <= s4_special_packet; s5_round_needed <= s4_round_needed;
                    s5_sign <= s4_sign; s5_exp <= s5_norm_exp; s5_sig <= s5_norm_sig;
                    s5_single <= s4_single; s5_rm <= s4_rm;
                    s5_dest_pr <= s4_dest_pr; s5_rob_idx <= s4_rob_idx;
                end
            end
            if (s6_ready) begin
                s6_valid <= s5_valid;
                if (s5_valid) begin
                    s6_special_packet <= s5_special_packet;
                    s6_round_needed <= s5_round_needed;
                    s6_round_pre <= s5_round_needed
                        ? round_prepare(s5_sign, s5_exp, s5_sig, s5_single, s5_rm)
                        : '0;
                    s6_dest_pr <= s5_dest_pr; s6_rob_idx <= s5_rob_idx;
                end
            end
            if (s7_ready) begin
                s7_valid <= s6_valid;
                if (s6_valid) begin
                    s7_packet <= s6_round_needed
                        ? round_finish(s6_round_pre) : s6_special_packet;
                    s7_dest_pr <= s6_dest_pr; s7_rob_idx <= s6_rob_idx;
                end
            end
            if (out_slot_ready) begin
                if (slow_pending) begin
                    out_valid <= 1'b1; out_result_d <= slow_packet.result; out_except <= slow_packet.except;
                    out_dest_pr <= slow_dest_pr; out_rob_idx <= slow_rob_idx; slow_pending <= 1'b0;
                end
                else if (s7_valid) begin
                    out_valid <= 1'b1; out_result_d <= s7_packet.result; out_except <= s7_packet.except;
                    out_dest_pr <= s7_dest_pr; out_rob_idx <= s7_rob_idx;
                end
                else out_valid <= 1'b0;
            end

            if (in_valid && in_ready && in_slow) begin
                slow_state <= in_slow_special ? SLOW_START : SLOW_NORM_COUNT;
                slow_op <= in_op;
                slow_A_norm <= in_A_decoded; slow_B_norm <= in_B_decoded;
                slow_single <= in_single; slow_rm <= in_rm;
                slow_sign <= in_A_decoded.sign ^ in_B_decoded.sign;
                slow_dest_pr <= in_dest_pr; slow_rob_idx <= in_rob_idx;
            end
            else if (slow_state == SLOW_NORM_COUNT) begin
                slow_A_norm_count <= slow_A_norm_count_comb;
                slow_B_norm_count <= slow_B_norm_count_comb;
                slow_state <= SLOW_NORM_SHIFT;
            end
            else if (slow_state == SLOW_NORM_SHIFT) begin
                if (slow_A_norm_count != 0) begin
                    slow_A_norm.sig <= slow_A_norm.sig << slow_A_norm_count;
                    slow_A_norm.exp <= slow_A_norm.exp - $signed({1'b0, slow_A_norm_count});
                end
                if (slow_B_norm_count != 0) begin
                    slow_B_norm.sig <= slow_B_norm.sig << slow_B_norm_count;
                    slow_B_norm.exp <= slow_B_norm.exp - $signed({1'b0, slow_B_norm_count});
                end
                slow_state <= SLOW_START;
            end
            else if (slow_state == SLOW_START) begin
                if (slow_op == OP_DIV) begin
                    if (slow_A_norm.nan || slow_B_norm.nan || (slow_A_norm.zero && slow_B_norm.zero) || (slow_A_norm.inf && slow_B_norm.inf)) begin
                        if (slow_single) begin
                            slow_packet.result.sign <= 1'b1;
                            slow_packet.result.exp <= 11'h7ff;
                            slow_packet.result.mant.upper <= 20'hfffff;
                            slow_packet.result.mant.single <= fpp::CNAN_S;
                        end
                        else slow_packet.result <= fpp::CNAN_D;
                        slow_packet.except <= { (slow_A_norm.snan | slow_B_norm.snan | (slow_A_norm.zero && slow_B_norm.zero) | (slow_A_norm.inf && slow_B_norm.inf)), 4'b0 };
                        slow_state <= SLOW_IDLE; slow_pending <= 1'b1;
                    end
                    else if (slow_A_norm.inf || slow_B_norm.zero) begin
                        slow_packet.result <= slow_single
                            ? {1'b1,11'h7ff,20'hfffff,slow_A_norm.sign ^ slow_B_norm.sign,8'hff,23'h0}
                            : {slow_A_norm.sign ^ slow_B_norm.sign,11'h7ff,52'h0};
                        slow_packet.except <= {1'b0, (slow_B_norm.zero & ~slow_A_norm.inf), 3'b0};
                        slow_state <= SLOW_IDLE; slow_pending <= 1'b1;
                    end
                    else if (slow_B_norm.inf || slow_A_norm.zero) begin
                        slow_packet.result <= slow_single
                            ? {1'b1,11'h7ff,20'hfffff,slow_A_norm.sign ^ slow_B_norm.sign,31'h0}
                            : {slow_A_norm.sign ^ slow_B_norm.sign,63'h0};
                        slow_packet.except <= '0;
                        slow_state <= SLOW_IDLE; slow_pending <= 1'b1;
                    end
                    else begin
                        slow_state <= SLOW_DIV; slow_exp <= div_exp_initial; slow_divisor <= slow_B_norm.sig;
                        slow_remainder <= div_rem_initial; slow_quotient <= {1'b1,55'b0}; slow_count <= 0;
                    end
                end
                else begin
                    if (slow_A_norm.nan) begin
                        if (slow_single) begin
                            slow_packet.result.sign <= 1'b1;
                            slow_packet.result.exp <= 11'h7ff;
                            slow_packet.result.mant.upper <= 20'hfffff;
                            slow_packet.result.mant.single <= fpp::CNAN_S;
                        end
                        else slow_packet.result <= fpp::CNAN_D;
                        slow_packet.except <= {slow_A_norm.snan, 4'b0};
                        slow_state <= SLOW_IDLE; slow_pending <= 1'b1;
                    end
                    else if (slow_A_norm.sign && !slow_A_norm.zero) begin
                        if (slow_single) begin
                            slow_packet.result.sign <= 1'b1;
                            slow_packet.result.exp <= 11'h7ff;
                            slow_packet.result.mant.upper <= 20'hfffff;
                            slow_packet.result.mant.single <= fpp::CNAN_S;
                        end
                        else slow_packet.result <= fpp::CNAN_D;
                        slow_packet.except <= {1'b1, 4'b0};
                        slow_state <= SLOW_IDLE; slow_pending <= 1'b1;
                    end
                    else if (slow_A_norm.inf || slow_A_norm.zero) begin
                        slow_packet.result <= slow_A_norm.inf
                            ? (slow_single ? {1'b1,11'h7ff,20'hfffff,1'b0,8'hff,23'h0} : {1'b0,11'h7ff,52'h0})
                            : (slow_single ? {1'b1,11'h7ff,20'hfffff,slow_A_norm.sign,31'h0} : {slow_A_norm.sign,63'h0});
                        slow_packet.except <= '0;
                        slow_state <= SLOW_IDLE; slow_pending <= 1'b1;
                    end
                    else begin
                        slow_state <= SLOW_SQRT; slow_exp <= sqrt_exp_initial >>> 1;
                        slow_radicand <= sqrt_rad_initial; slow_sqrt_remainder <= '0; slow_root <= '0; slow_count <= 0;
                    end
                end
            end
            else if (slow_state == SLOW_DIV) begin
                slow_remainder <= div_remainder_next;
                slow_quotient <= div_quotient_next;
                if (slow_count == 54) begin
                    slow_pack_sig <= {div_quotient_next[55:1], (div_quotient_next[0] | (|div_remainder_next))};
                    slow_state <= SLOW_PACK_PREP;
                end
                else slow_count <= slow_count + 1'b1;
            end
            else if (slow_state == SLOW_SQRT) begin
                slow_sqrt_remainder <= sqrt_remainder_next; slow_root <= sqrt_root_next;
                slow_radicand <= {slow_radicand[109:0],2'b0};
                if (slow_count == 55) begin
                    slow_pack_sig <= {sqrt_root_next[55:1], (sqrt_root_next[0] | (|sqrt_remainder_next))};
                    slow_state <= SLOW_PACK_PREP;
                end
                else slow_count <= slow_count + 1'b1;
            end
            else if (slow_state == SLOW_PACK_PREP) begin
                slow_round_pre <= round_prepare(slow_op == OP_SQRT ? 1'b0 : slow_sign,
                    slow_exp, slow_pack_sig, slow_single, slow_rm);
                slow_state <= SLOW_PACK_FINISH;
            end
            else if (slow_state == SLOW_PACK_FINISH) begin
                slow_packet <= round_finish(slow_round_pre);
                slow_state <= SLOW_IDLE;
                slow_pending <= 1'b1;
            end
        end
    end

endmodule
