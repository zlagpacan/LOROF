/*
    Filename: fpu_fuse.sv
    Author: zlagpacan
    Description: FPU Fuse-Multiply-Add Instructions
    Spec: LOROF/spec/design/fpu_fuse.md
*/

`include "fpp.vh"
`include "corep.vh"

module fpu_fuse #(

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
    input logic [6:0]       in_opcode7,
    input logic [1:0]       in_funct2,
    input logic [2:0]       in_instr_rm,
    input logic [2:0]       in_fcsr_rm,

    // fp input
    input fpp::double_t     in_A_d,
    input fpp::single_t     in_A_s_boxed, // post NaN-box check
    input fpp::double_t     in_B_d,
    input fpp::single_t     in_B_s_boxed, // post NaN-box check
    input fpp::double_t     in_C_d,
    input fpp::single_t     in_C_s_boxed, // post NaN-box check

    // output control
    output logic                out_valid,
    output corep::pr_t          out_dest_pr,
    output corep::rob_idx_t     out_rob_idx,
    input logic                 out_ready,

    // fp output
    output fpp::double_t        out_result_d,
    output fpp::fpu_except_t    out_except
);

    localparam int unsigned PIPE_STAGES = 13;

    typedef enum logic [2:0] {OP_MADD, OP_MSUB, OP_NMSUB, OP_NMADD, OP_BAD} op_t;

    typedef struct packed {
        fpp::double_t result;
        fpp::fpu_except_t except;
    } packet_t;

    typedef struct packed {
        logic sign;
        logic zero;
        logic inf;
        logic nan;
        logic snan;
        logic [52:0] sig;
        logic signed [12:0] exp;
    } operand_t;

    typedef struct packed {
        logic single;
        logic [2:0] rm;
        logic product_sign;
        logic signed [12:0] product_exp;
        operand_t C;
        logic round_needed;
        packet_t special_packet;
        corep::pr_t dest_pr;
        corep::rob_idx_t rob_idx;
    } meta_t;

    typedef struct packed {
        meta_t meta;
        operand_t A;
        operand_t B;
    } input_t;

    typedef struct packed {
        meta_t meta;
        logic [35:0] p00, p01, p02;
        logic [35:0] p10, p11, p12;
        logic [35:0] p20, p21, p22;
    } partial_t;

    typedef struct packed {
        meta_t meta;
        logic [107:0] row0, row1, row2;
    } rows_t;

    typedef struct packed {
        meta_t meta;
        logic [105:0] product;
    } product_t;

    typedef struct packed {
        meta_t meta;
        logic [105:0] product;
        logic [6:0] shift;
    } product_count_t;

    typedef struct packed {
        meta_t meta;
        logic [105:0] sig;
        logic signed [12:0] exp;
    } normalized_product_t;

    typedef struct packed {
        meta_t meta;
        logic [108:0] p_aligned, c_aligned;
        logic same_sign;
        logic signed [12:0] exp;
    } align_shift_t;

    typedef struct packed {
        meta_t meta;
        logic [108:0] x, y;
        logic add;
        logic sign;
        logic exact_zero;
        logic zero_sign;
        logic signed [12:0] exp;
    } aligned_t;

    typedef struct packed {
        meta_t meta;
        logic [109:0] sum;
        logic signed [12:0] exp;
        logic sign;
        logic exact_zero;
        logic zero_sign;
    } sum_t;

    typedef struct packed {
        meta_t meta;
        logic [109:0] sum;
        logic [6:0] shift;
        logic signed [12:0] exp;
        logic sign;
        logic exact_zero;
        logic zero_sign;
    } normalize_count_t;

    typedef struct packed {
        meta_t meta;
        logic [55:0] sig_ext;
        logic signed [12:0] exp;
        logic sign;
        logic exact_zero;
        logic zero_sign;
    } sig_t;

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
        meta_t meta;
        round_pre_t round_pre;
        logic round_needed;
        packet_t special_packet;
        logic exact_zero;
        logic zero_sign;
    } round_stage_t;

    logic [PIPE_STAGES-1:0] valid_pipe, ready_pipe;
    logic out_slot_ready;
    input_t input_txn;
    input_t txn_pipe [0:0];
    meta_t meta_pipe;
    partial_t partial_comb, partial_reg;
    rows_t rows_comb, rows_reg;
    product_t product_comb, product_reg;
    product_count_t product_count_comb, product_count_reg;
    normalized_product_t normalized_product_comb, normalized_product_reg;
    align_shift_t align_shift_comb, align_shift_reg;
    aligned_t aligned_comb, aligned_reg;
    sum_t sum_comb, sum_reg;
    normalize_count_t normalize_count_comb, normalize_count_reg;
    sig_t sig_comb, sig_reg;
    round_stage_t round_stage_comb, round_stage_reg;
    packet_t packet_comb, packet_reg;

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
                o.zero = (s.exp == 0) && (s.mant == 0);
                o.inf = fpp::is_inf_s(s);
                o.nan = fpp::is_nan_s(s);
                o.snan = o.nan && fpp::nan_is_snan_s(s);
                o.sig = {s.exp != 0, s.mant, 29'b0};
                o.exp = (s.exp == 0) ? -13'sd126 : ($signed({1'b0,s.exp}) - 13'sd127);
            end
            else begin
                o.sign = d.sign;
                o.zero = (d.exp == 0) && (d.mant == 0);
                o.inf = fpp::is_inf_d(d);
                o.nan = fpp::is_nan_d(d);
                o.snan = o.nan && fpp::nan_is_snan_d(d);
                o.sig = {d.exp != 0, d.mant};
                o.exp = (d.exp == 0) ? -13'sd1022 : ($signed({1'b0,d.exp}) - 13'sd1023);
            end
            return o;
        end
    endfunction

    function automatic op_t decode_op(input logic [1:0] fuse_op);
        case (fuse_op)
            2'b00: return OP_MADD;
            2'b01: return OP_MSUB;
            2'b10: return OP_NMSUB;
            2'b11: return OP_NMADD;
            default: return OP_BAD;
        endcase
    endfunction

    function automatic logic [35:0] mul18(
        input logic [17:0] lhs,
        input logic [17:0] rhs
    );
        logic [35:0] lhs_ext, rhs_ext;
        begin
            lhs_ext = {18'b0,lhs};
            rhs_ext = {18'b0,rhs};
            return lhs_ext * rhs_ext;
        end
    endfunction

    function automatic logic [6:0] leading_zeros_106(input logic [105:0] value);
        logic [105:0] x;
        logic [6:0] count;
        begin
            x = value;
            count = '0;
            if (x[105:42] == 64'b0) begin count = count + 7'd64; x = x << 64; end
            if (x[105:74] == 32'b0) begin count = count + 7'd32; x = x << 32; end
            if (x[105:90] == 16'b0) begin count = count + 7'd16; x = x << 16; end
            if (x[105:98] == 8'b0)  begin count = count + 7'd8;  x = x << 8;  end
            if (x[105:102] == 4'b0) begin count = count + 7'd4;  x = x << 4;  end
            if (x[105:104] == 2'b0) begin count = count + 7'd2;  x = x << 2;  end
            if (!x[105])             count = count + 7'd1;
            return count;
        end
    endfunction

    function automatic logic [6:0] leading_zeros_110(input logic [109:0] value);
        logic [109:0] x;
        logic [6:0] count;
        begin
            x = value;
            count = '0;
            if (x[109:46] == 64'b0) begin count = count + 7'd64; x = x << 64; end
            if (x[109:78] == 32'b0) begin count = count + 7'd32; x = x << 32; end
            if (x[109:94] == 16'b0) begin count = count + 7'd16; x = x << 16; end
            if (x[109:102] == 8'b0) begin count = count + 7'd8; x = x << 8; end
            if (x[109:106] == 4'b0)  begin count = count + 7'd4;  x = x << 4;  end
            if (x[109:108] == 2'b0)  begin count = count + 7'd2;  x = x << 2;  end
            if (!x[109])              count = count + 7'd1;
            return count;
        end
    endfunction

    function automatic logic [108:0] shift_right_jam109(
        input logic [108:0] value,
        input logic [12:0] amount
    );
        logic [108:0] x;
        logic sticky;
        begin
            x = value;
            sticky = 1'b0;
            if (amount >= 13'd109) begin x = '0; sticky = |value; end
            else begin
                if (amount[0]) begin sticky = sticky | x[0];       x = x >> 1;  end
                if (amount[1]) begin sticky = sticky | (|x[1:0]);  x = x >> 2;  end
                if (amount[2]) begin sticky = sticky | (|x[3:0]);  x = x >> 4;  end
                if (amount[3]) begin sticky = sticky | (|x[7:0]);  x = x >> 8;  end
                if (amount[4]) begin sticky = sticky | (|x[15:0]); x = x >> 16; end
                if (amount[5]) begin sticky = sticky | (|x[31:0]); x = x >> 32; end
                if (amount[6]) begin sticky = sticky | (|x[63:0]); x = x >> 64; end
            end
            x[0] = x[0] | sticky;
            return x;
        end
    endfunction

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
        logic [53:0] base, rounded;
        begin
            p = '0;
            base = q.single ? {30'b0,q.sig[55:32]} : {1'b0,q.sig[55:3]};
            rounded = base + q.increment;
            if (q.single) begin
                if (!q.subnormal && ((q.exp > 127) || ((q.exp == 127) &&
                    (rounded[24] || ((&q.sig[55:32]) && q.inexact))))) begin
                    if (q.overflow_to_inf) p.result = {1'b1,11'h7ff,20'hfffff,q.sign,8'hff,23'h0};
                    else p.result = {1'b1,11'h7ff,20'hfffff,q.sign,8'hfe,23'h7fffff};
                    p.except.OF = 1'b1; p.except.NX = 1'b1;
                end
                else if (q.subnormal && rounded[23]) begin
                    p.result = {1'b1,11'h7ff,20'hfffff,q.sign,8'h01,23'h0}; p.except.NX = q.inexact;
                end
                else if (q.subnormal) begin
                    p.result = {1'b1,11'h7ff,20'hfffff,q.sign,8'h00,rounded[22:0]};
                    p.except.NX = q.inexact; p.except.UF = q.inexact;
                end
                else if (rounded[24]) begin
                    p.result = {1'b1,11'h7ff,20'hfffff,q.sign,8'(q.exp+128),23'h0}; p.except.NX = q.inexact;
                end
                else begin
                    p.result = {1'b1,11'h7ff,20'hfffff,q.sign,8'(q.exp+127),rounded[22:0]}; p.except.NX = q.inexact;
                end
            end
            else begin
                if (!q.subnormal && ((q.exp > 1023) || ((q.exp == 1023) &&
                    (rounded[53] || ((&q.sig[55:3]) && q.inexact))))) begin
                    if (q.overflow_to_inf) p.result = {q.sign,11'h7ff,52'h0};
                    else p.result = {q.sign,11'h7fe,52'hf_ffff_ffff_ffff};
                    p.except.OF = 1'b1; p.except.NX = 1'b1;
                end
                else if (q.subnormal && rounded[52]) begin
                    p.result = {q.sign,11'h001,52'h0}; p.except.NX = q.inexact;
                end
                else if (q.subnormal) begin
                    p.result = {q.sign,11'h000,rounded[51:0]}; p.except.NX = q.inexact; p.except.UF = q.inexact;
                end
                else if (rounded[53]) begin
                    p.result = {q.sign,11'(q.exp+1024),52'h0}; p.except.NX = q.inexact;
                end
                else begin
                    p.result = {q.sign,11'(q.exp+1023),rounded[51:0]}; p.except.NX = q.inexact;
                end
            end
            return p;
        end
    endfunction

    always_comb begin : input_decode
        op_t op;
        logic single, negate_product, negate_c;
        operand_t A, B, C;
        logic invalid_product, invalid_inf_sum;
        input_txn = '0;
        op = decode_op(in_opcode7[3:2]);
        single = ~in_funct2[0];
        negate_product = (op == OP_NMSUB) || (op == OP_NMADD);
        negate_c = (op == OP_MSUB) || (op == OP_NMADD);
        A = decode_operand(in_A_d, in_A_s_boxed, single);
        B = decode_operand(in_B_d, in_B_s_boxed, single);
        C = decode_operand(in_C_d, in_C_s_boxed, single);
        C.sign = C.sign ^ negate_c;
        invalid_product = (A.inf && B.zero) || (B.inf && A.zero);
        invalid_inf_sum = (A.inf || B.inf) && C.inf && ((A.sign ^ B.sign ^ negate_product) != C.sign);
        input_txn.meta.single = single;
        input_txn.meta.rm = (in_instr_rm == fpp::RM_DYN) ? in_fcsr_rm : in_instr_rm;
        input_txn.meta.product_sign = A.sign ^ B.sign ^ negate_product;
        input_txn.meta.product_exp = A.exp + B.exp;
        input_txn.meta.C = C;
        input_txn.meta.dest_pr = in_dest_pr;
        input_txn.meta.rob_idx = in_rob_idx;
        if (op == OP_BAD) begin
            if (single) input_txn.meta.special_packet.result = 64'hffffffff7fc00000;
            else input_txn.meta.special_packet.result = 64'h7ff8000000000000;
        end
        else if (A.nan || B.nan || C.nan || invalid_product || invalid_inf_sum) begin
            if (single) input_txn.meta.special_packet.result = 64'hffffffff7fc00000;
            else input_txn.meta.special_packet.result = 64'h7ff8000000000000;
            input_txn.meta.special_packet.except.NV =
                A.snan || B.snan || C.snan || invalid_product || invalid_inf_sum;
        end
        else if (A.inf || B.inf) begin
            if (single)
                input_txn.meta.special_packet.result = {1'b1,11'h7ff,20'hfffff,input_txn.meta.product_sign,8'hff,23'h0};
            else input_txn.meta.special_packet.result = {input_txn.meta.product_sign,11'h7ff,52'h0};
        end
        else if (C.inf) begin
            if (single)
                input_txn.meta.special_packet.result = {1'b1,11'h7ff,20'hfffff,C.sign,8'hff,23'h0};
            else input_txn.meta.special_packet.result = {C.sign,11'h7ff,52'h0};
        end
        else begin
            input_txn.meta.round_needed = 1'b1;
            input_txn.A = A;
            input_txn.B = B;
        end
    end

    always_comb begin : pipeline_ready
        integer i;
        out_slot_ready = ~out_valid | out_ready;
        ready_pipe[PIPE_STAGES-1] = ~valid_pipe[PIPE_STAGES-1] | out_slot_ready;
        for (i = PIPE_STAGES-2; i >= 0; i = i - 1)
            ready_pipe[i] = ~valid_pipe[i] | ready_pipe[i+1];
        in_ready = ready_pipe[0];
    end

    always_comb begin : stage_math
        logic [105:0] normalized_p;
        logic signed [12:0] p_exp, exp_max;
        logic [12:0] exp_diff;
        logic [108:0] p_ext, c_ext, p_aligned, c_aligned;
        logic [108:0] x, y;
        logic same_sign, result_sign, exact_zero, zero_sign;
        logic [109:0] full_sum;
        logic [109:0] normalized_sum;
        logic signed [12:0] normalized_exp;
        packet_t zero_packet;

        partial_comb = '0;
        partial_comb.meta = txn_pipe[0].meta;
        partial_comb.p00 = mul18(txn_pipe[0].A.sig[17:0],txn_pipe[0].B.sig[17:0]);
        partial_comb.p01 = mul18(txn_pipe[0].A.sig[17:0],txn_pipe[0].B.sig[35:18]);
        partial_comb.p02 = mul18(txn_pipe[0].A.sig[17:0],{1'b0,txn_pipe[0].B.sig[52:36]});
        partial_comb.p10 = mul18(txn_pipe[0].A.sig[35:18],txn_pipe[0].B.sig[17:0]);
        partial_comb.p11 = mul18(txn_pipe[0].A.sig[35:18],txn_pipe[0].B.sig[35:18]);
        partial_comb.p12 = mul18(txn_pipe[0].A.sig[35:18],{1'b0,txn_pipe[0].B.sig[52:36]});
        partial_comb.p20 = mul18({1'b0,txn_pipe[0].A.sig[52:36]},txn_pipe[0].B.sig[17:0]);
        partial_comb.p21 = mul18({1'b0,txn_pipe[0].A.sig[52:36]},txn_pipe[0].B.sig[35:18]);
        partial_comb.p22 = mul18({1'b0,txn_pipe[0].A.sig[52:36]},{1'b0,txn_pipe[0].B.sig[52:36]});

        rows_comb = '0;
        rows_comb.meta = partial_reg.meta;
        rows_comb.row0 = {72'b0,partial_reg.p00}
            + {54'b0,partial_reg.p01,18'b0} + {36'b0,partial_reg.p02,36'b0};
        rows_comb.row1 = {54'b0,partial_reg.p10,18'b0}
            + {36'b0,partial_reg.p11,36'b0} + {18'b0,partial_reg.p12,54'b0};
        rows_comb.row2 = {36'b0,partial_reg.p20,36'b0}
            + {18'b0,partial_reg.p21,54'b0} + {partial_reg.p22,72'b0};

        product_comb = '0;
        product_comb.meta = rows_reg.meta;
        product_comb.product = rows_reg.row0 + rows_reg.row1 + rows_reg.row2;

        product_count_comb = '0;
        product_count_comb.meta = product_reg.meta;
        product_count_comb.product = product_reg.product;
        if (product_reg.product != 0)
            product_count_comb.shift = leading_zeros_106(product_reg.product);

        normalized_product_comb = '0;
        normalized_product_comb.meta = product_count_reg.meta;
        if (product_count_reg.product != 0) begin
            normalized_p = product_count_reg.product << product_count_reg.shift;
            p_exp = product_count_reg.meta.product_exp + 13'sd1
                - $signed({6'b0,product_count_reg.shift});
            normalized_product_comb.sig = normalized_p;
            normalized_product_comb.exp = p_exp;
        end
        else begin
            normalized_product_comb.sig = '0;
            normalized_product_comb.exp = product_count_reg.meta.C.exp;
        end

        align_shift_comb = '0;
        align_shift_comb.meta = normalized_product_reg.meta;
        align_shift_comb.same_sign =
            normalized_product_reg.meta.product_sign == normalized_product_reg.meta.C.sign;
        p_ext = {normalized_product_reg.sig,3'b0};
        c_ext = {{normalized_product_reg.meta.C.sig,53'b0},3'b0};
        if (normalized_product_reg.sig == 0) exp_max = normalized_product_reg.meta.C.exp;
        else if (normalized_product_reg.meta.C.zero) exp_max = normalized_product_reg.exp;
        else exp_max = (normalized_product_reg.exp >= normalized_product_reg.meta.C.exp)
            ? normalized_product_reg.exp : normalized_product_reg.meta.C.exp;
        if (normalized_product_reg.sig == 0) begin
            p_aligned = '0;
            c_aligned = c_ext;
        end
        else if (normalized_product_reg.meta.C.zero) begin
            p_aligned = p_ext;
            c_aligned = '0;
        end
        else if (normalized_product_reg.exp >= normalized_product_reg.meta.C.exp) begin
            exp_diff = normalized_product_reg.exp - normalized_product_reg.meta.C.exp;
            p_aligned = p_ext;
            c_aligned = shift_right_jam109(c_ext,exp_diff);
        end
        else begin
            exp_diff = normalized_product_reg.meta.C.exp - normalized_product_reg.exp;
            p_aligned = shift_right_jam109(p_ext,exp_diff);
            c_aligned = c_ext;
        end
        align_shift_comb.p_aligned = p_aligned;
        align_shift_comb.c_aligned = c_aligned;
        align_shift_comb.exp = exp_max;

        aligned_comb = '0;
        aligned_comb.meta = align_shift_reg.meta;
        same_sign = align_shift_reg.same_sign;
        if (same_sign || (align_shift_reg.p_aligned >= align_shift_reg.c_aligned)) begin
            x = align_shift_reg.p_aligned; y = align_shift_reg.c_aligned;
            result_sign = align_shift_reg.meta.product_sign;
        end
        else begin
            x = align_shift_reg.c_aligned; y = align_shift_reg.p_aligned;
            result_sign = align_shift_reg.meta.C.sign;
        end
        if (same_sign) result_sign = align_shift_reg.meta.product_sign;
        exact_zero = (x == y) && !same_sign;
        if ((align_shift_reg.p_aligned == 0) && (align_shift_reg.c_aligned == 0)) exact_zero = 1'b1;
        zero_sign = (align_shift_reg.meta.product_sign == align_shift_reg.meta.C.sign)
            ? align_shift_reg.meta.product_sign
            : (align_shift_reg.meta.rm == fpp::RM_RDN);
        aligned_comb.x = x;
        aligned_comb.y = y;
        aligned_comb.add = same_sign;
        aligned_comb.sign = result_sign;
        aligned_comb.exact_zero = exact_zero;
        aligned_comb.zero_sign = zero_sign;
        aligned_comb.exp = align_shift_reg.exp;

        sum_comb = '0;
        sum_comb.meta = aligned_reg.meta;
        sum_comb.exp = aligned_reg.exp;
        sum_comb.sign = aligned_reg.sign;
        sum_comb.exact_zero = aligned_reg.exact_zero;
        sum_comb.zero_sign = aligned_reg.zero_sign;
        full_sum = aligned_reg.add
            ? ({1'b0,aligned_reg.x} + {1'b0,aligned_reg.y})
            : ({1'b0,aligned_reg.x} - {1'b0,aligned_reg.y});
        sum_comb.sum = full_sum;

        normalize_count_comb = '0;
        normalize_count_comb.meta = sum_reg.meta;
        normalize_count_comb.sum = sum_reg.sum;
        normalize_count_comb.exp = sum_reg.exp;
        normalize_count_comb.sign = sum_reg.sign;
        normalize_count_comb.exact_zero = sum_reg.exact_zero || (sum_reg.sum == 0);
        normalize_count_comb.zero_sign = sum_reg.exact_zero ? sum_reg.zero_sign : sum_reg.sign;
        if ((sum_reg.sum != 0) && !sum_reg.sum[109])
            normalize_count_comb.shift = leading_zeros_110(sum_reg.sum);

        sig_comb = '0;
        sig_comb.meta = normalize_count_reg.meta;
        sig_comb.exp = normalize_count_reg.exp;
        sig_comb.sign = normalize_count_reg.sign;
        sig_comb.exact_zero = normalize_count_reg.exact_zero;
        sig_comb.zero_sign = normalize_count_reg.zero_sign;
        if (!normalize_count_reg.exact_zero) begin
            if (normalize_count_reg.sum[109]) begin
                normalized_sum = normalize_count_reg.sum;
                normalized_exp = normalize_count_reg.exp + 1'b1;
            end
            else begin
                normalized_sum = normalize_count_reg.sum << normalize_count_reg.shift;
                normalized_exp = normalize_count_reg.exp + 13'sd1
                    - $signed({6'b0,normalize_count_reg.shift});
            end
            sig_comb.sig_ext = normalized_sum[109:54];
            sig_comb.sig_ext[0] = normalized_sum[54] | (|normalized_sum[53:0]);
            sig_comb.exp = normalized_exp;
        end

        round_stage_comb = '0;
        round_stage_comb.meta = sig_reg.meta;
        round_stage_comb.round_needed = sig_reg.meta.round_needed && !sig_reg.exact_zero;
        round_stage_comb.special_packet = sig_reg.meta.special_packet;
        round_stage_comb.exact_zero = sig_reg.exact_zero;
        round_stage_comb.zero_sign = sig_reg.zero_sign;
        if (sig_reg.exact_zero && sig_reg.meta.round_needed) begin
            zero_packet = '0;
            if (sig_reg.meta.single) zero_packet.result = {1'b1,11'h7ff,20'hfffff,sig_reg.zero_sign,31'h0};
            else zero_packet.result = {sig_reg.zero_sign,63'h0};
            round_stage_comb.special_packet = zero_packet;
        end
        if (round_stage_comb.round_needed)
            round_stage_comb.round_pre = round_prepare(sig_reg.sign,sig_reg.exp,sig_reg.sig_ext,
                sig_reg.meta.single,sig_reg.meta.rm);

        packet_comb = round_stage_reg.round_needed
            ? round_finish(round_stage_reg.round_pre)
            : round_stage_reg.special_packet;
    end

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            valid_pipe <= '0;
            out_valid <= 1'b0;
            out_dest_pr <= '0;
            out_rob_idx <= '0;
            out_result_d <= '0;
            out_except <= '0;
            partial_reg <= '0;
            rows_reg <= '0;
            product_reg <= '0;
            product_count_reg <= '0;
            normalized_product_reg <= '0;
            align_shift_reg <= '0;
            aligned_reg <= '0;
            sum_reg <= '0;
            normalize_count_reg <= '0;
            sig_reg <= '0;
            round_stage_reg <= '0;
            packet_reg <= '0;
            txn_pipe[0] <= '0;
            meta_pipe <= '0;
        end
        else begin
            if (ready_pipe[0]) begin
                valid_pipe[0] <= in_valid;
                if (in_valid) txn_pipe[0] <= input_txn;
            end
            if (ready_pipe[1]) begin
                valid_pipe[1] <= valid_pipe[0];
                if (valid_pipe[0]) partial_reg <= partial_comb;
            end
            if (ready_pipe[2]) begin
                valid_pipe[2] <= valid_pipe[1];
                if (valid_pipe[1]) rows_reg <= rows_comb;
            end
            if (ready_pipe[3]) begin
                valid_pipe[3] <= valid_pipe[2];
                if (valid_pipe[2]) product_reg <= product_comb;
            end
            if (ready_pipe[4]) begin
                valid_pipe[4] <= valid_pipe[3];
                if (valid_pipe[3]) product_count_reg <= product_count_comb;
            end
            if (ready_pipe[5]) begin
                valid_pipe[5] <= valid_pipe[4];
                if (valid_pipe[4]) normalized_product_reg <= normalized_product_comb;
            end
            if (ready_pipe[6]) begin
                valid_pipe[6] <= valid_pipe[5];
                if (valid_pipe[5]) align_shift_reg <= align_shift_comb;
            end
            if (ready_pipe[7]) begin
                valid_pipe[7] <= valid_pipe[6];
                if (valid_pipe[6]) aligned_reg <= aligned_comb;
            end
            if (ready_pipe[8]) begin
                valid_pipe[8] <= valid_pipe[7];
                if (valid_pipe[7]) sum_reg <= sum_comb;
            end
            if (ready_pipe[9]) begin
                valid_pipe[9] <= valid_pipe[8];
                if (valid_pipe[8]) normalize_count_reg <= normalize_count_comb;
            end
            if (ready_pipe[10]) begin
                valid_pipe[10] <= valid_pipe[9];
                if (valid_pipe[9]) sig_reg <= sig_comb;
            end
            if (ready_pipe[11]) begin
                valid_pipe[11] <= valid_pipe[10];
                if (valid_pipe[10]) round_stage_reg <= round_stage_comb;
            end
            if (ready_pipe[12]) begin
                valid_pipe[12] <= valid_pipe[11];
                if (valid_pipe[11]) begin
                    packet_reg <= packet_comb;
                    meta_pipe <= round_stage_reg.meta;
                end
            end

            if (out_slot_ready) begin
                if (valid_pipe[12]) begin
                    out_valid <= 1'b1;
                    out_result_d <= packet_reg.result;
                    out_except <= packet_reg.except;
                    out_dest_pr <= meta_pipe.dest_pr;
                    out_rob_idx <= meta_pipe.rob_idx;
                end
                else out_valid <= 1'b0;
            end
        end
    end


endmodule
