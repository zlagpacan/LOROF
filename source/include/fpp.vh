/*
    Filename: fpp.vh
    Author: zlagpacan
    Description: Package Header File for Floating Point Types
*/

`ifndef FPP_VH
`define FPP_VH

package fpp;
    
    parameter int unsigned FPU_S_EXP_WIDTH = 8;
    parameter int unsigned FPU_S_MANT_WIDTH = 23;

    typedef struct packed {
        logic                           sign;
        logic [FPU_S_EXP_WIDTH-1:0]     exp;
        logic [FPU_S_MANT_WIDTH-1:0]    mant;
    } single_t;

    parameter int unsigned FPU_D_EXP_WIDTH = 11;
    parameter int unsigned FPU_D_MANT_WIDTH = 52;
    parameter int unsigned FPU_D_MANT_UPPER_WIDTH = 20; // 52 - 32 = 20

    typedef struct packed {
        logic [FPU_D_MANT_UPPER_WIDTH-1:0]  upper;
        single_t                            single;
    } double_mant_t;

    typedef struct packed {
        logic                           sign;
        logic [FPU_D_EXP_WIDTH-1:0]     exp;
        double_mant_t                   mant;
    } double_t;

    typedef struct packed {
        logic NV; // invalid
        logic DZ; // divide by zero
        logic OF; // overflow
        logic UF; // underflow
        logic NX; // inexact
    } fpu_except_t;

    parameter single_t CNAN_S = '{
        sign:   1'b0,
        exp:    8'hFF,
        mant:   1'b1 << (FPU_S_MANT_WIDTH-1) // msb = 1
    };

    parameter double_t CNAN_D = '{
        sign:   1'b0,
        exp:    11'h7FF,
        mant:   1'b1 << (FPU_D_MANT_WIDTH-1) // msb = 1
    };

    function logic is_inf_s (single_t in);
        return (in.exp == 8'hFF) & (in.mant == 23'h0);
    endfunction

    function logic is_inf_d (double_t in);
        return (in.exp == 11'h7FF) & (in.mant == 52'h0);
    endfunction

    function logic is_nan_s (single_t in);
        return (in.exp == 8'hFF) & |in.mant;
    endfunction

    function logic nan_is_qnan_s (single_t in);
        return in.mant[FPU_S_MANT_WIDTH-1];
    endfunction

    function logic nan_is_snan_s (single_t in);
        return ~in.mant[FPU_S_MANT_WIDTH-1];
    endfunction

    function logic is_nan_d (double_t in);
        return (in.exp == 11'h7FF) & |in.mant;
    endfunction

    function logic nan_is_qnan_d (double_t in);
        return in.mant[FPU_D_MANT_WIDTH-1];
    endfunction

    function logic nan_is_snan_d (double_t in);
        return ~in.mant[FPU_D_MANT_WIDTH-1];
    endfunction

    function logic is_boxed_d (double_t in);
        return in.sign & (in.exp == 11'h7FF) & (in.mant.upper == 20'hFFFFF);
    endfunction

    function logic s_eq_s (single_t A, single_t B);
        return (
            A == B
            | (A.exp == 0 & B.exp == 0 & A.mant == 0 & B.mant == 0)
        );
    endfunction

    function logic d_eq_d (double_t A, double_t B);
        return (
            A == B
            | (A.exp == 0 & B.exp == 0 & A.mant == 0 & B.mant == 0)
        );
    endfunction

    function logic s_lt_s (single_t A, single_t B);
        return (
            // negative A, positive B
            A.sign & ~B.sign
            // A bigger negative than B
            | A.sign & B.sign & (
                A.exp > B.exp
                | (A.exp == B.exp) & (A.mant > B.mant)
            )
            // A smaller positive than B
            | ~A.sign & ~B.sign & (
                A.exp < B.exp
                | (A.exp == B.exp) & (A.mant < B.mant)
            )
        ); 
    endfunction

    function logic d_lt_d (double_t A, double_t B);
        return (
            // negative A, positive B
            A.sign & ~B.sign
            // A bigger negative than B
            | A.sign & B.sign & (
                A.exp > B.exp
                | (A.exp == B.exp) & (A.mant > B.mant)
            )
            // A smaller positive than B
            | ~A.sign & ~B.sign & (
                A.exp < B.exp
                | (A.exp == B.exp) & (A.mant < B.mant)
            )
        ); 
    endfunction

endpackage

`endif // COREP_VH