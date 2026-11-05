/*
    Filename: fpu_easy.sv
    Author: zlagpacan
    Description: Easy FPU Instructions
    Spec: LOROF/spec/design/fpu_easy.md
*/

`include "fpp.vh"

module fpu_easy #(

) (
    // fully comb

    // instr components
    input logic [6:0] funct7,
    input logic [2:0] funct3,

    // operands
    input fpp::double_t A_d,
    input fpp::double_t B_d,

    input fpp::single_t A_s_boxed, // post NaN-box check
    input fpp::single_t B_s_boxed, // post NaN-box check

    // outputs
    output fpp::double_t result_d,
    output fpp::fpu_except_t except
);

    // ----------------------------------------------------------------
    // Signals:

    // helper signals
    logic A_lt_B_s;
    logic A_lt_B_d;

    logic A_eq_B_s;
    logic A_eq_B_d;

    // ----------------------------------------------------------------
    // Logic: 

    // can assume no illegal instr's at this point

    // helpers
    always_comb begin
        A_lt_B_s = fpp::s_lt_s(A_s_boxed, B_s_boxed);
        A_lt_B_d = fpp::d_lt_d(A_d, B_d);

        A_eq_B_s = A_s_boxed == B_s_boxed;
        A_eq_B_d = A_d == B_d;
    end

    // big decoder
    always_comb begin

        // activate exception flags where relevant in case
        except.NV = 1'b0;
        except.DZ = 1'b0;
        except.OF = 1'b0;
        except.UF = 1'b0;
        except.NX = 1'b0;

        casez (funct7)

            7'b00100?0: begin
                // FSGNJ*.S -> don't check for NaN boxing

                // start w/ NaN box
                result_d.sign = 1'b1;
                result_d.exp = 11'h7FF;
                result_d.mant.upper = 20'hFFFFF;

                // guaranteed rest of result_d from A
                result_d.mant.single.exp = A_d.mant.single.exp;
                result_d.mant.single.mant = A_d.mant.single.mant;

                if (funct3[0]) begin
                    // FSGNJN.S
                    result_d.mant.single.sign = ~B_d.mant.single.sign;
                end
                else if (funct3[1]) begin
                    // FSGNJX.S
                    result_d.mant.single.sign = A_d.mant.single.sign ^ B_d.mant.single.sign;
                end
                else begin
                    // FSGNJ.S
                    result_d.mant.single.sign = B_d.mant.single.sign;
                end
            end

            7'b00101?0: begin
                // FMIN.S, FMAX.S -> check for NaN boxing

                // start w/ NaN box
                result_d.sign = 1'b1;
                result_d.exp = 11'h7FF;
                result_d.mant.upper = 20'hFFFFF;

                // NaN operands
                if (fpp::is_nan_s(A_s_boxed) & fpp::is_nan_s(B_s_boxed)) begin
                    // output cNaN
                    result_d.mant.single = fpp::CNAN_S;
                    except.NV = fpp::nan_is_snan_s(A_s_boxed) | fpp::nan_is_snan_s(B_s_boxed);
                end
                else if (fpp::is_nan_s(A_s_boxed)) begin
                    // output B which is not NaN
                    result_d.mant.single = B_s_boxed;
                    except.NV = fpp::nan_is_snan_s(B_s_boxed);
                end
                else if (fpp::is_nan_s(B_s_boxed)) begin
                    // output A which is not NaN
                    result_d.mant.single = A_s_boxed;
                    except.NV = fpp::nan_is_snan_s(A_s_boxed);
                end

                // no NaN operands
                else begin
                    if (funct3[0]) begin
                        // FMIN.S
                        if (A_lt_B_s)   result_d.mant.single = A_s_boxed;
                        else            result_d.mant.single = B_s_boxed;
                    end
                    else begin
                        // FMAX.S
                        if (A_lt_B_s)   result_d.mant.single = B_s_boxed;
                        else            result_d.mant.single = A_s_boxed;
                    end
                end
            end

            7'b111?0?0: begin
                // FMV.X.W, FMV.W.X -> don't check for NaN boxing

                // NaN boxing == sign extension, so these are equivalent

                // start w/ NaN box
                result_d.sign = 1'b1;
                result_d.exp = 11'h7FF;
                result_d.mant.upper = 20'hFFFFF;

                result_d.mant.single = A_d.mant.single;
            end

            7'b10100?0: begin
                // FEQ.S, FLT.S, FLE.S -> check for NaN boxing

                // start w/ NaN box
                result_d.sign = 1'b1;
                result_d.exp = 11'h7FF;
                result_d.mant.upper = 20'hFFFFF;

                if (funct3[1]) begin
                    // FEQ.S
                    if (fpp::is_nan_s(A_s_boxed) | fpp::is_nan_s(B_s_boxed)) begin
                        result_d.mant.single = 32'h0;
                        except.NV = 
                            fpp::is_nan_s(A_s_boxed) & fpp::nan_is_snan_s(A_s_boxed) 
                            | fpp::is_nan_s(B_s_boxed) & fpp::nan_is_snan_s(B_s_boxed)
                        ;
                    end
                    else if (A_eq_B_s) begin
                        result_d.mant.single = 32'h1;
                    end
                    else begin
                        result_d.mant.single = 32'h0;
                    end
                end
                else if (funct3[0]) begin
                    // FLT.S
                    if (fpp::is_nan_s(A_s_boxed) | fpp::is_nan_s(B_s_boxed)) begin
                        result_d.mant.single = 32'h0;
                        except.NV = 1'b1;
                    end
                    else if (A_lt_B_s) begin
                        result_d.mant.single = 32'h1;
                    end
                    else begin
                        result_d.mant.single = 32'h0;
                    end
                end
                else begin
                    // FLE.S
                    if (fpp::is_nan_s(A_s_boxed) | fpp::is_nan_s(B_s_boxed)) begin
                        result_d.mant.single = 32'h0;
                        except.NV = 1'b1;
                    end
                    else if (A_lt_B_s | A_eq_B_s) begin
                        result_d.mant.single = 32'h1;
                    end
                    else begin
                        result_d.mant.single = 32'h0;
                    end
                end
            end

            7'b11100?0: begin
                // FCLASS.S -> check for NaN boxing

                // start w/ 0, set bit for class of interest
                result_d = 64'h0;

                // inf
                if (fpp::is_inf_s(A_s_boxed)) begin
                    if (A_s_boxed.sign)     result_d[0] = 1'b1; // -inf
                    else                    result_d[7] = 1'b1; // +inf
                end
                // NaN
                else if (fpp::is_nan_s(A_s_boxed)) begin
                    if (fpp::nan_is_snan_s(A_s_boxed))  result_d[8] = 1'b1; // sNaN
                    else                                result_d[9] = 1'b1; // qNaN
                end
                // zero and subnormal
                else if (A_s_boxed.exp == 8'h00) begin
                    if (A_s_boxed.mant == 23'h000000) begin
                        if (A_s_boxed.sign)     result_d[3] = 1'b1; // -0.0
                        else                    result_d[4] = 1'b1; // +0.0
                    end
                    else begin
                        if (A_s_boxed.sign)     result_d[2] = 1'b1; // neg subnormal
                        else                    result_d[5] = 1'b1; // pos subnormal
                    end
                end
                // normal
                else begin
                    if (A_s_boxed.sign)     result_d[1] = 1'b1; // neg normal
                    else                    result_d[6] = 1'b1; // pos normal
                end
            end

            7'b00100?1: begin
                // FSGNJ*.D

                // guaranteed rest of result from A
                result_d.exp = A_d.exp;
                result_d.mant = A_d.mant;

                if (funct3[0]) begin
                    // FSGNJN.D
                    result_d.sign = ~B_d.sign;
                end
                else if (funct3[1]) begin
                    // FSGNJX.D
                    result_d.sign = A_d.sign ^ B_d.sign;
                end
                else begin
                    // FSGNJ.D
                    result_d.sign = B_d.sign;
                end
            end

            7'b00101?1: begin
                // FMIN.D, FMAX.D

                // NaN operands
                if (fpp::is_nan_d(A_d) & fpp::is_nan_d(B_d)) begin
                    // output cNaN
                    result_d = fpp::CNAN_D;
                    except.NV = fpp::nan_is_snan_d(A_d) | fpp::nan_is_snan_d(B_d);
                end
                else if (fpp::is_nan_d(A_d)) begin
                    // output B which is not NaN
                    result_d = B_d;
                    except.NV = fpp::nan_is_snan_d(B_d);
                end
                else if (fpp::is_nan_d(B_d)) begin
                    // output A which is not NaN
                    result_d = A_d;
                    except.NV = fpp::nan_is_snan_d(A_d);
                end

                // no NaN operands
                else begin
                    if (funct3[0]) begin
                        // FMIN.D
                        if (A_lt_B_d)   result_d = A_d;
                        else            result_d = B_d;
                    end
                    else begin
                        // FMAX.D
                        if (A_lt_B_d)   result_d = B_d;
                        else            result_d = A_d;
                    end
                end
            end

            7'b111?0?1: begin
                // FMV.X.D, FMV.D.X

                // just 64b transfer
                result_d = A_d;
            end

            7'b10100?1: begin
                // FEQ.D, FLT.D, FLE.D

                if (funct3[1]) begin
                    // FEQ.D
                    if (fpp::is_nan_d(A_d) | fpp::is_nan_d(B_d)) begin
                        result_d = 64'h0;
                        except.NV = 
                            fpp::is_nan_d(A_d) & fpp::nan_is_snan_d(A_d) 
                            | fpp::is_nan_d(B_d) & fpp::nan_is_snan_d(B_d)
                        ;
                    end
                    else if (A_eq_B_d) begin
                        result_d = 64'h1;
                    end
                    else begin
                        result_d = 64'h0;
                    end
                end
                else if (funct3[0]) begin
                    // FLT.D
                    if (fpp::is_nan_d(A_d) | fpp::is_nan_d(B_d)) begin
                        result_d = 64'h0;
                        except.NV = 1'b1;
                    end
                    else if (A_lt_B_d) begin
                        result_d = 64'h1;
                    end
                    else begin
                        result_d = 64'h0;
                    end
                end
                else begin
                    // FLE.D
                    if (fpp::is_nan_d(A_d) | fpp::is_nan_d(B_d)) begin
                        result_d = 64'h0;
                        except.NV = 1'b1;
                    end
                    else if (A_lt_B_d | A_eq_B_d) begin
                        result_d = 64'h1;
                    end
                    else begin
                        result_d = 64'h0;
                    end
                end
            end

            7'b11100?1: begin
                // FCLASS.D

                // start w/ 0, set bit for class of interest
                result_d = 64'h0;

                // inf
                if (fpp::is_inf_d(A_d)) begin
                    if (A_d.sign)   result_d[0] = 1'b1; // -inf
                    else            result_d[7] = 1'b1; // +inf
                end
                // NaN
                else if (fpp::is_nan_d(A_d)) begin
                    if (fpp::nan_is_snan_d(A_d))    result_d[8] = 1'b1; // sNaN
                    else                            result_d[9] = 1'b1; // qNaN
                end
                // zero and subnormal
                else if (A_d.exp == 8'h00) begin
                    if (A_d.mant == 23'h000000) begin
                        if (A_d.sign)   result_d[3] = 1'b1; // -0.0
                        else            result_d[4] = 1'b1; // +0.0
                    end
                    else begin
                        if (A_d.sign)   result_d[2] = 1'b1; // neg subnormal
                        else            result_d[5] = 1'b1; // pos subnormal
                    end
                end
                // normal
                else begin
                    if (A_d.sign)   result_d[1] = 1'b1; // neg normal
                    else            result_d[6] = 1'b1; // pos normal
                end
            end

            default: begin
                // default to cNaN
                result_d = fpp::CNAN_D;
            end

        endcase
    end

endmodule