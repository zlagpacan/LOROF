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
    output fpp::double_t result,
    output fpp::fpu_except_t except
);

    // ----------------------------------------------------------------
    // Signals:

    // helper signals
    logic A_lt_B_s;
    logic A_lt_B_d;

    // ----------------------------------------------------------------
    // Logic: 

    // can assume no illegal instr's at this point

    // helpers
    always_comb begin
        A_lt_B_s = fpp::s_lt_s(A_s_boxed, B_s_boxed);
        A_lt_B_d = fpp::d_lt_d(A_d, B_d);
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
                result.sign = 1'b1;
                result.exp = 11'h7FF;
                result.mant.upper = 20'hFFFFF;

                // guaranteed rest of result from A
                result.mant.single.exp = A_d.mant.single.exp;
                result.mant.single.mant = A_d.mant.single.mant;

                if (funct3[0]) begin
                    // FSGNJN.S
                    result.mant.single.sign = ~B_d.mant.single.sign;
                end
                else if (funct3[1]) begin
                    // FSGNJX.S
                    result.sign = 1'b1;
                    result.mant.single.sign = A_d.mant.single.sign ^ B_d.mant.single.sign;
                end
                else begin
                    // FSGNJ.S
                    result.mant.single.sign = B_d.mant.single.sign;
                end
            end

            7'b00101?0: begin
                // FMIN.S, FMAX.S -> check for NaN boxing

                // start w/ NaN box
                result.sign = 1'b1;
                result.exp = 11'h7FF;
                result.mant.upper = 20'hFFFFF;

                // NaN operands
                if (fpp::is_nan_s(A_s_boxed) & fpp::is_nan_s(B_s_boxed)) begin
                    // output cNaN
                    result.mant.single = fpp::CNAN_S;
                    except.NV = fpp::nan_is_snan_s(A_s_boxed) | fpp::nan_is_snan_s(B_s_boxed);
                end
                else if (fpp::is_nan_s(A_s_boxed)) begin
                    // output B which is not NaN
                    result.mant.single = B_s_boxed;
                    except.NV = fpp::nan_is_snan_s(B_s_boxed);
                end
                else if (fpp::is_nan_s(B_s_boxed)) begin
                    // output A which is not NaN
                    result.mant.single = A_s_boxed;
                    except.NV = fpp::nan_is_snan_s(A_s_boxed);
                end

                // no NaN operands
                else begin
                    if (funct3[0]) begin
                        // FMIN.S
                        if (A_lt_B_s)   result.mant.single = A_s_boxed;
                        else            result.mant.single = B_s_boxed;
                    end
                    else begin
                        // FMAX.S
                        if (A_lt_B_s)   result.mant.single = B_s_boxed;
                        else            result.mant.single = A_s_boxed;
                    end
                end
            end

            // FMV.X.W
            // FEQ.S
            // FLT.S
            // FLE.S
            // FCLASS.S

            // FMV.W.X

            // FSGNJ.D
            // FSGNJN.D
            // FSGNJX.D
            // FMIN.D
            // FMAX.D

            // FCVT.S.D
            // FCVT.D.S
            // FMV.X.D
            // FEQ.D
            // FLT.D
            // FLE.D
            // FCLASS.D

            // FMV.D.X

            default: begin
                
            end

        endcase
    end

endmodule