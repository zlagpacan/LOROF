/*
    Filename: fpu_easy.sv
    Author: zlagpacan
    Description: Easy FPU Instructions
    Spec: LOROF/spec/design/fpu_easy.md
*/

`include "corep.vh"

module fpu_easy #(

) (
    // fully comb

    // instr components
    input logic [6:0] funct7,
    input logic [2:0] funct3,

    // operands
    input corep::double_t A,
    input corep::double_t B,

    // outputs
    output corep::double_t result,
    output corep::fpu_except_t except
);

    // ----------------------------------------------------------------
    // Signals:

    

    // ----------------------------------------------------------------
    // Logic: 

    // can assume no illegal instr's at this point

    // big decoder
    always_comb begin

        unique casez (funct7)

            7'b00100?0: begin
                if (funct3[0]) begin
                    // FSGNJN.S
                    result.sign = 1'b1;
                    result.exp = 11'h7FF;
                    result.mant.upper = 20'hFFFFF;
                    result.mant.single.sign = ~B.mant.single.sign;
                    result.mant.single.exp = A.mant.single.exp;
                    result.mant.single.mant = A.mant.single.mant;
                    except = 5'b00000;
                end
                else if (funct3[1]) begin
                    // FSGNJX.S
                    result.sign = 1'b1;
                    result.exp = 11'h7FF;
                    result.mant.upper = 20'hFFFFF;
                    result.mant.single.sign = A.mant.single.sign ^ B.mant.single.sign;
                    result.mant.single.exp = A.mant.single.exp;
                    result.mant.single.mant = A.mant.single.mant;
                    except = 5'b00000;
                end
                else begin
                    // FSGNJ.S
                    result.sign = 1'b1;
                    result.exp = 11'h7FF;
                    result.mant.upper = 20'hFFFFF;
                    result.mant.single.sign = B.mant.single.sign;
                    result.mant.single.exp = A.mant.single.exp;
                    result.mant.single.mant = A.mant.single.mant;
                    except = 5'b00000;
                end
            end

            7'b00101?0: begin
                // NAN checking
                if () begin

                end
                else begin
                    if (funct3[0]) begin
                        // FMIN.S
                    end
                    else begin
                        // FMAX.S
                    end
                end
            end

FMV.X.W
FEQ.S
FLT.S
FLE.S
FCLASS.S

FMV.W.X

FSGNJ.D
FSGNJN.D
FSGNJX.D
FMIN.D
FMAX.D

FCVT.S.D
FCVT.D.S
FMV.X.D
FEQ.D
FLT.D
FLE.D
FCLASS.D

FMV.D.X
        endcase
    end

endmodule