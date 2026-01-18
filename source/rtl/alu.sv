/*
    Filename: alu.sv
    Author: zlagpacan
    Description: RTL for ALU comb block
    Spec: LOROF/spec/design/alu.md
*/

`include "instrp.vh"

module alu (
    input logic [3:0]       op,
    input logic [63:0]      A,
    input logic [63:0]      B,

    output logic [63:0]     out
);

    always_comb begin
        unique casez (op)
            instrp::ALU_ADD:    out = A + B;
            instrp::ALU_SLL:    out = A << B[5:0];
            instrp::ALU_SLT:    out = $signed(A) < $signed(B) ? 64'h1 : 64'h0;
            instrp::ALU_SLTU:   out = A < B ? 64'h1 : 64'h0;
            instrp::ALU_XOR:    out = A ^ B;
            instrp::ALU_SRL:    out = A >> B[5:0];
            instrp::ALU_OR:     out = A | B;
            instrp::ALU_AND:    out = A & B;
            instrp::ALU_SUB:    out = A - B;
            instrp::ALU_SRA:    out = $signed(A) >>> B[5:0];
            instrp::ALU_ADDW: begin
                                out[31:0] = A[31:0] + B[31:0];
                                out[63:32] = {32{out[31]}};
            end
            instrp::ALU_SUBW: begin
                                out[31:0] = A[31:0] - B[31:0];
                                out[63:32] = {32{out[31]}};
            end
            instrp::ALU_SLLW: begin
                                out[31:0] = A[31:0] << B[4:0];
                                out[63:32] = {32{out[31]}};
            end
            instrp::ALU_SRLW: begin
                                out[31:0] = A[31:0] >> B[4:0];
                                out[63:32] = {32{out[31]}};
            end
            instrp::ALU_SRAW: begin
                                out[31:0] = $signed(A[31:0]) >>> B[4:0];
                                out[63:32] = {32{out[31]}};
            end
            default:            out = A + B;
        endcase
    end

endmodule