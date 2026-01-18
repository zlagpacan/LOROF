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
            instr_p::ALU_ADD:   out = A + B;
            instr_p::ALU_SLL:   out = A << B[5:0];
            instr_p::ALU_SLT:   out = $signed(A) < $signed(B) ? 64'h1 : 64'h0;
            instr_p::ALU_SLTU:  out = A < B ? 64'h1 : 64'h0;
            instr_p::ALU_XOR:   out = A ^ B;
            instr_p::ALU_SRL:   out = A >> B[5:0];
            instr_p::ALU_OR:    out = A | B;
            instr_p::ALU_AND:   out = A & B;
            instr_p::ALU_SUB:   out = A - B;
            instr_p::ALU_SRA:   out = $signed(A) >>> B[5:0];
            instr_p::ALU_ADDW: begin
                out[31:0] = A[31:0] + B[31:0];
                out[63:32] = {32{out[31]}};
            end
            instr_p::ALU_SUBW: begin
                out[31:0] = A[31:0] - B[31:0];
                out[63:32] = {32{out[31]}};
            end
            instr_p::ALU_SLLW: begin
                out[31:0] = A[31:0] << B[4:0];
                out[63:32] = {32{out[31]}};
            end
            instr_p::ALU_SRLW: begin
                out[31:0] = A[31:0] >> B[4:0];
                out[63:32] = {32{out[31]}};
            end
            instr_p::ALU_SRAW: begin
                out[31:0] = $signed(A[31:0]) >>> B[4:0];
                out[63:32] = {32{out[31]}};
            end
            default:                out = A + B;
        endcase
    end

endmodule