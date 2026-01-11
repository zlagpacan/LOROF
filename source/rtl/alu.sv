/*
    Filename: alu.sv
    Author: zlagpacan
    Description: RTL for ALU comb block
    Spec: LOROF/spec/design/alu.md
*/

// TODO: 64-bit ALU ops
    // should have total of 15x ops now, can keep op[3:0]

`include "instr_types.vh"

module alu (
    input logic [3:0]       op,
    input logic [63:0]      A,
    input logic [63:0]      B,

    output logic [63:0]     out
);

    always_comb begin
        unique casez (op)
            instr_types::ALU_ADD:   out = A + B;
            instr_types::ALU_SLL:   out = A << B[5:0];
            instr_types::ALU_SLT:   out = $signed(A) < $signed(B) ? 64'h1 : 64'h0;
            instr_types::ALU_SLTU:  out = A < B ? 64'h1 : 64'h0;
            instr_types::ALU_XOR:   out = A ^ B;
            instr_types::ALU_SRL:   out = A >> B[5:0];
            instr_types::ALU_OR:    out = A | B;
            instr_types::ALU_AND:   out = A & B;
            instr_types::ALU_SUB:   out = A - B;
            instr_types::ALU_SRA:   out = $signed(A) >>> B[5:0];
            instr_types::ALU_ADDW: begin
                out[31:0] = A[31:0] + B[31:0];
                out[63:32] = {32{out[31]}};
            end
            instr_types::ALU_SUBW: begin
                out[31:0] = A[31:0] - B[31:0];
                out[63:32] = {32{out[31]}};
            end
            instr_types::ALU_SLLW: begin
                out[31:0] = A[31:0] << B[4:0];
                out[63:32] = {32{out[31]}};
            end
            instr_types::ALU_SRLW: begin
                out[31:0] = A[31:0] >> B[4:0];
                out[63:32] = {32{out[31]}};
            end
            instr_types::ALU_SRAW: begin
                out[31:0] = $signed(A[31:0]) >>> B[4:0];
                out[63:32] = {32{out[31]}};
            end
            default:                out = A + B;
        endcase
    end

endmodule