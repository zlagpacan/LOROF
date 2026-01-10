/*
    Filename: alu.sv
    Author: zlagpacan
    Description: RTL for ALU comb block
    Spec: LOROF/spec/design/alu.md
*/

// TODO: 64-bit ALU ops
    // should have total of 15x ops now, can keep op[3:0]

// TODO: consider split ALU pipes
    // e.g. Arithmetic pipe + Logic pipe
    // can still share DQ, IQ
    // split for both Reg-Reg, and Reg-Imm
        // would be silly for this to be limiting bandwidth
    // especially valuable for 64-bit as adds may take more than 1 cycle

`include "core_types.vh"

module alu (
    input logic [3:0]           op,
    input core_types::XLEN_t    A,
    input core_types::XLEN_t    B,

    output core_types::XLEN_t   out
);

    always_comb begin
        casez (op)
            4'b0000:    out = A + B;
            4'b1000:    out = A - B;
            4'b?001:    out = A << B[4:0];
            4'b?010:    out = $signed(A) < $signed(B) ? 32'h1 : 32'h0;
            4'b?011:    out = A < B ? 32'h1 : 32'h0;
            4'b?100:    out = A ^ B;
            4'b0101:    out = A >> B[4:0];
            4'b1101:    out = $signed(A) >>> B[4:0];
            4'b?110:    out = A | B;
            4'b?111:    out = A & B;
        endcase
    end

endmodule