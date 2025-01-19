/*
    Filename: alu.sv
    Author: zlagpacan
    Description: RTL for ALU comb block
    Spec: LOROF/spec/design/alu.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu (
    input logic [3:0]   op,
    input logic [31:0]  A,
    input logic [31:0]  B,

    output logic [31:0] out
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