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

    logic lower63b_lt;

    logic [63:0] shift_in;

    logic [63:0] sll64_5b;
    logic [63:0] srl64_5b;
    logic [63:0] sra64_5b;

    logic [63:0] sll64_6b;
    logic [63:0] srl64_6b;
    logic [63:0] sra64_6b;

    always_comb begin
        lower63b_lt = A[62:0] < B[62:0];
    end

    always_comb begin
        if (op == instrp::ALU_SLLW | op == instrp::ALU_SRLW | op == instrp::ALU_SRAW) begin
            shift_in = {{32{A[31] & (op == instrp::ALU_SRAW)}}, A[31:0]};
        end
        else begin
            shift_in = A;
        end

        sll64_5b = shift_in << B[4:0];
        srl64_5b = shift_in >> B[4:0];
        sra64_5b = $signed(shift_in) >>> B[4:0];

        if (B[5]) begin
            sll64_6b = {sll64_5b[31:0], 32'h0};
            srl64_6b = {32'h0, srl64_5b[63:32]};
            sra64_6b = {{32{sra64_5b[63]}}, sra64_5b[63:32]};
        end
        else begin
            sll64_6b = sll64_5b;
            srl64_6b = srl64_5b;
            sra64_6b = sra64_5b;
        end
    end

    // case with shared intermediates:
    always_comb begin
        unique casez (op)
            instrp::ALU_ADD:    out = A + B;
            instrp::ALU_SLL:    out = sll64_6b;
            instrp::ALU_SLT:    out = A[63] & ~B[63] | ~(A[63] ^ B[63]) & lower63b_lt ? 64'h1 : 64'h0;
            instrp::ALU_SLTU:   out = ~A[63] & B[63] | ~(A[63] ^ B[63]) & lower63b_lt ? 64'h1 : 64'h0;
            instrp::ALU_XOR:    out = A ^ B;
            instrp::ALU_SRL:    out = srl64_6b;
            instrp::ALU_OR:     out = A | B;
            instrp::ALU_AND:    out = A & B;
            instrp::ALU_SUB:    out = A - B;
            instrp::ALU_SRA:    out = sra64_6b;
            instrp::ALU_ADDW: begin
                                out[31:0] = A[31:0] + B[31:0];
                                out[63:32] = {32{out[31]}};
            end
            instrp::ALU_SUBW: begin
                                out[31:0] = A[31:0] - B[31:0];
                                out[63:32] = {32{out[31]}};
            end
            instrp::ALU_SLLW:   out = {{32{sll64_5b[31]}}, sll64_5b[31:0]};
            instrp::ALU_SRLW:   out = {{32{srl64_5b[31]}}, srl64_5b[31:0]};
            instrp::ALU_SRAW:   out = {{32{sra64_5b[31]}}, sra64_5b[31:0]};
            default:            out = A + B;
        endcase
    end

    // // simple case:
    // always_comb begin
    //     unique casez (op)
    //         instrp::ALU_ADD:    out = A + B;
    //         instrp::ALU_SLL:    out = A << B[5:0];
    //         instrp::ALU_SLT:    out = $signed(A) < $signed(B) ? 64'h1 : 64'h0;
    //         instrp::ALU_SLTU:   out = A < B ? 64'h1 : 64'h0;
    //         instrp::ALU_XOR:    out = A ^ B;
    //         instrp::ALU_SRL:    out = A >> B[5:0];
    //         instrp::ALU_OR:     out = A | B;
    //         instrp::ALU_AND:    out = A & B;
    //         instrp::ALU_SUB:    out = A - B;
    //         instrp::ALU_SRA:    out = $signed(A) >>> B[5:0];
    //         instrp::ALU_ADDW: begin
    //                             out[31:0] = A[31:0] + B[31:0];
    //                             out[63:32] = {32{out[31]}};
    //         end
    //         instrp::ALU_SUBW: begin
    //                             out[31:0] = A[31:0] - B[31:0];
    //                             out[63:32] = {32{out[31]}};
    //         end
    //         instrp::ALU_SLLW: begin
    //                             out[31:0] = A[31:0] << B[4:0];
    //                             out[63:32] = {32{out[31]}};
    //         end
    //         instrp::ALU_SRLW: begin
    //                             out[31:0] = A[31:0] >> B[4:0];
    //                             out[63:32] = {32{out[31]}};
    //         end
    //         instrp::ALU_SRAW: begin
    //                             out[31:0] = $signed(A[31:0]) >>> B[4:0];
    //                             out[63:32] = {32{out[31]}};
    //         end
    //         default:            out = A + B;
    //     endcase
    // end

endmodule