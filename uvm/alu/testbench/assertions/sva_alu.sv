/*
  Module        : alu
  UMV Component : SVA Assertions
  Author        : Adam Keith
*/

`ifndef ALU_SVA_SV
`define ALU_SVA_SV


// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_sva (
    input logic CLK,
    input logic [3:0] op,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] out
);

   // ALU Operation 0: Add
    property sva_alu_add;
        @(posedge CLK) (op == 4'b0000) |-> (out == (A + B));
    endproperty
    assert property (sva_alu_add) begin
        $display("SVA_INFO @%t ALU_ADD - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_ADD - FAILED", $time());
    end
    c_ALU_ADD: cover property (sva_alu_add);

    // ALU Operation 1: Shift Left
    property sva_alu_shift_left;
        @(posedge CLK) (op == 4'b0001) |-> (out == (A << B[4:0]));
    endproperty
    assert property (sva_alu_shift_left) begin
        $display("SVA_INFO @%t ALU_SHIFT_LEFT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_SHIFT_LEFT - FAILED", $time());
    end
    c_ALU_SHIFT_LEFT: cover property (sva_alu_shift_left);

    // ALU Operation 2: Signed Less Than
    property sva_alu_signed_lt;
        @(posedge CLK) (op == 4'b0010) |-> (out == ($signed(A) < $signed(B) ? '1 : '0));
    endproperty
    assert property (sva_alu_signed_lt) begin
        $display("SVA_INFO @%t ALU_SIGNED_LT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_SIGNED_LT - FAILED", $time());
    end
    c_ALU_SIGNED_LT: cover property (sva_alu_signed_lt);

    // ALU Operation 3: Unsigned Less Than
    property sva_alu_unsigned_lt;
        @(posedge CLK) (op == 4'b0011) |-> (out == ($unsigned(A) < $unsigned(B) ? '1 : '0));
    endproperty
    assert property (sva_alu_unsigned_lt) begin
        $display("SVA_INFO @%t ALU_UNSIGNED_LT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_UNSIGNED_LT - FAILED", $time());
    end
    c_ALU_UNSIGNED_LT: cover property (sva_alu_unsigned_lt);

    // ALU Operation 4: XOR
    property sva_alu_xor;
        @(posedge CLK) (op == 4'b0100) |-> (out == (A ^ B));
    endproperty
    assert property (sva_alu_xor) begin
        $display("SVA_INFO @%t ALU_XOR - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_XOR - FAILED", $time());
    end
    c_ALU_XOR: cover property (sva_alu_xor);

    // ALU Operation 5: Shift Right
    property sva_alu_shift_right;
        @(posedge CLK) (op == 4'b0101) |-> (out == (A >> B[4:0]));
    endproperty
    assert property (sva_alu_shift_right) begin
        $display("SVA_INFO @%t ALU_SHIFT_RIGHT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_SHIFT_RIGHT - FAILED", $time());
    end
    c_ALU_SHIFT_RIGHT: cover property (sva_alu_shift_right);

    // ALU Operation 6: OR
    property sva_alu_or;
        @(posedge CLK) (op == 4'b0110) |-> (out == (A | B));
    endproperty
    assert property (sva_alu_or) begin
        $display("SVA_INFO @%t ALU_OR - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_OR - FAILED", $time());
    end
    c_ALU_OR: cover property (sva_alu_or);

    // ALU Operation 7: AND
    property sva_alu_and;
        @(posedge CLK) (op == 4'b0111) |-> (out == (A & B));
    endproperty
    assert property (sva_alu_and) begin
        $display("SVA_INFO @%t ALU_AND - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_AND - FAILED", $time());
    end
    c_ALU_AND: cover property (sva_alu_and);

    // ALU Operation 8: Subtract
    property sva_alu_sub;
        @(posedge CLK) (op == 4'b1000) |-> (out == (A - B));
    endproperty
    assert property (sva_alu_sub) begin
        $display("SVA_INFO @%t ALU_SUB - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_SUB - FAILED", $time());
    end
    c_ALU_SUB: cover property (sva_alu_sub);

    // ALU Operation 9: Shift Left (Repeat)
    property sva_alu_shift_left_repeat;
        @(posedge CLK) (op == 4'b1001) |-> (out == (A << B[4:0]));
    endproperty
    assert property (sva_alu_shift_left_repeat) begin
        $display("SVA_INFO @%t ALU_SHIFT_LEFT_REPEAT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_SHIFT_LEFT_REPEAT - FAILED", $time());
    end
    c_ALU_SHIFT_LEFT_REPEAT: cover property (sva_alu_shift_left_repeat);

    // ALU Operation 10: Signed Less Than (Repeat)
    property sva_alu_signed_lt_repeat;
        @(posedge CLK) (op == 4'b1010) |-> (out == ($signed(A) < $signed(B) ? '1 : '0));
    endproperty
    assert property (sva_alu_signed_lt_repeat) begin
        $display("SVA_INFO @%t ALU_SIGNED_LT_REPEAT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_SIGNED_LT_REPEAT - FAILED", $time());
    end
    c_ALU_SIGNED_LT_REPEAT: cover property (sva_alu_signed_lt_repeat);

    // ALU Operation 11: Unsigned Less Than (Repeat)
    property sva_alu_unsigned_lt_repeat;
        @(posedge CLK) (op == 4'b1011) |-> (out == ($unsigned(A) < $unsigned(B) ? '1 : '0));
    endproperty
    assert property (sva_alu_unsigned_lt_repeat) begin
        $display("SVA_INFO @%t ALU_UNSIGNED_LT_REPEAT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_UNSIGNED_LT_REPEAT - FAILED", $time());
    end
    c_ALU_UNSIGNED_LT_REPEAT: cover property (sva_alu_unsigned_lt_repeat);

    // ALU Operation 12: XOR (Repeat)
    property sva_alu_xor_repeat;
        @(posedge CLK) (op == 4'b1100) |-> (out == (A ^ B));
    endproperty
    assert property (sva_alu_xor_repeat) begin
        $display("SVA_INFO @%t ALU_XOR_REPEAT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_XOR_REPEAT - FAILED", $time());
    end
    c_ALU_XOR_REPEAT: cover property (sva_alu_xor_repeat);

    // ALU Operation 13: Signed Arithmetic Shift Right
    property sva_alu_arith_shift_right;
        @(posedge CLK) (op == 4'b1101) |-> (out == ($signed(A) >>> B[4:0]));
    endproperty
    assert property (sva_alu_arith_shift_right) begin
        $display("SVA_INFO @%t ALU_ARITH_SHIFT_RIGHT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_ARITH_SHIFT_RIGHT - FAILED", $time());
    end
    c_ALU_ARITH_SHIFT_RIGHT: cover property (sva_alu_arith_shift_right);

    // ALU Operation 14: OR (Repeat)
    property sva_alu_or_repeat;
        @(posedge CLK) (op == 4'b1110) |-> (out == (A | B));
    endproperty
    assert property (sva_alu_or_repeat) begin
        $display("SVA_INFO @%t ALU_OR_REPEAT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_OR_REPEAT - FAILED", $time());
    end
    c_ALU_OR_REPEAT: cover property (sva_alu_or_repeat);

    // ALU Operation 15: AND (Repeat)
    property sva_alu_and_repeat;
        @(posedge CLK) (op == 4'b1111) |-> (out == (A & B));
    endproperty
    assert property (sva_alu_and_repeat) begin
        $display("SVA_INFO @%t ALU_AND_REPEAT - PASSED", $time());
    end else begin
        $display("SVA_INFO @%t ALU_AND_REPEAT - FAILED", $time());
    end
    c_ALU_AND_REPEAT: cover property (sva_alu_and_repeat);

endmodule

`endif