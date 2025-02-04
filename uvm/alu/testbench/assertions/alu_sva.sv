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

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

module alu_sva (
    input logic CLK,
    input logic [3:0] op,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] out
);

    // --- ALU Operation 0: Add --- //
    property sva_alu_add;
        @(posedge CLK) 
        (op == 4'b0000) |-> (out == (A + B));
    endproperty

    // --- ALU Operation 1: Shift Left --- //
    property sva_alu_shift_left;
        @(posedge CLK) 
        (op == 4'b0001) |-> (out == (A << B[4:0]));
    endproperty

    // --- ALU Operation 2: Signed Less Than --- //
    property sva_alu_signed_lt;
        @(posedge CLK) 
        (op == 4'b0010) |-> (out == ($signed(A) < $signed(B) ? 32'h1 : '0));
    endproperty

    // --- ALU Operation 3: Unsigned Less Than --- //
    property sva_alu_unsigned_lt;
        @(posedge CLK) 
        (op == 4'b0011) |-> (out == ((A < B) ? 32'h1 : '0));
    endproperty

    // --- ALU Operation 4: XOR --- //
    property sva_alu_xor;
        @(posedge CLK) 
        (op == 4'b0100) |-> (out == (A ^ B));
    endproperty

    // --- ALU Operation 5: Shift Right --- //
    property sva_alu_shift_right;
        @(posedge CLK) 
        (op == 4'b0101) |-> (out == (A >> B[4:0]));
    endproperty

    // --- ALU Operation 6: OR --- //
    property sva_alu_or;
        @(posedge CLK) 
        (op == 4'b0110) |-> (out == (A | B));
    endproperty

    // --- ALU Operation 7: AND --- //
    property sva_alu_and;
        @(posedge CLK) 
        (op == 4'b0111) |-> (out == (A & B));
    endproperty

    // --- ALU Operation 8: Subtract --- //
    property sva_alu_sub;
        @(posedge CLK) 
        (op == 4'b1000) |-> (out == (A - B));
    endproperty

    // --- ALU Operation 9: Shift Left (Repeat) --- //
    property sva_alu_shift_left_repeat;
        @(posedge CLK) 
        (op == 4'b1001) |-> (out == (A << B[4:0]));
    endproperty

    // --- ALU Operation 10: Signed Less Than (Repeat) --- //
    property sva_alu_signed_lt_repeat;
        @(posedge CLK) 
        (op == 4'b1010) |-> (out == ($signed(A) < $signed(B) ? 32'h1 : '0));
    endproperty

    // --- ALU Operation 11: Unsigned Less Than (Repeat) --- //
    property sva_alu_unsigned_lt_repeat;
        @(posedge CLK) 
        (op == 4'b1011) |-> (out == ((A < B) ? 32'h1 : '0));
    endproperty

    // --- ALU Operation 12: XOR (Repeat) --- //
    property sva_alu_xor_repeat;
        @(posedge CLK) 
        (op == 4'b1100) |-> (out == (A ^ B));
    endproperty

    // --- ALU Operation 13: Signed Arithmetic Shift Right --- //
    property sva_alu_arith_shift_right;
        @(posedge CLK) 
        ((op == 4'b1101) |-> ($signed(out) == $signed(A) >>> B[4:0]));
    endproperty

    // --- ALU Operation 14: OR (Repeat) --- //
    property sva_alu_or_repeat;
        @(posedge CLK) 
        (op == 4'b1110) |-> (out == (A | B));
    endproperty

    // --- ALU Operation 15: AND (Repeat) --- //
    property sva_alu_and_repeat;
        @(posedge CLK) 
        (op == 4'b1111) |-> (out == (A & B));
    endproperty


    // --- Assertion and Cover Instances --- //

    // ALU Operation 0: Add
    assert property (sva_alu_add) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_ADD : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_ADD : FAILED"), UVM_LOW)
    end
    c_ALU_ADD: cover property (sva_alu_add);

    // ALU Operation 1: Shift Left
    assert property (sva_alu_shift_left) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SHIFT_LEFT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SHIFT_LEFT : FAILED"), UVM_LOW)
    end
    c_ALU_SHIFT_LEFT: cover property (sva_alu_shift_left);

    // ALU Operation 2: Signed Less Than
    assert property (sva_alu_signed_lt) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SIGNED_LT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SIGNED_LT : FAILED"), UVM_LOW)
    end
    c_ALU_SIGNED_LT: cover property (sva_alu_signed_lt);

    // ALU Operation 3: Unsigned Less Than
    assert property (sva_alu_unsigned_lt) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_UNSIGNED_LT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_UNSIGNED_LT : FAILED"), UVM_LOW)
    end
    c_ALU_UNSIGNED_LT: cover property (sva_alu_unsigned_lt);

    // ALU Operation 4: XOR
    assert property (sva_alu_xor) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_XOR : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_XOR : FAILED"), UVM_LOW)
    end
    c_ALU_XOR: cover property (sva_alu_xor);

    // ALU Operation 5: Shift Right
    assert property (sva_alu_shift_right) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SHIFT_RIGHT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SHIFT_RIGHT : FAILED"), UVM_LOW)
    end
    c_ALU_SHIFT_RIGHT: cover property (sva_alu_shift_right);

    // ALU Operation 6: OR
    assert property (sva_alu_or) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_OR : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_OR : FAILED"), UVM_LOW)
    end
    c_ALU_OR: cover property (sva_alu_or);

    // ALU Operation 7: AND
    assert property (sva_alu_and) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_AND : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_AND : FAILED"), UVM_LOW)
    end
    c_ALU_AND: cover property (sva_alu_and);

    // ALU Operation 8: Subtract
    assert property (sva_alu_sub) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SUB : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SUB : FAILED"), UVM_LOW)
    end
    c_ALU_SUB: cover property (sva_alu_sub);

    // ALU Operation 9: Shift Left (Repeat)
    assert property (sva_alu_shift_left_repeat) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SHIFT_LEFT_REPEAT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SHIFT_LEFT_REPEAT : FAILED"), UVM_LOW)
    end
    c_ALU_SHIFT_LEFT_REPEAT: cover property (sva_alu_shift_left_repeat);

    // ALU Operation 10: Signed Less Than (Repeat)
    assert property (sva_alu_signed_lt_repeat) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SIGNED_LT_REPEAT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_SIGNED_LT_REPEAT : FAILED"), UVM_LOW)
    end
    c_ALU_SIGNED_LT_REPEAT: cover property (sva_alu_signed_lt_repeat);

    // ALU Operation 11: Unsigned Less Than (Repeat)
    assert property (sva_alu_unsigned_lt_repeat) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_UNSIGNED_LT_REPEAT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_UNSIGNED_LT_REPEAT : FAILED"), UVM_LOW)
    end
    c_ALU_UNSIGNED_LT_REPEAT: cover property (sva_alu_unsigned_lt_repeat);

    // ALU Operation 12: XOR (Repeat)
    assert property (sva_alu_xor_repeat) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_XOR_REPEAT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_XOR_REPEAT : FAILED"), UVM_LOW)
    end
    c_ALU_XOR_REPEAT: cover property (sva_alu_xor_repeat);

    // ALU Operation 13: Signed Arithmetic Shift Right
    assert property (sva_alu_arith_shift_right) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_ARITH_SHIFT_RIGHT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_ARITH_SHIFT_RIGHT : FAILED"), UVM_LOW)
    end
    c_ALU_ARITH_SHIFT_RIGHT: cover property (sva_alu_arith_shift_right);

    // ALU Operation 14: OR (Repeat)
    assert property (sva_alu_or_repeat) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_OR_REPEAT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_OR_REPEAT : FAILED"), UVM_LOW)
    end
    c_ALU_OR_REPEAT: cover property (sva_alu_or_repeat);

    // ALU Operation 15: AND (Repeat)
    assert property (sva_alu_and_repeat) begin
        `uvm_info("sva", $sformatf("Test Case: ALU_AND_REPEAT : PASSED"), UVM_LOW)
    end else begin
        `uvm_info("sva", $sformatf("Test Case: ALU_AND_REPEAT : FAILED"), UVM_LOW)
    end
    c_ALU_AND_REPEAT: cover property (sva_alu_and_repeat);

endmodule

`endif
