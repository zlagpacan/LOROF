`include "alu_pkg.svh"
import alu_pkg::*;

module alu (
    input  logic    clk,
    input  logic    n_rst,
    input  data_t   a,
    input  data_t   b,
    input  opcode_t opcode,
    output data_t   out,
    output logic    negative,
    output logic    overflow,
    output logic    zero
);
    // --- ALU Package -- //
    import alu_pkg::*;

    // --- Logic --- //
    data_t result, nxt_result;

    // --- Flip-Flop --- //
    always_ff @(posedge clk, negedge n_rst) begin
        if (~n_rst) begin
            result <= '0;
        end else begin
            result <= nxt_result;
        end
    end

    // --- Comb Logic --- //
    always_comb begin
        case(opcode)
            ALU_ADD : nxt_result = a +  b;
            ALU_SUB : nxt_result = a -  b;
            ALU_AND : nxt_result = a &  b;
            ALU_XOR : nxt_result = a ^  b;
            ALU_SLL : nxt_result = a << b;
            ALU_OR  : nxt_result = a |  b;
            default : nxt_result = '0;
        endcase
    end

    // --- Assign Ouput --- //
    assign out      = result;
    assign zero     = (result == '0);
    assign negative = (result[DATA_W-1] == 1'b1);

endmodule