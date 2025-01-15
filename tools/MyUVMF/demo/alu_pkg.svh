`ifndef ALU_PKG_SVH
`define ALU_PKG_SVH

package alu_pkg;

    // --- Params --- //
    parameter DATA_W   = 32;
    parameter OPCODE_W = 4;

    // --- 
    typedef logic [DATA_W-1:0] data_t;
    
    typedef enum logic [OPCODE_W-1:0] {
        ALU_SLL     = 4'b0000,
        ALU_SRL     = 4'b0001,
        ALU_SRA     = 4'b0010,
        ALU_ADD     = 4'b0011,
        ALU_SUB     = 4'b0100,
        ALU_AND     = 4'b0101,
        ALU_OR      = 4'b0110,
        ALU_XOR     = 4'b0111,
        ALU_SLT     = 4'b1010,
        ALU_SLTU    = 4'b1011
    } opcode_t;

endpackage

`endif