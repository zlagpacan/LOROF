/*
    Filename: instrp.vh
    Author: zlagpacan
    Description: Package Header File for Instruction Types
*/

`ifndef INSTRP_VH
`define INSTRP_VH

package instrp;

    // ----------------------------------------------------------------
    // instr decoding:

    // opcode5
    parameter logic [4:0] O5_LUI    = 5'b01101;
    parameter logic [4:0] O5_AUIPC  = 5'b00101;
    parameter logic [4:0] O5_JAL    = 5'b11011;
    parameter logic [4:0] O5_JALR   = 5'b11001;
    parameter logic [4:0] O5_BEQ    = 5'b11000;
    parameter logic [4:0] O5_L      = 5'b00000;
    parameter logic [4:0] O5_S      = 5'b01000;
    parameter logic [4:0] O5_I      = 5'b00100;
    parameter logic [4:0] O5_IW     = 5'b00110;
    parameter logic [4:0] O5_R_M    = 5'b01100;
    parameter logic [4:0] O5_R_M_W  = 5'b01110;
    parameter logic [4:0] O5_FENCE  = 5'b00011;
    parameter logic [4:0] O5_SYS    = 5'b11100;
    parameter logic [4:0] O5_A      = 5'b01011;
    parameter logic [4:0] O5_FL     = 5'b00001;
    parameter logic [4:0] O5_FS     = 5'b01001;
    parameter logic [4:0] O5_FMADD  = 5'b10000;
    parameter logic [4:0] O5_FMSUB  = 5'b10001;
    parameter logic [4:0] O5_FNMSUB = 5'b10010;
    parameter logic [4:0] O5_FNMADD = 5'b10011;
    parameter logic [4:0] O5_FOP    = 5'b10100;

    // ----------------------------------------------------------------
    // Custom op encoding:

    // generic op
        // follow max op size
    typedef logic [3:0] generic_op_t;

    // alu op
    typedef logic [3:0] alu_op_t;
    // funct3 following:
    parameter alu_op_t ALU_ADD      = 4'b0000;
    parameter alu_op_t ALU_SLL      = 4'b0001;
    parameter alu_op_t ALU_SLT      = 4'b0010;
    parameter alu_op_t ALU_SLTU     = 4'b0011;
    parameter alu_op_t ALU_XOR      = 4'b0100;
    parameter alu_op_t ALU_SRL      = 4'b0101;
    parameter alu_op_t ALU_OR       = 4'b0110;
    parameter alu_op_t ALU_AND      = 4'b0111;
    parameter alu_op_t ALU_SUB      = 4'b1000;
    parameter alu_op_t ALU_SRA      = 4'b1101;
    // non-funct3 following:
    parameter alu_op_t ALU_ADDW     = 4'b1001;
    parameter alu_op_t ALU_SUBW     = 4'b1010;
    parameter alu_op_t ALU_SLLW     = 4'b1011;
    parameter alu_op_t ALU_SRLW     = 4'b1100;
    parameter alu_op_t ALU_SRAW     = 4'b1110;

    // mdu op
    typedef logic [3:0] mdu_op_t;
    parameter mdu_op_t MDU_MUL      = 4'b0000;
    parameter mdu_op_t MDU_MULH     = 4'b0001;
    parameter mdu_op_t MDU_MULHSU   = 4'b0010;
    parameter mdu_op_t MDU_MULHU    = 4'b0011;
    parameter mdu_op_t MDU_DIV      = 4'b0100;
    parameter mdu_op_t MDU_DIVU     = 4'b0101;
    parameter mdu_op_t MDU_REM      = 4'b0110;
    parameter mdu_op_t MDU_REMU     = 4'b0111;
    parameter mdu_op_t MDU_MULW     = 4'b1000;
    parameter mdu_op_t MDU_DIVW     = 4'b1100;
    parameter mdu_op_t MDU_DIVUW    = 4'b1101;
    parameter mdu_op_t MDU_REMW     = 4'b1110;
    parameter mdu_op_t MDU_REMUW    = 4'b1111;

    // bru op
    typedef logic [3:0] bru_op_t;
    parameter bru_op_t BRU_JALR     = 4'b0000;
    parameter bru_op_t BRU_C_JALR   = 4'b0001;
    parameter bru_op_t BRU_JAL      = 4'b0010;
    // C.JAL -> not in RV64GC
    parameter bru_op_t BRU_C_J      = 4'b0100;
    parameter bru_op_t BRU_C_JR     = 4'b0101;
    parameter bru_op_t BRU_LUI      = 4'b0110;
    parameter bru_op_t BRU_AUIPC    = 4'b0111;
    parameter bru_op_t BRU_BEQ      = 4'b1000;
    parameter bru_op_t BRU_BNE      = 4'b1001;
    parameter bru_op_t BRU_C_BEQZ   = 4'b1010;
    parameter bru_op_t BRU_C_BNEZ   = 4'b1011;
    parameter bru_op_t BRU_BLT      = 4'b1100;
    parameter bru_op_t BRU_BGE      = 4'b1101;
    parameter bru_op_t BRU_BLTU     = 4'b1110;
    parameter bru_op_t BRU_BGEU     = 4'b1111;

    // ldu op
        // + access width modifier
    typedef logic ldu_op_t;
    parameter logic [1:0] LDU_U     = 2'b00; // unsigned (zero-extend)
    parameter logic [1:0] LDU_S     = 2'b01; // signed (sign-extend)
    parameter logic [1:0] LDU_N     = 2'b10; // NaN-boxed (one-extend)
        // upper bits: from mem? mem bit : ldu_op[1] | ldu_op[0] & msb

    // st op
        // only access width modifier

    // amo op
        // + access width modifier
    typedef logic [3:0] amo_op_t;
    parameter amo_op_t AMO_LR       = 4'b0010;
    parameter amo_op_t AMO_SC       = 4'b0011;
    parameter amo_op_t AMO_SWAP     = 4'b0111;
    parameter amo_op_t AMO_ADD      = 4'b0000;
    parameter amo_op_t AMO_XOR      = 4'b0100;
    parameter amo_op_t AMO_AND      = 4'b1100;
    parameter amo_op_t AMO_OR       = 4'b1000;
    parameter amo_op_t AMO_MIN      = 4'b1001;
    parameter amo_op_t AMO_MAX      = 4'b1101;
    parameter amo_op_t AMO_MINU     = 4'b0001;
    parameter amo_op_t AMO_MAXU     = 4'b0101;

    // access width
    typedef logic [1:0] aw_t;
    parameter aw_t AW_B = 2'b00;
    parameter aw_t AW_H = 2'b01;
    parameter aw_t AW_W = 2'b10;
    parameter aw_t AW_D = 2'b11;

    // fence op
    typedef logic [1:0] fence_op_t;
    parameter fence_op_t FENCE      = 2'b00;
    parameter fence_op_t FENCE_I    = 2'b01;
    parameter fence_op_t SFENCE_VMA = 2'b10;

    // sysu op
    typedef logic [2:0] sysu_op_t;
    parameter sysu_op_t SYSU_MISC   = 3'b000;
    parameter sysu_op_t SYSU_CSRRW  = 3'b001;
    parameter sysu_op_t SYSU_CSRRS  = 3'b010;
    parameter sysu_op_t SYSU_CSRRC  = 3'b011;
    parameter sysu_op_t SYSU_CSRRWI = 3'b101;
    parameter sysu_op_t SYSU_CSRRSI = 3'b110;
    parameter sysu_op_t SYSU_CSRRCI = 3'b111;

    // fpu op
        // use fpnew
        // encode w/ op_i + op_mod_i + rnd_mode_i

endpackage

`endif // INSTRP_VH