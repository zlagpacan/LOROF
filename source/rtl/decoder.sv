/*
    Filename: decoder.sv
    Author: zlagpacan
    Description: RTL for Decoder
    Spec: LOROF/spec/design/decoder.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module decoder (

    // input info
    input logic                             uncompressed,
    input logic [31:0]                      instr32,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   pred_info_chunk0,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   pred_info_chunk1,

    // FU select
    output logic is_alu_reg,
    output logic is_alu_imm,
    output logic is_bru,
    output logic is_mdu,
    output logic is_ldu,
    output logic is_stamou,
    output logic is_sys,
    output logic is_illegal_instr,

    // op
    output logic [4:0]  op5,
    
    // A operand
    output logic [4:0]  A_AR,
    output logic        A_is_zero,
    output logic        is_ret_ra,

    // B operand
    output logic [4:0]  B_AR,
    output logic        B_is_zero,

    // dest operand
    output logic        is_reg_write,
    output logic [4:0]  dest_AR,
    output logic        dest_is_zero,
    output logic        is_link_ra,

    // imm
    output logic [19:0] imm20,

    // ordering
    output logic is_acquire,
    output logic is_release,

    // faults
    output logic instr_yield,
    output logic non_branch_notif,
    output logic fault_after_chunk0,
    output logic fault_after_chunk1,
    output logic fault_unrecoverable
);

    // stamou can fit into op5 if invert AMO ops
        // also need acquire release bits

    // ----------------------------------------------------------------
    // Signals:

    // instr components:
    logic [1:0]     instr_opcode_lsbs;

    // uncompressed instr components
    logic [4:0]     uncinstr_opcode_msbs;
    logic [2:0]     uncinstr_funct3;
    logic [6:0]     uncinstr_funct7;
    logic [4:0]     uncinstr_funct5;
    logic [4:0]     uncinstr_rs1;
    logic [4:0]     uncinstr_rs2;
    logic [4:0]     uncinstr_rd;
    logic           uncinstr_aq;
    logic           uncinstr_rl;
    logic [3:0]     uncinstr_fm;
    logic [11:0]    uncinstr_csr;
    logic [4:0]     uncinstr_uimm;
    
    // compressed instr components
    logic [2:0]     cinstr_funct3;
    logic [4:0]     cinstr_rlow;
    logic [4:0]     cinstr_rhigh;
    logic [1:0]     cinstr_funct2_low;
    logic [1:0]     cinstr_funct2_high;
    logic           cinstr_funct1;

    // uncompressed helper signals
    logic unc_funct3_not_0b010;
    logic unc_funct7_is_0b0000000;
    logic unc_funct7_is_0b0100000;
    logic unc_funct7_not_0b0x00000;
    logic unc_funct7_not_0b0000001;
    logic unc_fm_not_0bx000;

    // compressed helper signals
    logic [4:0]     cA_AR;
    logic [4:0]     cB_AR;
    logic [4:0]     cdest_AR;

    // ----------------------------------------------------------------
    // Helper Logic: 

    assign instr_opcode_lsbs = instr32[1:0];

    assign uncinstr_opcode_msbs = instr32[6:2];
    assign uncinstr_funct3 = instr32[14:12];
    assign uncinstr_funct7 = instr32[31:25];
    assign uncinstr_funct5 = instr32[31:27];
    assign uncinstr_rs1 = instr32[19:15];
    assign uncinstr_rs2 = instr32[24:20];
    assign uncinstr_rd = instr32[11:7];
    assign uncinstr_aq = instr32[26];
    assign uncinstr_rl = instr32[25];
    assign uncinstr_fm = instr32[31:28];
    assign uncinstr_csr = instr32[31:20];
    assign uncinstr_uimm = instr32[19:15];

    assign cinstr_funct3 = instr32[15:13];
    assign cinstr_rlow = instr32[6:2];
    assign cinstr_rhigh = instr32[11:7];
    assign cinstr_funct2_low = instr32[6:5];
    assign cinstr_funct2_high = instr32[11:10];
    assign cinstr_funct1 = instr32[12];
    
    assign unc_funct3_not_0b010 = instr_funct3 != 3'b010;
    assign unc_funct7_is_0bx0xxxxx = ~instr_funct7[5];
    assign unc_funct7_is_0bx1xxxxx = instr_funct7[5];
    assign unc_funct7_not_0b0x00000 = {instr_funct7[6], instr_funct7[4:0]} != 6'b000000;
    assign unc_funct7_not_0b0000001 = instr_func7 != 7'b0000001;
    assign unc_fm_not_0bx000 = instr_fm[2:0] != 3'b000;
    
    // ----------------------------------------------------------------
    // Main Case:

    always_comb begin
        case (instr_opcode_lsbs)

            2'b00: // compressed 00
            begin

            end

            2'b01: // compressed 01
            begin

            end
            
            2'b10: // compressed 10
            begin

            end
            
            2'b11: // uncompressed
            begin
                case (uncinstr_opcode_msbs) 

                    5'b01101:
                    begin
                        // LUI:
                        
                    end
                endcase
            end

        endcase
    end

    // opcode_lsbs: 2'b11
        // opcode_msbs: 5'b01101
            // LUI
        // opcode_msbs: 5'b00101
            // AUIPC
        // opcode_msbs: 5'b11011
            // JAL
        // opcode_msbs: 5'b11001
            // JALR
        // opcode_msbs: 5'b11000
            // Branch
            // funct3: 3'b000
                // BEQ
            // funct3: 3'b001
                // BNE
            // funct3: 3'b100
                // BLT
            // funct3: 3'b101
                // BGE
            // funct3: 3'b110
                // BLTU
            // funct3: 3'b111
                // BGEU
        // opcode_msbs: 5'b00000
            // Load
            // funct3: 3'b000
                // LB
            // funct3: 3'b001
                // LH
            // funct3: 3'b010
                // LW
            // funct3: 3'b100
                // LBU
            // funct3: 3'b101
                // LHU
        // opcode_msbs: 5'b01000
            // Store
            // funct3: 3'b000
                // SB
            // funct3: 3'b001
                // SH
            // funct3: 3'b010
                // SW
        // opcode_msbs: 5'b00100
            // ALU Reg-Imm
            // funct3: 3'b000
                // ADDI
            // funct3: 3'b001
                // funct7: 7'b0000000
                    // SLLI
            // funct3: 3'b010
                // SLTI
            // funct3: 3'b011
                // SLTIU
            // funct3: 3'b100
                // XORI
            // funct3: 3'b101
                // funct7: 7'b0000000
                    // SRLI
                // funct7: 7'b0100000
                    // SRAI
            // funct3: 3'b110
                // ORI
            // funct3: 3'b111
                // ANDI
        // opcode_msbs: 5'b01100
            // funct3: 3'b000
                // funct7: 7'b0000000
                    // ADD
                // funct7: 7'b0100000
                    // SUB
            // funct3: 3'b001
                // funct7: 7'b0000000
                    // SLL
            // funct3: 3'b010
                // funct7: 7'b0000000
                    // SLT
            // funct3: 3'b011
                // funct7: 7'b0000000
                    // SLTU
            // funct3: 3'b100
                // funct7: 7'b0000000
                    // XOR
            // funct3: 3'b101
                // funct7: 7'b0000000
                    // SRL
                // funct7: 7'b0100000
                    // SRA
            // funct3: 3'b110
                // funct7: 7'b0000000
                    // OR
            // funct3: 3'b111
                // funct7: 7'b0000000
                    // AND
        // opcode_msbs: 5'b00011
            // funct3: 3'b000
                // fm: 4'b0000
                    // FENCE
                // fm: 4'b1000
                    // FENCE.TSO
            // funct3: 3'b001
                // FENCE.I
        // opcode_msbs: 5'b11100
            // funct3: 3'b000
                // funct7: 7'b0000000
                    // uimm: 5'b00000
                        // ECALL
                    // uimm: 5'b00001
                        // EBREAK
                // funct7: 7'b0001000
                    // uimm: 5'b00010
                        // SRET
                    // uimm: 5'b00101
                        // WFI
                // funct7: 7'b0001001
                    // SFENCE.VMA
                // funct7: 7'b0011000
                    // uimm: 5'b00010
                        // MRET
            // funct3: 3'b001
                // CSRRW
            // funct3: 3'b010
                // CSRRS
            // funct3: 3'b011
                // CSRRC
            // funct3: 3'b101
                // CSRRWI
            // funct3: 3'b110
                // CSRRSI
            // funct3: 3'b111
                // CSRRCI
        // opcode_msbs: 5'b01100
            // funct3: 3'b000
                // funct7: 7'b0000001
                    // MUL
            // funct3: 3'b001
                // funct7: 7'b0000001
                    // MULH
            // funct3: 3'b010
                // funct7: 7'b0000001
                    // MULHSU
            // funct3: 3'b011
                // funct7: 7'b0000001
                    // MULHU
            // funct3: 3'b100
                // funct7: 7'b0000001
                    // DIV
            // funct3: 3'b101
                // funct7: 7'b0000001
                    // DIVU
            // funct3: 3'b110
                // funct7: 7'b0000001
                    // REM
            // funct3: 3'b111
                // funct7: 7'b0000001
                    // REMU
        // opcode_msbs: 5'b01011
            // funct3: 3'b010
                // funct5: 5'b00010
                    // LR.W
                // funct5: 5'b00011
                    // SC.W
                // funct5: 5'b00001
                    // AMOSWAP.W
                // funct5: 5'b00000
                    // AMOADD.W
                // funct5: 5'b00100
                    // AMOXOR.W
                // funct5: 5'b01100
                    // AMOAND.W
                // funct5: 5'b01000
                    // AMOOR.W
                // funct5: 5'b10000
                    // AMOMIN.W
                // funct5: 5'b10100
                    // AMOMAX.W
                // funct5: 5'b11000
                    // AMOMINU.W
                // funct5: 5'b11100
                    // AMOMAXU.W
    // opcode_lsbs: 2'b00
        // cfunct3: 3'b000
            // C.ADDI4SPN
        // cfunct3: 3'b010
            // C.LW
        // cfunct3: 3'b110
            // C.SW
    // opcode_lsbs: 2'b01
        // cfunct3: 3'b000
            // C.NOP, C.ADDI
        // cfunct3: 3'b001
            // C.JAL
        // cfunct3: 3'b010
            // C.LI
        // cfunct3: 3'b011
            // crhigh: 5'b00010 
                // C.ADDI16SP
            // crhigh: else
                // C.LUI
        // cfunct3: 3'b100
            // cfunct2_high: 2'b00
                // C.SRLI
            // cfunct2_high: 2'b01
                // C.SRAI
            // cfunct2_high: 2'b10
                // C.ANDI
            // cfunct2_high: 2'b11
                // cfunct1: 1'b0
                    // cfunct2_low: 2'b00
                        // C.SUB
                    // cfunct2_low: 2'b01
                        // C.XOR
                    // cfunct2_low: 2'b10
                        // C.OR
                    // cfunct2_low: 2'b11
                        // C.AND
        // cfunct3: 3'b101
            // C.J
        // cfunct3: 3'b110
            // C.BEQZ
        // cfunct3: 3'b111
            // C.BNEZ
    // opcode_lsbs: 2'b10
        // cfunct3: 3'b000
            // C.SLLI
        // cfunct3: 3'b010
            // C.LWSP
        // cfunct3: 3'b100
            // funct1: 1'b0
                // crlow: 5'b00000
                    // C.MV
                // crlow: else
                    // C.JR
            // funct1: 1'b1
                // crlow: 5'b00000
                    // crhigh: 5'b00000
                        // C.EBREAK
                    // crhigh: else
                        // C.JALR
                // crlow: else
                    // C.ADD
        // cfunct3: 3'b110
            // C.SWSP



endmodule