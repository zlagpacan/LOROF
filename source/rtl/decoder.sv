/*
    Filename: decoder.sv
    Author: zlagpacan
    Description: RTL for Decoder
    Spec: LOROF/spec/design/decoder.md
*/

// TODO: update for RV64IMAFDC
// TODO: update for floating point
    // fpnew input coding
    // tell if instr includes freg
        // not strictly is_fpu as fp loads and stores have freg's
// TODO: decode if want checkpoint

// further decoding

`include "corep.vh"
`include "instrp.vh"

module decoder (

    // environment info
    input corep::exec_mode_t    env_exec_mode,
    input logic                 env_trap_sfence,
    input logic                 env_trap_wfi,
    input logic                 env_trap_sret,
    input logic                 env_menvconfig_FIOM,
    input logic                 env_senvconfig_FIOM,

    // instr info
    input corep::fetch4B_t  fetch4B,
    input logic             btb_hit,
    input logic             redirect_taken,
    input logic             mid_instr_redirect,
    input corep::mdp_t      mdp,

    // FU select
    output logic is_alu_reg,
    output logic is_alu_imm,
    output logic is_bru,
    output logic is_mdu,
    output logic is_fpu,
    output logic is_ldu,
    output logic is_stamofu,
    output logic is_sysu,
    output logic is_illegal_instr,

    // op
    output logic [3:0]  op,
    output logic        dest_write,
    output logic        has_freg,
    output logic        has_imm,
    output logic        wfr,
    
    // A operand
    output corep::ar6_t A_ar6,
    output logic        A_unneeded,
    output logic        A_is_zero,
    output logic        A_is_ret_ra,

    // B operand
    output corep::ar6_t B_ar6,
    output logic        B_unneeded,
    output logic        B_is_zero,

    // C operand
    output corep::ar5_t C_ar5,

    // dest operand
    output corep::ar6_t dest_ar6,
    output logic        dest_is_zero,
    output logic        dest_is_link_ra,

    // imm
    output logic [19:0] imm20,

    // ordering
    output logic wait_for_restart,
    output logic amo_is_double,
    output logic mem_aq,
    output logic io_aq,
    output logic mem_rl,
    output logic io_rl,

    // yielding
    output logic        instr_yield,
    output logic        restart_valid,
    output logic [1:0]  restart_pc38_offset,
    output logic        unrecoverable_fault // not sure if will use
);

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
    logic [4:0]     uncinstr_rs3;
    logic [4:0]     uncinstr_rd;
    logic           uncinstr_aq;
    logic           uncinstr_rl;
    logic [3:0]     uncinstr_fm;
    logic [3:0]     uncinstr_pred_set;
    logic [3:0]     uncinstr_succ_set;
    logic [11:0]    uncinstr_csr;
    
    // compressed instr components
    logic [2:0]     cinstr_funct3;
    logic [4:0]     cinstr_rlow;
    logic [4:0]     cinstr_rhigh;
    logic [1:0]     cinstr_funct2_low;
    logic [1:0]     cinstr_funct2_high;
    logic           cinstr_funct1;

    // helper signals
    logic instr_can_redirect;

    // uncompressed helper signals
    logic uncfunct7_is_0bx1xxxxx;
    logic uncfunct7_is_0bx0xxxxx;
    logic uncfunct7_not_0b0x00000;
    logic uncfunct7_is_0bxxxxxx1;
    logic uncfm_not_0bx000;
    logic uncimm_type;

    corep::ar6_t    uncA_ar6;
    corep::ar6_t    uncB_ar6;
    corep::ar6_t    uncdest_ar6;

    // compressed helper signals
    corep::ar6_t    cA_ar6;
    corep::ar6_t    cB_ar6;
    corep::ar6_t    cdest_ar6;
    logic [19:0]    cimm20;

    // ----------------------------------------------------------------
    // Instr Resolution Logic:
        // uses some main case decode logic

    always_comb begin

        // uncompressed
        if (uncompressed) begin

            // automatic restart if in middle of uncompressed
            if (mid_instr_redirect) begin
                instr_yield = 1'b0;
                restart_valid = 1'b1;
                restart_pc38_offset = 2'b00; // restart this instr
            end
            // check for unredirectable instr
            else if (redirect_taken & ~instr_can_redirect) begin
                instr_yield = 1'b1;
                restart_valid = 1'b1;
                restart_pc38_offset = 2'b10; // restart after this good uncompressed instr
            end
            else begin
                instr_yield = 1'b1;
                restart_valid = 1'b0;
                restart_pc38_offset = 2'b00;
            end
        end

        // otherwise, compressed
        else begin

            // check for unredirectable instr
            if (redirect_taken & ~instr_can_redirect) begin
                instr_yield = 1'b1;
                restart_valid = 1'b1;
                restart_pc38_offset = 2'b01; // restart after this good compressed instr
            end
            else begin
                instr_yield = 1'b1;
                restart_valid = 1'b0;
                restart_pc38_offset = 2'b00;
            end
        end
    end

    // ----------------------------------------------------------------
    // Helper Logic: 

    assign instr_opcode_lsbs = instr32[1:0];
    assign uncompressed = instr_opcode_lsbs == 2'b11;

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
    assign uncinstr_pred_set = instr32[27:24];
    assign uncinstr_succ_set = instr32[23:20];
    assign uncinstr_csr = instr32[31:20];

    assign cinstr_funct3 = instr32[15:13];
    assign cinstr_rlow = instr32[6:2];
    assign cinstr_rhigh = instr32[11:7];
    assign cinstr_funct2_low = instr32[6:5];
    assign cinstr_funct2_high = instr32[11:10];
    assign cinstr_funct1 = instr32[12];
    
    assign uncfunct7_is_0bx0xxxxx = ~uncinstr_funct7[5];
    assign uncfunct7_is_0bx1xxxxx = uncinstr_funct7[5];
    assign uncfunct7_not_0b0x00000 = {uncinstr_funct7[6], uncinstr_funct7[4:0]} != 6'b000000;
    assign uncfunct7_is_0bxxxxxx1 = uncinstr_funct7[0];
    assign uncfm_not_0bx000 = uncinstr_fm[2:0] != 3'b000;
    assign uncamoop[3] = uncinstr_funct5[3] ^ uncinstr_funct5[4];
    assign uncamoop[2] = uncinstr_funct5[2] | (~uncinstr_funct5[1] & uncinstr_funct5[0]);
    assign uncamoop[1] = uncinstr_funct5[1] | (~uncinstr_funct5[1] & uncinstr_funct5[0]);
    assign uncamoop[0] = uncinstr_funct5[0] | uncinstr_funct5[4];

    assign A_ar6 = uncompressed ? uncA_ar6 : cA_ar6;
    assign A_is_zero == (A_ar6 == 6'h00);
    assign A_is_ret_ra == (A_ar6 == 6'h01) | (A_AR == 6'h05);

    assign B_ar6 = uncompressed ? uncB_ar6 : cB_ar6;
    assign B_is_zero = (B_ar6 == 6'h00);

    assign dest_ar6 = uncompressed ? uncdest_ar6 : cdest_ar6;
    assign dest_is_zero = (dest_ar6 == 6'h00);
    assign dest_is_link_ra = (dest_ar6 == 6'h01) : (dest_ar6 == 6'h05);

    always_comb begin
        if (uncompressed & uncimm_type) begin
            // S-Type, B-Type Imm
            imm20 = {instr32[19:12], instr32[31], instr32[30:25], instr32[11:8], instr32[7]};
        end
        else if (uncompressed) begin
            // I-Type, U-Type, J-Type Imm
            imm20 = {instr32[19:12], instr32[31], instr32[30:25], instr32[24:21], instr32[20]};
        end
        else begin
            // Compressed Imm
            imm20 = cimm20;
        end
    end

    // ----------------------------------------------------------------
    // Main Case:

    always_comb begin

        // defaults:
        is_alu_reg = 1'b0;
        is_alu_imm = 1'b0;
        is_bru = 1'b0;
        is_mdu = 1'b0;
        is_fpu = 1'b0;
        is_ldu = 1'b0;
        is_store = 1'b0;
        is_amo = 1'b0;
        is_fence = 1'b0;
        is_sysu = 1'b0;
        is_illegal_instr = 1'b0;

        op[3] = uncfunct7_is_0bx1xxxxx;
        op[2:0] = uncinstr_funct3;
        dest_write = 1'b0;
        has_freg = 1'b1;

        A_unneeded = 1'b1;
        B_unneeded = 1'b1;

        wait_for_restart = 1'b0;
        amo_is_double = 1'b0;
        mem_aq = 1'b0;
        io_aq = 1'b0;
        mem_rl = 1'b0;
        io_rl = 1'b0;

        instr_can_redirect = 1'b0;

        uncimm_type = 1'b0;

        uncA_ar6 = {1'b0, uncinstr_rs1};
        uncB_ar6 = {1'b0, uncinstr_rs2};
        uncdest_ar6 = {1'b0, uncinstr_rd};

        cA_ar6 = {1'b0, cinstr_rhigh};
        cB_ar6 = {1'b0, cinstr_rlow};
        cdest_ar6 = {1'b0, cinstr_rhigh};
        cimm20 = {{15{instr32[12]}}, instr32[6:2]};

        case (instr_opcode_lsbs)

            2'b00: begin
                // compressed 00

                cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                cB_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};
                cdest_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};

                case (cinstr_funct3)

                    3'b000: begin
                        op = instrp::ALU_ADD;
                        cA_ar6 = {1'b0, 5'h02}; // sp
                        cdest_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};
                        cimm20 = {10'h0, instr32[10:7], instr32[12:11], instr32[5], instr32[6], 2'b00};

                        if ({cinstr_rhigh, cinstr_rlow} == '0) begin
                            is_illegal_instr = 1'b1;
                        end
                        else begin
                            // C.ADDI4SPN
                                // ADDI rd', sp/x2, uimm
                            is_alu_imm = 1'b1;
                            dest_write = 1'b1;
                        end
                    end

                    3'b001: begin
                        // C.FLD
                            // FLD frd', uimm(rs1')
                        is_ldu = 1'b1;
                        op = instrp::LDU_D_U;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cdest_ar6 = {1'b1, 2'b01, cinstr_rlow[2:0]};
                        cimm20 = {12'h000, instr32[6:5], instr32[12:10], 3'b000};
                    end

                    3'b010: begin
                        // C.LW
                            // LW rd', uimm(rs1')
                        is_ldu = 1'b1;
                        op = instrp::LDU_W_S;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cdest_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};
                        cimm20 = {13'h0000, instr32[5], instr32[12:10], instr32[6], 2'b00};
                    end

                    3'b011: begin
                        // C.LD
                            // LD rd', uimm(rs1')
                        is_ldu = 1'b1;
                        op = instrp::LDU_D_U;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cdest_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};
                        cimm20 = {12'h000, instr32[6:5], instr32[12:10], 3'b000};
                    end

                    3'b101: begin
                        // C.FSD
                            // FSD frs2', uimm(rs1')
                        is_store = 1'b1;
                        op[1:0] = instrp::ST_D;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cB_ar6 = {1'b1, 2'b01, cinstr_rlow[2:0]};
                        cimm20 = {12'h000, instr32[6:5], instr32[12:10], 3'b000};
                    end

                    3'b110: begin
                        // C.SW
                            // SW rs2', uimm(rs1')
                        is_store = 1'b1;
                        op[1:0] = instrp::ST_W;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cB_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};
                        cimm20 = {13'h0, instr32[5], instr32[12:10], instr32[6], 2'b00};
                    end

                    3'b111: begin
                        // C.SD
                            // SD rs2', uimm(rs1')
                        is_store = 1'b1;
                        op[1:0] = instrp::ST_D;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cB_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};
                        cimm20 = {12'h000, instr32[6:5], instr32[12:10], 3'b000};
                    end

                    default: begin
                        is_illegal_instr = 1'b1;
                    end
                endcase
            end

            2'b01: begin
                // compressed 01

                case (cinstr_funct3)
                
                    3'b000: begin
                        // C.ADDI
                            // ADDI rd, rd, imm
                        is_alu_imm = 1'b1;
                        op = instrp::ALU_ADD;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, cinstr_rhigh};
                        cdest_ar6 = {1'b0, cinstr_rhigh};
                        cimm20 = {{15{instr32[12]}}, instr32[6:2]};
                    end

                    3'b001: begin
                        // C.ADDIW
                            // ADDIW rd, rd, imm
                        is_bru = 1'b1;
                        op = instrp::ALU_ADDW;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, cinstr_rhigh};
                        cdest_ar6 = {1'b0, cinstr_rhigh};
                        cimm20 = {{15{instr32[12]}}, instr32[6:2]};
                    end

                    3'b010: begin
                        // C.LI
                            // ADDI rd, x0, imm
                        is_alu_imm = 1'b1;
                        op = instrp::ALU_ADD;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, 5'h00}; // x0
                        cdest_ar6 = {1'b0, cinstr_rhigh};
                        cimm20 = {{15{instr32[12]}}, instr32[6:2]};
                    end

                    3'b011: begin
                        cA_ar6 = {1'b0, cinstr_rhigh};
                        cdest_ar6 = {1'b0, cinstr_rhigh};
                        dest_write = 1'b1;

                        if (cinstr_rhigh == 5'h2) begin
                            // C.ADDI16SP
                                // ADDI sp/x2, sp/x2, imm
                            is_alu_imm = 1'b1;
                            op = instrp::ALU_ADD;
                            cimm20 = {{11{instr32[12]}}, instr32[4:3], instr32[5], instr32[2], instr32[6], 4'h0};
                        end
                        else begin
                            // C.LUI
                                // LUI rd, imm
                            is_bru = 1'b1;
                            op = instrp::BRU_LUI;
                            cimm20 = {{3{instr32[12]}}, instr32[6:2], {12{instr32[12]}}};
                        end
                    end

                    3'b100: begin
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};      // rs1'
                        cB_ar6 = {1'b0, 2'b01, cinstr_rlow[2:0]};       // rs2'
                        cdest_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};   // rd'
                        dest_write = 1'b1;
                        
                        case (cinstr_funct2_high)

                            2'b00: begin
                                // C.SRLI
                                    // SRLI rd', rd', uimm
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_SRL;
                                cimm20 = {14'h0, instr32[12], instr32[6:2]};
                            end

                            2'b01: begin
                                // C.SRAI
                                    // SRAI rd', rd', uimm
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_SRA;
                                cimm20 = {14'h0, instr32[12], instr32[6:2]};
                            end

                            2'b10: begin
                                // C.ANDI
                                    // ANDI rd', rd', imm
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_AND;
                                cimm20 = {{15{instr32[12]}}, instr32[6:2]};
                            end

                            2'b11: begin
                                is_alu_reg = 1'b1;

                                if (cinstr_funct1) begin

                                    case (cinstr_funct2_low)

                                        2'b00: begin
                                            // C.SUB
                                                // SUB rd', rd', rs2'
                                            op = instrp::ALU_SUB;
                                        end

                                        2'b01: begin
                                            // C.XOR
                                                // XOR rd', rd', rs2'
                                            op = instrp::ALU_XOR;
                                        end

                                        2'b10: begin
                                            // C.OR
                                                // OR rd', rd', rs2'
                                            op = instrp::ALU_OR;
                                        end

                                        2'b11: begin
                                            // C.AND
                                                // AND rd', rd', rs2'
                                            op = instrp::ALU_AND;
                                        end
                                    endcase

                                end else begin

                                    case (cinstr_funct2_low)

                                        2'b00: begin
                                            // C.SUBW
                                                // SUBW rd', rd', rs2'
                                            op = instrp::ALU_SUBW;
                                        end

                                        2'b01: begin
                                            // C.ADDW
                                                // ADDW rd', rd', rs2'
                                            op = instrp::ALU_ADDW;
                                        end

                                        default: begin
                                            // fine with default op
                                        end
                                    endcase
                                end
                            end
                        endcase
                    end

                    3'b101: begin
                        // C.J
                            // JAL x0, imm
                        is_bru = 1'b1;
                        op = instrp::BRU_C_J;
                        instr_can_redirect = 1'b1;
                        cimm20 = {{9{instr32[12]}}, instr32[8], instr32[10:9], instr32[6], instr32[7], instr32[2], instr32[11], instr32[5:3], instr32[12]};
                    end

                    3'b110: begin
                        // C.BEQZ
                            // BEQ rs1', x0, imm
                        is_bru = 1'b1;
                        op = instrp::BRU_C_BEQZ;
                        instr_can_redirect = 1'b1;
                        A_unneeded = 1'b0;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cimm20 = {{12{instr32[12]}}, instr32[6:5], instr32[2], instr32[11:10], instr32[4:3], instr32[12]};
                    end

                    3'b111:
                    begin
                        // C.BNEZ
                            // BNE rs1', x0, imm
                        is_bru = 1'b1;
                        op = instrp::BRU_C_BNEZ;
                        instr_can_redirect = 1'b1;
                        A_unneeded = 1'b0;
                        cA_ar6 = {1'b0, 2'b01, cinstr_rhigh[2:0]};
                        cimm20 = {{12{instr32[12]}}, instr32[6:5], instr32[2], instr32[11:10], instr32[4:3], instr32[12]};
                    end
                endcase
            end
            
            2'b10: begin
                // compressed 10

                case (cinstr_funct3)

                    3'b000: begin
                        // C.SLLI
                            // SLLI rd, rd, uimm
                        is_alu_imm = 1'b1;
                        op = instrp::ALU_SLL;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, cinstr_rhigh};
                        cdest_ar6 = {1'b0, cinstr_rhigh};
                        cimm20 = {14'h0, instr32[12], instr32[6:2]};
                    end

                    3'b001: begin
                        // C.FLDSP
                            // FLD frd, uimm(sp/x2)
                        is_ldu = 1'b1;
                        op = instrp::LDU_D_U;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, 5'h02}; // sp
                        cdest_ar6 = {1'b1, cinstr_rhigh};
                        cimm20 = {11'h000, instr32[4:2], instr32[12], instr32[6:5], 3'h0};
                    end

                    3'b010: begin
                        // C.LWSP
                            // LW rd, uimm(sp/x2)
                        is_ldu = 1'b1;
                        op = instrp::LDU_W_S;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, 5'h02}; // sp
                        cdest_ar6 = {1'b0, cinstr_rhigh};
                        cimm20 = {12'h000, instr32[3:2], instr32[12], instr32[6:4], 2'h0};
                    end

                    3'b011: begin
                        // C.LDSP
                            // LD rd, uimm(sp/x2)
                        is_ldu = 1'b1;
                        op = isntrp::LDU_D_U;
                        dest_write = 1'b1;
                        cA_ar6 = {1'b0, 5'h02}; // sp
                        cdest_ar6 = {1'b1, cinstr_rhigh};
                        cimm20 = {11'h000, instr32[4:2], instr32[12], instr32[6:5], 3'h0};
                    end

                    3'b100: begin
                        if (~cinstr_funct1) begin
                            if (cinstr_rlow == 5'h0) begin
                                // C.JR
                                    // JALR x0, 0(rs1)
                                is_bru = 1'b1;
                                op = instrp::BRU_C_JR;
                                A_unneeded = 1'b0;
                                instr_can_redirect = 1'b1;
                                cA_ar6 = {1'b0, cinstr_rhigh};
                            end
                            else begin
                                // C.MV
                                    // ADD rd, x0, rs2
                                is_alu_reg = 1'b1;
                                op = instrp::ALU_ADD;
                                dest_write = 1'b1;
                                cA_ar6 = {1'b0, 5'h00};
                                cB_ar6 = {1'b0, cinstr_rlow};
                                cdest_ar6 = {1'b0, cinstr_rhigh};
                            end
                        end
                        else begin
                            if (cinstr_rhigh == 5'h0 & cinstr_rlow == 5'h0) begin
                                // C.EBREAK
                                    // EBREAK
                                is_sysu = 1'b1;
                                op[2:0] = instrp::SYSU_MISC;
                                wait_for_restart = 1'b1;
                                cimm20 = {8'b00000000, 7'b0000000, 5'b00001};
                            end
                            else if (cinstr_rlow == 5'h0) begin
                                // C.JALR
                                    // JALR ra/x1, 0(rs1)
                                is_bru = 1'b1;
                                op = instrp::BRU_C_JALR;
                                dest_write = 1'b1;
                                A_unneeded = 1'b0;
                                instr_can_redirect = 1'b1;
                                cA_ar6 = {1'b0, cinstr_rhigh};
                                cdest_ar6 = {1'b0, 5'h01}; // ra
                            end
                            else begin
                                // C.ADD
                                    // ADD rd, rd, rs2
                                is_alu_reg = 1'b1;
                                op = instrp::ALU_ADD;
                                dest_write = 1'b1;
                                cA_ar6 = {1'b0, cinstr_rhigh};
                                cB_ar6 = {1'b0, cinstr_rlow};
                                cdest_ar6 = {1'b0, cinstr_rhigh};
                            end
                        end
                    end

                    3'b101: begin
                        // C.FSDSP
                            // FSD frs2, uimm(sp/x2)
                        is_store = 1'b1;
                        op[1:0] = instrp::ST_D;
                        cA_ar6 = {1'b0, 5'h02}; // sp
                        cB_ar6 = {1'b1, cinstr_rlow};
                        cimm20 = {11'h000, instr32[9:7], instr32[12:10], 3'h0};
                    end

                    3'b110: begin
                        // C.SWSP
                            // SW rs2, uimm(sp/x2)
                        is_store = 1'b1;
                        op[1:0] = instrp::ST_W;
                        cA_ar6 = {1'b0, 5'h02}; // sp
                        cB_ar6 = {1'b0, cinstr_rlow};
                        cimm20 = {12'h0, instr32[8:7], instr32[12:9], 2'h0};
                    end

                    3'b111: begin
                        // C.SDSP
                            // SD rs2, uimm(sp/x2)
                        is_store = 1'b1;
                        op[1:0] = instrp::ST_D;
                        cA_ar6 = {1'b0, 5'h02}; // sp
                        cB_ar6 = {1'b0, cinstr_rlow};
                        cimm20 = {11'h000, instr32[9:7], instr32[12:10], 3'h0};
                    end

                    default:
                    begin
                        is_illegal_instr = 1'b1;
                    end
                endcase
            end

            2'b11: begin
                // uncompressed 11

                case (uncinstr_opcode_msbs) 

                    5'b01101: begin
                        // LUI:
                        is_bru = 1'b1;
                        op = instrp::BRU_LUI;
                        dest_write = 1'b1;
                    end

                    5'b00101: begin
                        // AUIPC:
                        is_bru = 1'b1;
                        op = instrp::BRU_AUIPC;
                        dest_write = 1'b1;
                    end

                    5'b11011: begin
                        // JAL:
                        is_bru = 1'b1;
                        op = instrp::BRU_JAL;
                        dest_write = 1'b1;
                        instr_can_redirect = 1'b1;
                    end

                    5'b11001: begin
                        if (uncinstr_funct3 == 3'b000) begin
                            // JALR:
                            is_bru = 1'b1;
                            op = instrp::BRU_JALR;
                            dest_write = 1'b1;
                            A_unneeded = 1'b0;
                            instr_can_redirect = 1'b1;
                        end
                        else begin
                            is_illegal_instr = 1'b1;
                        end
                    end

                    5'b11000:
                    begin
                        // Branch:
                        A_unneeded = 1'b0;
                        B_unneeded = 1'b0;
                        instr_can_redirect = 1'b1;
                        uncimm_type = 1'b1;

                        case (uncinstr_funct3)

                            3'b000: begin
                                // BEQ
                                is_bru = 1'b1;
                                op = instrp::BRU_BEQ;
                            end

                            3'b001: begin
                                // BNE
                                is_bru = 1'b1;
                                op = instrp::BRU_BNE;
                            end

                            3'b100: begin
                                // BLT
                                is_bru = 1'b1;
                                op = instrp::BRU_BLT;
                            end

                            3'b101: begin
                                // BGE
                                is_bru = 1'b1;
                                op = instrp::BRU_BGE;
                            end

                            3'b110: begin
                                // BLTU
                                is_bru = 1'b1;
                                op = instrp::BRU_BLTU;
                            end

                            3'b111: begin
                                // BGEU
                                is_bru = 1'b1;
                                op = instrp::BRU_BGEU;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b00000: begin
                        // Load

                        case (uncinstr_funct3)

                            3'b000: begin
                                // LB 
                                is_ldu = 1'b1;
                                op = instrp::LDU_B_S;
                                dest_write = 1'b1;
                            end

                            3'b001: begin
                                // LH
                                is_ldu = 1'b1;
                                op = instrp::LDU_H_S;
                                dest_write = 1'b1;
                            end

                            3'b010: begin
                                // LW
                                is_ldu = 1'b1;
                                op = instrp::LDU_W_S;
                                dest_write = 1'b1;
                            end

                            3'b011: begin
                                // LD
                                is_ldu = 1'b1;
                                op = instrp::LDU_D_U;
                                dest_write = 1'b1;
                            end

                            3'b100: begin
                                // LBU
                                is_ldu = 1'b1;
                                op = instrp::LDU_B_U;
                                dest_write = 1'b1;
                            end

                            3'b101: begin
                                // LHU
                                is_ldu = 1'b1;
                                op = instrp::LDU_H_U;
                                dest_write = 1'b1;
                            end

                            3'b110: begin
                                // LWU
                                is_ldu = 1'b1;
                                op = instrp::LDU_W_U;
                                dest_write = 1'b1;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b01000: begin
                        // Store

                        uncimm_type = 1'b1;

                        case (uncinstr_funct3)

                            3'b000: begin
                                // SB
                                is_store = 1'b1;
                                op = instrp::ST_B;
                            end

                            3'b001: begin
                                // SH
                                is_store = 1'b1;
                                op = instrp::ST_H;
                            end

                            3'b010: begin
                                // SW
                                is_store = 1'b1;
                                op = instrp::ST_W;
                            end

                            3'b011: begin
                                // SD
                                is_store = 1'b1;
                                op = instrp::ST_D;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b00100: begin
                        // ALU Reg-Imm

                        case (uncinstr_funct3)

                            3'b000: begin
                                // ADDI
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_ADD;
                                dest_write = 1'b1;
                            end

                            3'b001: begin
                                if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                    is_illegal_instr = 1'b1;
                                end
                                else begin
                                    // SLLI
                                    is_alu_imm = 1'b1;
                                    op = instrp::ALU_SLL;
                                    dest_write = 1'b1;
                                end
                            end

                            3'b010: begin
                                // SLTI
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_SLT;
                                dest_write = 1'b1;
                            end

                            3'b011: begin
                                // SLTIU
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_SLTU;
                                dest_write = 1'b1;
                            end

                            3'b100: begin
                                // XORI
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_XOR;
                                dest_write = 1'b1;
                            end

                            3'b101: begin
                                if (uncfunct7_not_0b0x00000) begin
                                    is_illegal_instr = 1'b1;
                                end 
                                else if (uncfunct7_is_0bx0xxxxx) begin
                                    // SRLI
                                    is_alu_imm = 1'b1;
                                    op = instrp::ALU_SRL;
                                    dest_write = 1'b1; 
                                end
                                else begin
                                    // SRAI
                                    is_alu_imm = 1'b1;
                                    op = instrp::ALU_SRA;
                                    dest_write = 1'b1;
                                end
                            end

                            3'b110: begin
                                // ORI
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_OR;
                                dest_write = 1'b1;
                            end

                            3'b111: begin
                                // ANDI
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_AND;
                                dest_write = 1'b1;
                            end
                        endcase
                    end

                    5'b00110: begin
                        // ALU Reg-Imm W

                        case (uncinstr_funct3)

                            3'b000: begin
                                // ADDIW
                                is_alu_imm = 1'b1;
                                op = instrp::ALU_ADDW;
                                dest_write = 1'b1;
                            end

                            3'b001: begin
                                if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                    is_illegal_instr = 1'b1;
                                end
                                else begin
                                    // SLLIW
                                    is_alu_imm = 1'b1;
                                    op = instrp::ALU_SLLW;
                                    dest_write = 1'b1;
                                end
                            end

                            3'b101: begin
                                if (uncfunct7_not_0b0x00000) begin
                                    is_illegal_instr = 1'b1;
                                end 
                                else if (uncfunct7_is_0bx0xxxxx) begin
                                    // SRLIW
                                    is_alu_imm = 1'b1;
                                    op = instrp::ALU_SRLW;
                                    dest_write = 1'b1; 
                                end
                                else begin
                                    // SRAIW
                                    is_alu_imm = 1'b1;
                                    op = instrp::ALU_SRAW;
                                    dest_write = 1'b1;
                                end
                            end

                            default: begin
                                is_illegal_instr = 1'b1;
                            end

                        endcase
                    end

                    5'b01100: begin
                        // ALU Reg-Reg + M-Ext

                        if (uncinstr_funct7 == 7'b0000001) begin

                            case (uncinstr_funct3)

                                3'b000: begin
                                    // MUL
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_MUL;
                                    dest_write = 1'b1;
                                end

                                3'b001: begin
                                    // MULH
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_MULH;
                                    dest_write = 1'b1;
                                end

                                3'b010: begin
                                    // MULHSU
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_MULHSU;
                                    dest_write = 1'b1;
                                end

                                3'b011: begin
                                    // MULHU
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_MULHU;
                                    dest_write = 1'b1;
                                end

                                3'b100: begin
                                    // DIV
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_DIV;
                                    dest_write = 1'b1;
                                end

                                3'b101: begin
                                    // DIVU
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_DIVU;
                                    dest_write = 1'b1;
                                end

                                3'b110: begin
                                    // REM
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_REM;
                                    dest_write = 1'b1;
                                end

                                3'b111: begin
                                    // REMU
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_REMU;
                                    dest_write = 1'b1;
                                end

                            endcase
                        end
                        else begin
                            // ALU Reg-Reg

                            case (uncinstr_funct3)

                                3'b000: begin
                                    if (uncfunct7_not_0b0x00000) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else if (uncfunct7_is_0bx0xxxxx) begin
                                        // ADD
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_ADD;
                                        dest_write = 1'b1;
                                    end
                                    else begin
                                        // SUB
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SUB;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b001: begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // SLL
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SLL;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b010: begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // SLT
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SLT;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b011: begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // SLTU
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SLTU;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b100: begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // XOR
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_XOR;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b101: begin
                                    if (uncfunct7_not_0b0x00000) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else if (uncfunct7_is_0bx0xxxxx) begin
                                        // SRL
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SRL;
                                        dest_write = 1'b1;
                                    end
                                    else begin
                                        // SRA
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SRA;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b110: begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // OR
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_OR;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b111: begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // AND
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_AND;
                                        dest_write = 1'b1;
                                    end
                                end

                            endcase
                        end
                    end

                    5'b01110: begin
                        // ALU Reg-Reg W + M-Ext W
                        
                        if (uncinstr_funct7 == 7'b0000001) begin
                            // M-Ext W
                            
                            case (uncinstr_funct3)

                                3'b000: begin
                                    // MULW
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_MULW;
                                    dest_write = 1'b1;
                                end

                                3'b100: begin
                                    // DIVW
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_DIVW;
                                    dest_write = 1'b1;
                                end

                                3'b101: begin
                                    // DIVUW
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_DIVUW;
                                    dest_write = 1'b1;
                                end

                                3'b110: begin
                                    // REMW
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_REMW;
                                    dest_write = 1'b1;
                                end

                                3'b111: begin
                                    // REMUW
                                    is_mdu = 1'b1;
                                    op = instrp::MDU_REMUW;
                                    dest_write = 1'b1;
                                end

                                default: begin
                                    is_illegal_instr = 1'b1;
                                end

                            endcase
                        end

                        else begin
                            // ALU Reg-Reg W

                            case (uncinstr_funct3)

                                3'b000: begin
                                    if (uncfunct7_not_0b0x00000) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else if (uncfunct7_is_0bx0xxxxx) begin
                                        // ADDW
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_ADDW;
                                        dest_write = 1'b1;
                                    end
                                    else begin
                                        // SUBW
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SUBW;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b001: begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // SLLW
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SLLW;
                                        dest_write = 1'b1;
                                    end
                                end

                                3'b101: begin
                                    if (uncfunct7_not_0b0x00000) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else if (uncfunct7_is_0bx0xxxxx) begin
                                        // SRLW
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SRLW;
                                        dest_write = 1'b1;
                                    end
                                    else begin
                                        // SRAW
                                        is_alu_reg = 1'b1;
                                        op = instrp::ALU_SRAW;
                                        dest_write = 1'b1;
                                    end
                                end

                                default: begin
                                    is_illegal_instr = 1'b1;
                                end

                            endcase
                        end
                    end

                    5'b00011: begin
                        // FENCE's

                        // R in succ set
                        if (uncinstr_succ_set[1]) mem_aq = 1'b1;
                        // I in succ set
                        if (uncinstr_succ_set[3]) io_aq = 1'b1;
                        // FIOM
                        if (
                            uncinstr_succ_set[3]
                            & (
                                (env_exec_mode == S_MODE) & (env_menvconfig_FIOM)
                                | (env_exec_mode == U_MODE) & (env_menvconfig_FIOM | env_senvconfig_FIOM)
                            )        
                        ) mem_aq = 1'b1;

                        // W in pred set
                        if (uncinstr_pred_set[0]) mem_rl = 1'b1;
                        // O in pred set
                        if (uncinstr_pred_set[2]) io_rl = 1'b1;
                        
                        case (uncinstr_funct3) 

                            3'b000: begin
                                if (uncfm_not_0bx000) begin
                                    is_illegal_instr = 1'b1;
                                end
                                else begin
                                    // FENCE, FENCE.TSO
                                    is_fence = 1'b1;
                                    op[1:0] = instrp::FENCE;
                                end
                            end

                            3'b001: begin
                                // FENCE.I
                                    // make sure writes propagate to icache when eventually does reads
                                    // op will tell stamofu to perform icache flush when committed
                                is_fence = 1'b1;
                                op[1:0] = instrp::FENCE_I;
                                wait_for_restart = 1'b1;
                                mem_rl = 1'b1;
                                    // need local hart stores in front of the FENCE.I to be visible to this hart's icache
                                    // instruction stream after fence.i expects normal program order of stores, not global order
                            end

                            default: begin
                                is_illegal_instr = 1'b1;
                            end

                        endcase
                    end

                    5'b11100: begin
                        // sysu + SFENCE.VMA

                        case (uncinstr_funct3)
                        
                            3'b000: begin

                                case (uncinstr_funct7)

                                    7'b0000000: begin
                                        if (uncinstr_rs2 == 5'b00000) begin
                                            // ECALL
                                            is_sysu = 1'b1;
                                            op[2:0] = instrp::SYSU_MISC;
                                            wait_for_restart = 1'b1;
                                        end
                                        else if (uncinstr_rs2 == 5'b00001) begin
                                            // EBREAK
                                            is_sysu = 1'b1;
                                            op[2:0] = instrp::SYSU_MISC;
                                            wait_for_restart = 1'b1;
                                        end
                                        else begin
                                            is_illegal_instr = 1'b1;
                                        end
                                    end

                                    7'b0001000: begin
                                        if (uncinstr_rs2 == 5'b00010) begin
                                            // SRET
                                            if (
                                                env_exec_mode == U_MODE 
                                                | 
                                                (env_exec_mode == S_MODE & env_trap_sret)
                                            ) begin
                                                is_illegal_instr = 1'b1;
                                            end 
                                            else begin
                                                is_sysu = 1'b1;
                                                op[2:0] = instrp::SYSU_MISC;
                                                wait_for_restart = 1'b1; 
                                            end
                                        end
                                        else if (uncinstr_rs2 == 5'b00101) begin
                                            // WFI
                                            if (
                                                env_exec_mode == U_MODE
                                                |
                                                env_exec_mode == S_MODE & env_trap_wfi
                                            ) begin
                                                is_illegal_instr = 1'b1;
                                            end
                                            else begin
                                                // flush fetch to be resumed after interrupt
                                                // rob takes care of WFI stall state
                                                is_sysu = 1'b1;
                                                op[2:0] = instrp::SYSU_MISC;
                                                wait_for_restart = 1'b1;
                                            end
                                        end
                                        else begin
                                            is_illegal_instr = 1'b1;
                                        end
                                    end

                                    7'b0001001: begin
                                        // SFENCE.VMA
                                        if (
                                            env_exec_mode == U_MODE
                                            |
                                            env_exec_mode == S_MODE & env_trap_sfence
                                        ) begin
                                            is_illegal_instr = 1'b1;
                                        end
                                        else begin
                                            // don't have to flush out instructions
                                                // FENCE.I will be used if page table update is in executable memory
                                            // do need to make sure no new data mem ops try to get a dTLB translation
                                                // would need bunch of special case logic for functionality in LSQ
                                                    // loads could be stopped with regular acquire rules
                                                    // currently no mechanism to stop stores or AMO's from grabbing a translation
                                                // just do a restart 
                                            is_fence = 1'b1;
                                            op[1:0] = instrp::SFENCE_VMA;
                                            wait_for_restart = 1'b1;
                                        end
                                    end

                                    7'b0011000: begin
                                        if (uncinstr_rs2 == 5'b00010) begin
                                            // MRET
                                            if (env_exec_mode != M_MODE)
                                            begin
                                                is_illegal_instr = 1'b1;
                                            end
                                            else begin
                                                is_sysu = 1'b1;
                                                op[2:0] = instrp::SYSU_MISC;
                                                wait_for_restart = 1'b1;
                                            end
                                        end
                                        else begin
                                            is_illegal_instr = 1'b1;
                                        end
                                    end

                                    default: begin
                                        is_illegal_instr = 1'b1;
                                    end

                                endcase
                            end

                            3'b001: begin
                                is_sysu = 1'b1;
                                op[2:0] = instrp::SYSU_CSRRW;
                                dest_write = 1'b1;
                            end

                            3'b010: begin
                                is_sysu = 1'b1;
                                op[2:0] = instrp::SYSU_CSRRS;
                                dest_write = 1'b1;
                            end

                            3'b011: begin
                                is_sysu = 1'b1;
                                op[2:0] = instrp::SYSU_CSRRC;
                                dest_write = 1'b1;
                            end

                            3'b101: begin
                                is_sysu = 1'b1;
                                op[2:0] = instrp::SYSU_CSRRWI;
                                dest_write = 1'b1;
                            end

                            3'b110: begin
                                is_sysu = 1'b1;
                                op[2:0] = instrp::SYSU_CSRRSI;
                                dest_write = 1'b1;
                            end

                            3'b111: begin
                                is_sysu = 1'b1;
                                op[2:0] = instrp::SYSU_CSRRCI;
                                dest_write = 1'b1;
                            end

                            default: begin
                                is_illegal_instr = 1'b1;
                            end

                        endcase
                    end

                    5'b01011: begin
                        // AMO

                        amo_is_double = uncinstr_funct3[0];

                        // don't know io vs. mem, mark both aq's and rl's (can be relaxed after translation)
                        mem_aq = uncinstr_aq;
                        io_aq = uncinstr_aq;
                        mem_rl = uncinstr_rl;
                        io_rl = uncinstr_rl;
                        
                        if (uncinstr_funct3[2:1] != 2'b01) begin
                            is_illegal_instr = 1'b1;
                        end
                        else begin
                            
                            case (uncinstr_funct5)

                                5'b00010: begin
                                    // LR.W/D
                                    is_amo = 1'b1;
                                    op = instrp::AMO_LR;
                                    dest_write = 1'b1;
                                end

                                5'b00011: begin
                                    // SC.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_SC;
                                    dest_write = 1'b1;
                                end

                                5'b00001:
                                begin
                                    // AMOSWAP.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_SWAP;
                                    dest_write = 1'b1;
                                end

                                5'b00000:
                                begin
                                    // AMOADD.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_ADD;
                                    dest_write = 1'b1;
                                end

                                5'b00100:
                                begin
                                    // AMOXOR.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_XOR;
                                    dest_write = 1'b1;
                                end

                                5'b01100:
                                begin
                                    // AMOAND.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_AND;
                                    dest_write = 1'b1;
                                end

                                5'b01000:
                                begin
                                    // AMOOR.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_OR;
                                    dest_write = 1'b1;
                                end

                                5'b10000:
                                begin
                                    // AMOMIN.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_MIN;
                                    dest_write = 1'b1;
                                end

                                5'b10100:
                                begin
                                    // AMOMAX.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_MAX;
                                    dest_write = 1'b1;
                                end

                                5'b11000:
                                begin
                                    // AMOMINU.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_MINU;
                                    dest_write = 1'b1;
                                end

                                5'b11100:
                                begin
                                    // AMOMAXU.W
                                    is_amo = 1'b1;
                                    op = instrp::AMO_MAXU;
                                    dest_write = 1'b1;
                                end

                                default:
                                begin
                                    is_illegal_instr = 1'b1;
                                end

                            endcase
                        end
                    end

                    5'b00001: begin
                        // FP Load

                        uncdest_ar6.is_freg = 1'b1;

                        if (uncinstr_funct3[2:1] != 2'b01) begin
                            is_illegal_instr = 1'b1;
                        end
                        else if (uncinstr_funct3[0]) begin
                            // FLD
                            is_ldu = 1'b1;
                            op = instrp::LDU_W_N;
                            dest_write = 1'b1;
                            has_freg = 1'b1;
                        end
                        else begin
                            // FLW
                            is_ldu = 1'b1;
                            op = instrp::LDU_D_U;
                            dest_write = 1'b1;
                            has_freg = 1'b1;
                        end
                    end

                    5'b01001: begin
                        // FP Store

                        uncB_ar6.is_freg = 1'b1;

                        uncimm_type = 1'b1;

                        if (uncinstr_funct3[2:1] != 2'b01) begin
                            is_illegal_instr = 1'b1;
                        end
                        else if (uncinstr_funct3[0]) begin
                            // FSD
                            is_store = 1'b1;
                            op = instrp::ST_D;
                            has_freg = 1'b1;
                        end
                        else begin
                            // FSW
                            is_store = 1'b1;
                            op = instrp::ST_W;
                            has_freg = 1'b1;
                        end
                    end

                    5'b10000, 5'b10001, 5'b10010, 5'b10011: begin
                        // FMADD's

                        uncA_ar6.is_freg = 1'b1;
                        uncB_ar6.is_freg = 1'b1;
                        uncdest_ar6.is_freg = 1'b1;

                        if (~uncinstr_funct7[1]) begin
                            // FMADD.*, FMSUB.*, FNMSUB.*, FNMADD.*
                            is_fpu = 1'b1;
                            dest_write = 1'b1;
                            has_freg = 1'b1;
                        end
                        else begin
                            is_illegal_instr = 1'b1;
                        end
                    end

                    5'b10100: begin
                        // FP
                            // do specific op decoding in FPU (too much for here)
                            // bits will be in imm20 w/ uncimm_type = 1'b0

                        casez (uncinstr_funct7) 
                                
                            7'b000000?: begin
                                // FADD.*
                                is_fpu = 1'b1;
                                dest_write = 1'b1;
                                has_freg = 1'b1;

                                uncA_ar6.is_freg = 1'b1;
                                uncB_ar6.is_freg = 1'b1;
                                uncdest_ar6.is_freg = 1'b1;
                            end

                            7'b000010?: begin
                                // FSUB.*
                                is_fpu = 1'b1;
                                dest_write = 1'b1;
                                has_freg = 1'b1;

                                uncA_ar6.is_freg = 1'b1;
                                uncB_ar6.is_freg = 1'b1;
                                uncdest_ar6.is_freg = 1'b1;
                            end

                            7'b000100?: begin
                                // FMUL.*
                                is_fpu = 1'b1;
                                dest_write = 1'b1;
                                has_freg = 1'b1;

                                uncA_ar6.is_freg = 1'b1;
                                uncB_ar6.is_freg = 1'b1;
                                uncdest_ar6.is_freg = 1'b1;
                            end
                            7'b000110?: begin
                                // FDIV.*
                                is_fpu = 1'b1;
                                dest_write = 1'b1;
                                has_freg = 1'b1;

                                uncA_ar6.is_freg = 1'b1;
                                uncB_ar6.is_freg = 1'b1;
                                uncdest_ar6.is_freg = 1'b1;
                            end
                            7'b010110?: begin
                                // FSQRT.*

                                uncA_ar6.is_freg = 1'b1;
                                uncdest_ar6.is_freg = 1'b1;

                                if (uncinstr_rs2 == 5'h00) begin
                                    is_fpu = 1'b1;
                                    dest_write = 1'b1;
                                    has_freg = 1'b1;
                                end
                                else begin
                                    is_illegal_instr = 1'b1;
                                end
                            end

                            7'b001000?: begin
                                // FSGNJ*.*

                                uncA_ar6.is_freg = 1'b1;
                                uncB_ar6.is_freg = 1'b1;
                                uncdest_ar6.is_freg = 1'b1;

                                case (uncinstr_funct3)
                                    3'b000, 3'b001, 3'b010: begin
                                        is_fpu = 1'b1;
                                        dest_write = 1'b1;
                                        has_freg = 1'b1;
                                    end
                                    default: begin
                                        is_illegal_instr = 1'b1;
                                    end
                                endcase
                            end

                            7'b001010?: begin
                                // FMIN.*, FMAX.*

                                uncA_ar6.is_freg = 1'b1;
                                uncB_ar6.is_freg = 1'b1;
                                uncdest_ar6.is_freg = 1'b1;

                                case (uncinstr_funct3)
                                    3'b000, 3'b001: begin
                                        is_fpu = 1'b1;
                                        dest_write = 1'b1;
                                        has_freg = 1'b1;
                                    end
                                    default: begin
                                        is_illegal_instr = 1'b1;
                                    end
                                endcase
                            end

                            7'b110000?: begin
                                // FCVT.int.float

                                uncA_ar6.is_freg = 1'b1;
                                
                                case (uncinstr_rs2)
                                    5'b00000, 5'b00001, 5'b00010, 5'b00011: begin
                                        is_fpu = 1'b1;
                                        dest_write = 1'b1;
                                        has_freg = 1'b1;
                                    end
                                    default: begin
                                        is_illegal_instr = 1'b1;
                                    end
                                endcase
                            end

                            // bookmark

                            7'b111000?: begin

                            end

                        endcase
                    end

                    default:
                    begin
                        is_illegal_instr = 1'b1;
                    end

                endcase
            end
        endcase
    end

endmodule