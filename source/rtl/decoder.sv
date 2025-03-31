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
    output logic is_store,
    output logic is_amo,
    output logic is_fence,
    output logic is_sys,
    output logic is_illegal_instr,

    // op
    output logic [3:0]  op,
    output logic        is_reg_write,
    
    // A operand
    output logic [4:0]  A_AR,
    output logic        A_unneeded,
    output logic        A_is_zero,
    output logic        A_is_ret_ra,

    // B operand
    output logic [4:0]  B_AR,
    output logic        B_unneeded,
    output logic        B_is_zero,

    // dest operand
    output logic [4:0]  dest_AR,
    output logic        dest_is_zero,
    output logic        dest_is_link_ra,

    // imm
    output logic [19:0] imm20,

    // pred info out
    output logic [BTB_PRED_INFO_WIDTH-1:0]  pred_info_out,
    output logic                            missing_pred,

    // ordering
    output logic flush_fetch,
    output logic stall_mem_read,
    output logic stall_mem_write,
    output logic wait_write_buffer,

    // faults
    output logic instr_yield,
    output logic non_branch_notif_chunk0,
    output logic non_branch_notif_chunk1,
    output logic restart_on_chunk0,
    output logic restart_after_chunk0,
    output logic restart_after_chunk1,
    output logic unrecoverable_fault
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
    logic use_pred_info;

    // uncompressed helper signals
    logic uncfunct7_is_0bx1xxxxx;
    logic uncfunct7_is_0bx0xxxxx;
    logic uncfunct7_not_0b0x00000;
    logic uncfunct7_is_0bxxxxxx1;
    logic uncfm_not_0bx000;
    logic uncimm_type;
    logic [3:0] uncamoop;

    // compressed helper signals
    logic [4:0]     cA_AR;
    logic [4:0]     cB_AR;
    logic [4:0]     cdest_AR;
    logic [19:0]    cimm20;

    // ----------------------------------------------------------------
    // Instr Resolution Logic:
        // uses some main case decode logic

    always_comb begin

        // check allegedly uncompressed but is compressed
        if (uncompressed & (instr_opcode_lsbs != 2'b11)) begin
            instr_yield = 1'b0;
            non_branch_notif_chunk0 = 1'b0;
            non_branch_notif_chunk1 = 1'b0;
            restart_on_chunk0 = 1'b0;
            restart_after_chunk0 = 1'b0;
            restart_after_chunk1 = 1'b0;
            unrecoverable_fault = 1'b1;
        end

        // otherwise, check correctly uncompressed
        else if (uncompressed) begin

            // check have pred on chunk 0
                // decided not to optim restart if simple branch NT on chunk 0 for unC
            if (pred_info_chunk0[7] | pred_info_chunk0[6]) begin
                instr_yield = 1'b0;
                non_branch_notif_chunk0 = 1'b1;
                non_branch_notif_chunk1 = 1'b0;
                restart_on_chunk0 = 1'b1;
                restart_after_chunk0 = 1'b0;
                restart_after_chunk1 = 1'b0;
                unrecoverable_fault = 1'b0;
            end

            // otherwise, check have pred on chunk 1
            else if (pred_info_chunk1[7] | pred_info_chunk1[6]) begin

                // check will use pred
                if (use_pred_info) begin
                    instr_yield = 1'b1;
                    non_branch_notif_chunk0 = 1'b0;
                    non_branch_notif_chunk1 = 1'b0;
                    restart_on_chunk0 = 1'b0;
                    restart_after_chunk0 = 1'b0;
                    restart_after_chunk1 = 1'b0;
                    unrecoverable_fault = 1'b0;
                end

                // otherwise, bad pred
                else begin
                    instr_yield = 1'b1;
                    non_branch_notif_chunk0 = 1'b0;
                    non_branch_notif_chunk1 = 1'b1;
                    restart_on_chunk0 = 1'b0;
                    restart_after_chunk0 = 1'b0;
                    restart_after_chunk1 = 1'b1;
                    unrecoverable_fault = 1'b0;
                end
            end

            // otherwise, no pred's, all good
            else begin
                instr_yield = 1'b1;
                non_branch_notif_chunk0 = 1'b0;
                non_branch_notif_chunk1 = 1'b0;
                restart_on_chunk0 = 1'b0;
                restart_after_chunk0 = 1'b0;
                restart_after_chunk1 = 1'b0;
                unrecoverable_fault = 1'b0;
            end
        end

        // otherwise, check allegedly compressed but is uncompressed
        else if (instr_opcode_lsbs == 2'b11) begin
            instr_yield = 1'b0;
            non_branch_notif_chunk0 = 1'b0;
            non_branch_notif_chunk1 = 1'b0;
            restart_on_chunk0 = 1'b0;
            restart_after_chunk0 = 1'b0;
            restart_after_chunk1 = 1'b0;
            unrecoverable_fault = 1'b1;
        end

        // otherwise, correctly compressed
        else begin

            // check have pred on chunk 0
            if (pred_info_chunk0[7] | pred_info_chunk0[6]) begin

                // check will use pred
                if (use_pred_info) begin
                    instr_yield = 1'b1;
                    non_branch_notif_chunk0 = 1'b0;
                    non_branch_notif_chunk1 = 1'b0;
                    restart_on_chunk0 = 1'b0;
                    restart_after_chunk0 = 1'b0;
                    restart_after_chunk1 = 1'b0;
                    unrecoverable_fault = 1'b0;
                end

                // otherwise, bad pred
                else begin
                    instr_yield = 1'b1;
                    non_branch_notif_chunk0 = 1'b1;
                    non_branch_notif_chunk1 = 1'b0;
                    restart_on_chunk0 = 1'b0;
                    restart_after_chunk0 = 1'b1;
                    restart_after_chunk1 = 1'b0;
                    unrecoverable_fault = 1'b0;
                end
            end

            // otherwise, no pred's, all good
            else begin
                instr_yield = 1'b1;
                non_branch_notif_chunk0 = 1'b0;
                non_branch_notif_chunk1 = 1'b0;
                restart_on_chunk0 = 1'b0;
                restart_after_chunk0 = 1'b0;
                restart_after_chunk1 = 1'b0;
                unrecoverable_fault = 1'b0;
            end
        end
    end

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

    // ----------------------------------------------------------------
    // Outside Main Case:

    assign A_AR = uncompressed ? uncinstr_rs1 : cA_AR;
    assign A_is_zero = (A_AR == 5'h0);
    assign A_is_ret_ra = (A_AR == 5'h1) | (A_AR == 5'h5);

    assign B_AR = uncompressed ? uncinstr_rs2 : cB_AR;
    assign B_is_zero = (B_AR == 5'h0);

    assign dest_AR = uncompressed ? uncinstr_rd : cdest_AR;
    assign dest_is_zero = (dest_AR == 5'h0);
    assign dest_is_link_ra = (dest_AR == 5'h1) | (dest_AR == 5'h5);

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

    assign pred_info_out = uncompressed ? pred_info_chunk1 : pred_info_chunk0;

    assign missing_pred = use_pred_info & ~(pred_info_out[7] | pred_info_out[6]);

    // ----------------------------------------------------------------
    // Main Case:

    always_comb begin

        // defaults:
        is_alu_reg = 1'b0;
        is_alu_imm = 1'b0;
        is_bru = 1'b0;
        is_mdu = 1'b0;
        is_ldu = 1'b0;
        is_store = 1'b0;
        is_amo = 1'b0;
        is_fence = 1'b0;
        is_sys = 1'b0;
        is_illegal_instr = 1'b0;

        op[3] = uncfunct7_is_0bx1xxxxx;
        op[2:0] = uncinstr_funct3;
        is_reg_write = 1'b0;

        A_unneeded = 1'b1;
        B_unneeded = 1'b1;

        flush_fetch = 1'b0;
        stall_mem_read = 1'b0;
        stall_mem_write = 1'b0;
        wait_write_buffer = 1'b0;

        use_pred_info = 1'b0;

        uncimm_type = 1'b0;

        cA_AR = cinstr_rhigh;
        cB_AR = cinstr_rlow;
        cdest_AR = cinstr_rhigh;
        cimm20 = {{15{instr32[12]}}, instr32[6:2]};

        case (instr_opcode_lsbs)

            2'b00: // compressed 00
            begin
                cB_AR = {2'b01, cinstr_rlow[2:0]};
                cdest_AR = {2'b01, cinstr_rlow[2:0]};

                case (cinstr_funct3)

                    3'b000:
                    begin
                        op = 4'b0000;
                        cA_AR = 5'h2;
                        cimm20 = {10'h0, instr32[10:7], instr32[12:11], instr32[5], instr32[6], 2'b00};

                        if ({cinstr_rhigh, cinstr_rlow} == '0) begin
                            is_illegal_instr = 1'b1;
                        end
                        else begin
                            // C.ADDI4SPN
                                // ADDI rd', sp/x2, uimm
                            is_alu_imm = 1'b1;
                            is_reg_write = 1'b1;
                        end
                    end

                    3'b010:
                    begin
                        // C.LW
                            // LW rd', uimm(rs1')
                        is_ldu = 1'b1;
                        op[2:0] = 3'b010;
                        is_reg_write = 1'b1;
                        cA_AR = {2'b01, cinstr_rhigh[2:0]};
                        cimm20 = {13'h0, instr32[5], instr32[12:10], instr32[6], 2'b00};
                    end

                    3'b110:
                    begin
                        // C.SW
                            // SW rs2', uimm(rs1')
                        is_store = 1'b1;
                        op[1:0] = 2'b10;
                        cA_AR = {2'b01, cinstr_rhigh[2:0]};
                        cB_AR = {2'b01, cinstr_rlow[2:0]};
                        cimm20 = {13'h0, instr32[5], instr32[12:10], instr32[6], 2'b00};
                    end

                    default:
                    begin
                        is_illegal_instr = 1'b1;
                    end
                endcase
            end

            2'b01: // compressed 01
            begin

                case (cinstr_funct3)
                
                    3'b000:
                    begin
                        // C.ADDI
                            // ADDI rd, rd, imm
                        is_alu_imm = 1'b1;
                        op = 4'b0000;
                        is_reg_write = 1'b1;
                        cA_AR = cinstr_rhigh;
                        cdest_AR = cinstr_rhigh;
                        cimm20 = {{15{instr32[12]}}, instr32[6:2]};
                    end

                    3'b001:
                    begin
                        // C.JAL
                            // JAL ra/x1, imm
                        is_bru = 1'b1;
                        op = 4'b0011;
                        is_reg_write = 1'b1;
                        use_pred_info = 1'b1;
                        cdest_AR = 5'h1;
                        cimm20 = {{9{instr32[12]}}, instr32[8], instr32[10:9], instr32[6], instr32[7], instr32[2], instr32[11], instr32[5:3], instr32[12]};
                    end

                    3'b010:
                    begin
                        // C.LI
                            // ADDI rd, x0, imm
                        is_alu_imm = 1'b1;
                        op = 4'b0000;
                        is_reg_write = 1'b1;
                        cA_AR = 5'h0;
                        cdest_AR = cinstr_rhigh;
                        cimm20 = {{15{instr32[12]}}, instr32[6:2]};
                    end

                    3'b011:
                    begin
                        cA_AR = cinstr_rhigh;
                        cdest_AR = cinstr_rhigh;
                        is_reg_write = 1'b1;

                        if (cinstr_rhigh == 5'h2) begin
                            // C.ADDI16SP
                                // ADDI sp/x2, sp/x2, imm
                            is_alu_imm = 1'b1;
                            op = 4'b0000;
                            cimm20 = {{11{instr32[12]}}, instr32[4:3], instr32[5], instr32[2], instr32[6], 4'h0};
                        end
                        else begin
                            // C.LUI
                                // LUI rd, imm
                            is_bru = 1'b1;
                            op = 4'b0110;
                            cimm20 = {{3{instr32[12]}}, instr32[6:2], {12{instr32[12]}}};
                        end
                    end

                    3'b100:
                    begin
                        is_reg_write = 1'b1;
                        cA_AR = {2'b01, cinstr_rhigh[2:0]};     // rs1'
                        cB_AR = {2'b01, cinstr_rlow[2:0]};      // rs2'
                        cdest_AR = {2'b01, cinstr_rhigh[2:0]};  // rd'
                        
                        case (cinstr_funct2_high)

                            2'b00:
                            begin
                                // C.SRLI
                                    // SRLI rd', rd', uimm
                                is_alu_imm = 1'b1;
                                op = 4'b0101;
                                cimm20 = {14'h0, instr32[12], instr32[6:2]};
                            end

                            2'b01:
                            begin
                                // C.SRAI
                                    // SRAI rd', rd', uimm
                                is_alu_imm = 1'b1;
                                op = 4'b1101;
                                cimm20 = {14'h0, instr32[12], instr32[6:2]};
                            end

                            2'b10:
                            begin
                                // C.ANDI
                                    // ANDI rd', rd', imm
                                is_alu_imm = 1'b1;
                                op[2:0] = 3'b111;
                                cimm20 = {{15{instr32[12]}}, instr32[6:2]};
                            end

                            2'b11:
                            begin
                                is_alu_reg = 1'b1;

                                case (cinstr_funct2_low)

                                    2'b00:
                                    begin
                                        // C.SUB
                                            // SUB rd', rd', rs2'
                                        op = 4'b1000;
                                    end

                                    2'b01:
                                    begin
                                        // C.XOR
                                            // XOR rd', rd', rs2'
                                        op[2:0] = 3'b100;
                                    end

                                    2'b10:
                                    begin
                                        // C.OR
                                            // OR rd', rd', rs2'
                                        op[2:0] = 3'b110;
                                    end

                                    2'b11:
                                    begin
                                        // C.AND
                                            // AND rd', rd', rs2'
                                        op[2:0] = 3'b111;
                                    end
                                endcase
                            end
                        endcase
                    end

                    3'b101:
                    begin
                        // C.J
                            // JAL x0, imm
                        is_bru = 1'b1;
                        op = 4'b0100;
                        use_pred_info = 1'b1;
                        cimm20 = {{9{instr32[12]}}, instr32[8], instr32[10:9], instr32[6], instr32[7], instr32[2], instr32[11], instr32[5:3], instr32[12]};
                    end

                    3'b110:
                    begin
                        // C.BEQZ
                            // BEQ rs1', x0, imm
                        is_bru = 1'b1;
                        op = 4'b1010;
                        use_pred_info = 1'b1;
                        A_unneeded = 1'b0;
                        cA_AR = {2'b01, cinstr_rhigh[2:0]};
                        cimm20 = {{12{instr32[12]}}, instr32[6:5], instr32[2], instr32[11:10], instr32[4:3], instr32[12]};
                    end

                    3'b111:
                    begin
                        // C.BNEZ
                            // BNE rs1', x0, imm
                        is_bru = 1'b1;
                        op = 4'b1011;
                        use_pred_info = 1'b1;
                        A_unneeded = 1'b0;
                        cA_AR = {2'b01, cinstr_rhigh[2:0]};
                        cimm20 = {{12{instr32[12]}}, instr32[6:5], instr32[2], instr32[11:10], instr32[4:3], instr32[12]};
                    end
                endcase
            end
            
            2'b10: // compressed 10
            begin

                case (cinstr_funct3)

                    3'b000:
                    begin
                        // C.SLLI
                            // SLLI rd, rd, uimm
                        is_alu_imm = 1'b1;
                        op[2:0] = 3'b001;
                        is_reg_write = 1'b1;
                        cA_AR = cinstr_rhigh;
                        cdest_AR = cinstr_rhigh;
                        cimm20 = {14'h0, instr32[12], instr32[6:2]};
                    end

                    3'b010:
                    begin
                        // C.LWSP
                            // LW rd, uimm(sp/x2)
                        is_ldu = 1'b1;
                        op[2:0] = 3'b010;
                        is_reg_write = 1'b1;
                        cA_AR = 5'h2;
                        cdest_AR = cinstr_rhigh;
                        cimm20 = {12'h0, instr32[3:2], instr32[12], instr32[6:4], 2'h0};
                    end

                    3'b100:
                    begin
                        if (~cinstr_funct1) begin
                            if (cinstr_rlow == 5'h0) begin
                                // C.JR
                                    // JALR x0, 0(rs1)
                                is_bru = 1'b1;
                                op = 4'b0101;
                                A_unneeded = 1'b0;
                                use_pred_info = 1'b1;
                                cA_AR = cinstr_rhigh;
                            end
                            else begin
                                // C.MV
                                    // ADD rd, x0, rs2
                                is_alu_reg = 1'b1;
                                op = 4'b0000;
                                is_reg_write = 1'b1;
                                cA_AR = 5'h0;
                                cB_AR = cinstr_rlow;
                                cdest_AR = cinstr_rhigh;
                            end
                        end
                        else begin
                            if (cinstr_rhigh == 5'h0 & cinstr_rlow == 5'h0) begin
                                // C.EBREAK
                                    // EBREAK
                                is_sys = 1'b1;
                                op[2:0] = 3'b000;
                                flush_fetch = 1'b1;
                                cimm20 = {8'b00000000, 7'b0000000, 5'b00001};
                            end
                            else if (cinstr_rlow == 5'h0) begin
                                // C.JALR
                                    // JALR ra/x1, 0(rs1)
                                is_bru = 1'b1;
                                op = 4'b0001;
                                is_reg_write = 1'b1;
                                A_unneeded = 1'b0;
                                use_pred_info = 1'b1;
                                cA_AR = cinstr_rhigh;
                                cdest_AR = 5'h1;
                            end
                            else begin
                                // C.ADD
                                    // ADD rd, rd, rs2
                                is_alu_reg = 1'b1;
                                op = 4'b0000;
                                is_reg_write = 1'b1;
                                cA_AR = cinstr_rhigh;
                                cB_AR = cinstr_rlow;
                                cdest_AR = cinstr_rhigh;
                            end
                        end
                    end

                    3'b110:
                    begin
                        // C.SWSP
                            // SW rs2, uimm(sp/x2)
                        is_store = 1'b1;
                        op[1:0] = 2'b10;
                        cA_AR = 5'h2;
                        cB_AR = cinstr_rlow;
                        cimm20 = {12'h0, instr32[8:7], instr32[12:9], 2'h0};
                    end

                    default:
                    begin
                        is_illegal_instr = 1'b1;
                    end
                endcase
            end
            
            2'b11: // uncompressed
            begin

                case (uncinstr_opcode_msbs) 

                    5'b01101:
                    begin
                        // LUI:
                        is_bru = 1'b1;
                        op = 4'b0110;
                        is_reg_write = 1'b1;
                    end

                    5'b00101:
                    begin
                        // AUIPC:
                        is_bru = 1'b1;
                        op = 4'b0111;
                        is_reg_write = 1'b1;
                    end

                    5'b11011:
                    begin
                        // JAL:
                        is_bru = 1'b1;
                        op = 4'b0010;
                        is_reg_write = 1'b1;
                        use_pred_info = 1'b1;
                    end

                    5'b11001:
                    begin
                        if (uncinstr_funct3 == 3'b000) begin
                            // JALR:
                            is_bru = 1'b1;
                            op = 4'b0000;
                            is_reg_write = 1'b1;
                            A_unneeded = 1'b0;
                            use_pred_info = 1'b1;
                        end
                        else begin
                            is_illegal_instr = 1'b1;
                        end
                    end

                    5'b11000:
                    begin
                        // Branch:
                        op[3] = 1'b1;
                        op[2:0] = uncinstr_funct3;
                        A_unneeded = 1'b0;
                        B_unneeded = 1'b0;
                        use_pred_info = 1'b1;
                        uncimm_type = 1'b1;

                        case (uncinstr_funct3)

                            3'b000, 3'b001, 3'b100, 3'b101, 3'b110, 3'b111:
                            begin
                                // BEQ, BNE, BLT, BGE, BLTU, BGEU
                                is_bru = 1'b1;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b00000:
                    begin
                        // Load
                        is_ldu = 1'b0;
                        op[2:0] = uncinstr_funct3;

                        case (uncinstr_funct3)

                            3'b000, 3'b001, 3'b010, 3'b100, 3'b101:
                            begin
                                // LB, LH, LW, LBU, LHU
                                is_ldu = 1'b1;
                                is_reg_write = 1'b1;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b01000:
                    begin
                        // Store
                        op[2:0] = uncinstr_funct3;
                        uncimm_type = 1'b1;

                        case (uncinstr_funct3)

                            3'b000, 3'b001, 3'b010:
                            begin
                                // SB, SH, SW
                                is_store = 1'b1;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b00100:
                    begin
                        // ALU Reg-Imm
                        op[3] = uncfunct7_is_0bx1xxxxx;
                        op[2:0] = uncinstr_funct3;

                        case (uncinstr_funct3)

                            3'b000:
                            begin
                                // ADDI
                                is_alu_imm = 1'b1;
                                is_reg_write = 1'b1;
                            end

                            3'b001:
                            begin
                                if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                    is_illegal_instr = 1'b1;
                                end
                                else begin
                                    // SLLI
                                    is_alu_imm = 1'b1;
                                    is_reg_write = 1'b1;
                                end
                            end

                            3'b010:
                            begin
                                // SLTI
                                is_alu_imm = 1'b1;
                                is_reg_write = 1'b1;
                            end

                            3'b011:
                            begin
                                // SLTIU
                                is_alu_imm = 1'b1;
                                is_reg_write = 1'b1;
                            end

                            3'b100:
                            begin
                                // XORI
                                is_alu_imm = 1'b1;
                                is_reg_write = 1'b1;
                            end

                            3'b101:
                            begin
                                if (uncfunct7_not_0b0x00000) begin
                                    is_illegal_instr = 1'b1;
                                end 
                                else if (uncfunct7_is_0bx0xxxxx) begin
                                    // SRLI
                                    is_alu_imm = 1'b1;
                                    is_reg_write = 1'b1; 
                                end
                                else begin
                                    // SRAI
                                    is_alu_imm = 1'b1;
                                    is_reg_write = 1'b1;
                                end
                            end

                            3'b110:
                            begin
                                // ORI
                                is_alu_imm = 1'b1;
                                is_reg_write = 1'b1;
                            end

                            3'b111:
                            begin
                                // ANDI
                                is_alu_imm = 1'b1;
                                is_reg_write = 1'b1;
                            end
                        endcase
                    end

                    5'b01100:
                    begin
                        // ALU Reg-Reg + M-Ext
                        op[3] = uncfunct7_is_0bx1xxxxx;
                        op[2:0] = uncinstr_funct3;

                        if (uncinstr_funct7 == 7'b0000001) begin
                            // M-Ext
                                // MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU
                            is_mdu = 1'b1;
                            is_reg_write = 1'b1;
                        end
                        else begin
                            // ALU Reg-Reg

                            case (uncinstr_funct3)

                                3'b000:
                                begin
                                    if (uncfunct7_not_0b0x00000) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else if (uncfunct7_is_0bx0xxxxx) begin
                                        // ADD
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                    else begin
                                        // SUB
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end

                                3'b001:
                                begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // SLL
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end

                                3'b010:
                                begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // SLT
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end

                                3'b011:
                                begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // SLTU
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end

                                3'b100:
                                begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // XOR
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end

                                3'b101:
                                begin
                                    if (uncfunct7_not_0b0x00000) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else if (uncfunct7_is_0bx0xxxxx) begin
                                        // SRL
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                    else begin
                                        // SRA
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end

                                3'b110:
                                begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // OR
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end

                                3'b111:
                                begin
                                    if (uncfunct7_not_0b0x00000 | uncfunct7_is_0bx1xxxxx) begin
                                        is_illegal_instr = 1'b1;
                                    end
                                    else begin
                                        // AND
                                        is_alu_reg = 1'b1;
                                        is_reg_write = 1'b1;
                                    end
                                end
                            endcase
                        end
                    end

                    5'b00011:
                    begin
                        // FENCE's
                        op[2:0] = uncinstr_funct3;
                        
                        case (uncinstr_funct3) 

                            3'b000:
                            begin
                                if (uncfm_not_0bx000) begin
                                    is_illegal_instr = 1'b1;
                                end
                                else begin
                                    // FENCE, FENCE.TSO
                                    is_fence = 1'b1;

                                    // don't differentiate I vs. R, O vs. W

                                    // read after: stall mem read
                                        // I or R in succ set
                                    if (uncinstr_succ_set[3] | uncinstr_succ_set[1]) begin
                                        stall_mem_read = 1'b1;
                                    end

                                    // write before: wait write buffer
                                        // O or W in pred set
                                    if (uncinstr_pred_set[2] | uncinstr_pred_set[0]) begin
                                        wait_write_buffer = 1'b1;
                                    end
                                end
                            end

                            3'b001:
                            begin
                                // FENCE.I
                                    // make sure writes propagate to icache when eventually does reads
                                    // op will tell stamofu to perform icache flush when committed
                                is_fence = 1'b1;
                                flush_fetch = 1'b1;
                                wait_write_buffer = 1'b1;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b11100:
                    begin
                        // SYS + SFENCE.VMA

                        case (uncinstr_funct3)
                        
                            3'b000:
                            begin

                                case (uncinstr_funct7)

                                    7'b0000000:
                                    begin
                                        if (uncinstr_rs2 == 5'b00000) begin
                                            // ECALL
                                            is_sys = 1'b1;
                                            op[2:0] = uncinstr_funct3;
                                            flush_fetch = 1'b1;
                                        end
                                        else if (uncinstr_rs2 == 5'b00001) begin
                                            // EBREAK
                                            is_sys = 1'b1;
                                            op[2:0] = uncinstr_funct3;
                                            flush_fetch = 1'b1;
                                        end
                                        else begin
                                            is_illegal_instr = 1'b1;
                                        end
                                    end

                                    7'b0001000:
                                    begin
                                        if (uncinstr_rs2 == 5'b00010) begin
                                            // SRET
                                            is_sys = 1'b1;
                                            op[2:0] = uncinstr_funct3;
                                            flush_fetch = 1'b1;
                                        end
                                        else if (uncinstr_rs2 == 5'b00101) begin
                                            // WFI
                                                // flush fetch to be resumed after interrupt
                                                // sys_pipeline takes care of WFI stall state
                                            is_sys = 1'b1;
                                            op[2:0] = uncinstr_funct3;
                                            flush_fetch = 1'b1;
                                        end
                                        else begin
                                            is_illegal_instr = 1'b1;
                                        end
                                    end

                                    7'b0001001:
                                    begin
                                        // SFENCE.VMA
                                            // don't have to flush out instructions
                                                // FENCE.I will be used if page table update is in executable memory
                                            // do need to make sure no new data mem ops try to get a dTLB translation
                                        is_fence = 1'b1;
                                        op[1:0] = 2'b10;
                                        stall_mem_read = 1'b1;
                                        stall_mem_write = 1'b1;
                                    end

                                    7'b0011000:
                                    begin
                                        if (uncinstr_rs2 == 5'b00010) begin
                                            // MRET
                                            is_sys = 1'b1;
                                            op[2:0] = uncinstr_funct3;
                                            flush_fetch = 1'b1;
                                        end
                                        else begin
                                            is_illegal_instr = 1'b1;
                                        end
                                    end

                                    default:
                                    begin
                                        is_illegal_instr = 1'b1;
                                    end
                                endcase
                            end

                            3'b001, 3'b010, 3'b011, 3'b101, 3'b110, 3'b111:
                            begin
                                // CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI
                                is_sys = 1'b1;
                                op[2:0] = uncinstr_funct3;
                                is_reg_write = 1'b1;
                            end

                            default:
                            begin
                                is_illegal_instr = 1'b1;
                            end
                        endcase
                    end

                    5'b01011:
                    begin
                        // AMO
                        op = uncamoop;
                        
                        if (uncinstr_funct3 != 3'b010) begin
                            is_illegal_instr = 1'b1;
                        end
                        else begin
                            
                            case (uncinstr_funct5)

                                5'b00010:
                                begin
                                    // LR.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b00011:
                                begin
                                    // SC.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b00001:
                                begin
                                    // AMOSWAP.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b00000:
                                begin
                                    // AMOADD.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b00100:
                                begin
                                    // AMOXOR.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b01100:
                                begin
                                    // AMOAND.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b01000:
                                begin
                                    // AMOOR.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b10000:
                                begin
                                    // AMOMIN.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b10100:
                                begin
                                    // AMOMAX.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b11000:
                                begin
                                    // AMOMINU.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                5'b11100:
                                begin
                                    // AMOMAXU.W
                                    is_amo = 1'b1;
                                    is_reg_write = 1'b1;
                                    stall_mem_read = uncinstr_aq;
                                    wait_write_buffer = uncinstr_rl;
                                end

                                default:
                                begin
                                    is_illegal_instr = 1'b1;
                                end
                            endcase
                        end
                    end

                    default:
                    begin
                        is_illegal_instr = 1'b1;
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
                    // uimm: 5'b00000
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