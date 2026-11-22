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
    logic [3:0] uncamoop;

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

        A_unneeded = 1'b1;
        B_unneeded = 1'b1;

        mem_aq = 1'b0;
        io_aq = 1'b0;
        mem_rl = 1'b0;
        io_rl = 1'b0;

        uncimm_type = 1'b0;

        uncA_ar6 = {1'b0, uncinstr_rs1};
        uncB_ar6 = {1'b0, uncinstr_rs2};
        uncdest_ar6 = {1'b0, uncinstr_rd};

        cA_ar6 = {1'b0, cinstr_rhigh};
        cB_ar6 = {1'b0, cinstr_rlow};
        cdest_ar6 = {1'b0, cinstr_rhigh};
        cimm20 = {{15{instr32[12]}}, instr32[6:2]};

        case (instr_opcode_lsbs)

            2'b00: // compressed 00
            begin
                cB_AR = {2'b01, cinstr_rlow[2:0]};
                cdest_AR = {2'b01, cinstr_rlow[2:0]};

                case (cinstr_funct3)

                    3'b000: begin
                        op = instrp::ALU_ADD;
                        cA_AR = 5'h2; // sp
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

                    3'b001: begin

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



        endcase
    end

endmodule