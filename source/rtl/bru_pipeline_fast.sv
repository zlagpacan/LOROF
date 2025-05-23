/*
    Filename: bru_pipeline_fast.sv
    Author: zlagpacan
    Description: RTL for Branch Resolution Unit Pipeline
    Spec: LOROF/spec/design/bru_pipeline_fast.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pipeline_fast (

    // seq
    input logic CLK,
    input logic nRST,

    // BRU op issue from BRU IQ
    input logic                             issue_valid,
    input logic [3:0]                       issue_op,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   issue_pred_info,
    input logic                             issue_pred_lru,
    input logic                             issue_is_link_ra,
    input logic                             issue_is_ret_ra,
    input logic [31:0]                      issue_PC,
    input logic [31:0]                      issue_pred_PC,
    input logic [19:0]                      issue_imm20,
    input logic                             issue_A_unneeded_or_is_zero,
    input logic                             issue_A_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_bank,
    input logic                             issue_B_unneeded_or_is_zero,
    input logic                             issue_B_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_B_bank,
    input logic [LOG_PR_COUNT-1:0]          issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       issue_ROB_index,

    // output feedback to BRU IQ
    output logic                            issue_ready,

    // reg read info and data from PRF
    input logic                                     A_reg_read_ack,
    input logic                                     A_reg_read_port,
    input logic                                     B_reg_read_ack,
    input logic                                     B_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0]     reg_read_data_by_bank_by_port,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // writeback backpressure from PRF
    input logic                         WB_ready,

    // branch notification to ROB
    output logic                            branch_notif_valid,
    output logic [LOG_ROB_ENTRIES-1:0]      branch_notif_ROB_index,
    output logic                            branch_notif_is_mispredict,
    output logic                            branch_notif_is_taken,
    output logic                            branch_notif_use_upct,
    output logic [BTB_PRED_INFO_WIDTH-1:0]  branch_notif_updated_pred_info,
    output logic                            branch_notif_pred_lru,
    output logic [31:0]                     branch_notif_start_PC,
    output logic [31:0]                     branch_notif_target_PC,

    // branch notification backpressure from ROB
    input logic                             branch_notif_ready
);

    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_WB;
    logic stall_EX;
    logic stall_OC;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                               valid_OC;
    logic [3:0]                         op_OC;
    logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info_OC;
    logic                               pred_lru_OC;
    logic                               is_link_ra_OC;
    logic                               is_ret_ra_OC;
    logic [31:0]                        PC_OC;
    logic [31:0]                        pred_PC_OC;
    logic [19:0]                        imm20_OC;
    logic                               A_saved_OC;
    logic                               A_unneeded_or_is_zero_OC;
    logic                               A_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]      A_bank_OC;
    logic                               B_saved_OC;
    logic                               B_unneeded_or_is_zero_OC;
    logic                               B_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]      B_bank_OC;
    logic [LOG_PR_COUNT-1:0]            dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]         ROB_index_OC;

    logic [31:0] A_saved_data_OC;
    logic [31:0] B_saved_data_OC;

    logic launch_ready_OC;

    logic                               next_valid_EX;
    logic [3:0]                         next_op_EX;
    logic [BTB_PRED_INFO_WIDTH-1:0]     next_pred_info_EX;
    logic                               next_pred_lru_EX;
    logic                               next_is_link_ra_EX;
    logic                               next_is_ret_ra_EX;
    logic [31:0]                        next_PC_EX;
    logic [31:0]                        next_pred_PC_EX;
    logic [31:0]                        next_imm32_EX;
    logic [31:0]                        next_A_EX;
    logic [31:0]                        next_B_EX;
    logic [LOG_PR_COUNT-1:0]            next_dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]         next_ROB_index_EX;

    // ----------------------------------------------------------------
    // EX Stage Signals:

    logic                               valid_EX;
    logic [3:0]                         op_EX;
    logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info_EX;
    logic                               pred_lru_EX;
    logic                               is_link_ra_EX;
    logic                               is_ret_ra_EX;
    logic [31:0]                        PC_EX;
    logic [31:0]                        pred_PC_EX;
    logic [31:0]                        imm32_EX;
    logic [31:0]                        A_EX;
    logic [31:0]                        B_EX;
    logic [LOG_PR_COUNT-1:0]            dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]         ROB_index_EX;

    logic [31:0]    PC_plus_imm32_EX;
    logic [31:0]    PC_plus_2_EX;
    logic [31:0]    PC_plus_4_EX;
    logic [31:0]    A_plus_imm32_EX;
    logic           inner_A_lt_B_EX;
    logic           A_eq_B_EX;
    logic           A_eq_zero_EX;
    logic           A_lts_B_EX;
    logic           A_ltu_B_EX;

    logic                               next_WB_stage_valid;
    logic [3:0]                         next_WB_stage_op;
    logic [BTB_PRED_INFO_WIDTH-1:0]     next_WB_stage_pred_info;
    logic                               next_WB_stage_pred_lru;
    logic                               next_WB_stage_is_link_ra;
    logic                               next_WB_stage_is_ret_ra;
    logic                               next_WB_stage_is_taken;
    logic [31:0]                        next_WB_stage_start_PC;
    logic [31:0]                        next_WB_stage_pred_PC;
    logic [31:0]                        next_WB_stage_target_PC;
    logic [31:0]                        next_WB_stage_write_data;
    logic [LOG_PR_COUNT-1:0]            next_WB_stage_dest_PR;
    logic [LOG_ROB_ENTRIES-1:0]         next_WB_stage_ROB_index;

    // ----------------------------------------------------------------
    // EX2 Stage Signals:

    logic                               WB_stage_valid;
    logic [3:0]                         WB_stage_op;
    logic [BTB_PRED_INFO_WIDTH-1:0]     WB_stage_pred_info;
    logic                               WB_stage_pred_lru;
    logic                               WB_stage_is_link_ra;
    logic                               WB_stage_is_ret_ra;
    logic                               WB_stage_is_taken;
    logic [31:0]                        WB_stage_start_PC;
    logic [31:0]                        WB_stage_pred_PC;
    logic [31:0]                        WB_stage_target_PC;
    logic [31:0]                        WB_stage_write_data;
    logic [LOG_PR_COUNT-1:0]            WB_stage_dest_PR;
    logic [LOG_ROB_ENTRIES-1:0]         WB_stage_ROB_index;

    logic WB_stage_WB_acked;
    logic WB_stage_branch_notif_acked;

    logic                       WB_stage_start_neq_target_upper_PC;
    logic [UPPER_PC_WIDTH-1:0]  WB_stage_delta_start_target_upper_PC;
    logic                       WB_stage_small_delta_upper_PC;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    // ----------------------------------------------------------------
    // Control Logic: 

    // propagate stalls backwards
    assign stall_WB = (WB_valid & ~WB_ready) | (branch_notif_valid & ~branch_notif_ready);
    assign stall_EX = valid_EX & stall_WB;
    assign stall_OC = valid_OC & stall_EX;

    // ----------------------------------------------------------------
    // OC Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_OC <= 1'b0;
            op_OC <= 4'b0000;
            pred_info_OC <= 8'h0;
            pred_lru_OC <= 1'b0;
            is_link_ra_OC <= 1'b0;
            is_ret_ra_OC <= 1'b0;
            PC_OC <= 32'h0;
            pred_PC_OC <= 32'h0;
            imm20_OC <= 20'h0;
            A_saved_OC <= 1'b0;
            A_unneeded_or_is_zero_OC <= 1'b0;
            A_forward_OC <= 1'b0;
            A_bank_OC <= 2'h0;
            A_saved_data_OC <= 32'h0;
            B_saved_OC <= 1'b0;
            B_unneeded_or_is_zero_OC <= 1'b0;
            B_forward_OC <= 1'b0;
            B_bank_OC <= 2'h0;
            B_saved_data_OC <= 32'h0;
            dest_PR_OC <= 7'h0;
            ROB_index_OC <= 7'h0;
        end
        // stall OC stage when have valid op which can't move on: issue_ready == 1'b0
        else if (~issue_ready) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            pred_info_OC <= pred_info_OC;
            pred_lru_OC <= pred_lru_OC;
            is_link_ra_OC <= is_link_ra_OC;
            is_ret_ra_OC <= is_ret_ra_OC;
            PC_OC <= PC_OC;
            pred_PC_OC <= pred_PC_OC;
            imm20_OC <= imm20_OC;
            A_saved_OC <= A_saved_OC | A_forward_OC | A_reg_read_ack;
            A_unneeded_or_is_zero_OC <= A_unneeded_or_is_zero_OC;
            A_forward_OC <= 1'b0;
            A_bank_OC <= A_bank_OC;
            A_saved_data_OC <= next_A_EX;
            B_saved_OC <= B_saved_OC | B_forward_OC | B_reg_read_ack;
            B_unneeded_or_is_zero_OC <= B_unneeded_or_is_zero_OC;
            B_forward_OC <= 1'b0;
            B_bank_OC <= B_bank_OC;
            B_saved_data_OC <= next_B_EX;
            dest_PR_OC <= dest_PR_OC;
            ROB_index_OC <= ROB_index_OC;
        end
        // pass input issue to OC
        else begin
            valid_OC <= issue_valid;
            op_OC <= issue_op;
            pred_info_OC <= issue_pred_info;
            pred_lru_OC <= issue_pred_lru;
            is_link_ra_OC <= issue_is_link_ra;
            is_ret_ra_OC <= issue_is_ret_ra;
            PC_OC <= issue_PC;
            pred_PC_OC <= issue_pred_PC;
            imm20_OC <= issue_imm20;
            A_saved_OC <= 1'b0;
            A_unneeded_or_is_zero_OC <= issue_A_unneeded_or_is_zero;
            A_forward_OC <= issue_A_forward;
            A_bank_OC <= issue_A_bank;
            A_saved_data_OC <= next_A_EX;
            B_saved_OC <= 1'b0;
            B_unneeded_or_is_zero_OC <= issue_B_unneeded_or_is_zero;
            B_forward_OC <= issue_B_forward;
            B_bank_OC <= issue_B_bank;
            B_saved_data_OC <= next_B_EX;
            dest_PR_OC <= issue_dest_PR;
            ROB_index_OC <= issue_ROB_index;
        end
    end

    assign launch_ready_OC = 
        // no backpressure
        ~stall_OC
        &
        // A operand present
        (A_unneeded_or_is_zero_OC | A_saved_OC | A_forward_OC | A_reg_read_ack)
        &
        // B operand present
        (B_unneeded_or_is_zero_OC | B_saved_OC | B_forward_OC | B_reg_read_ack)
    ;
    assign issue_ready = ~valid_OC | launch_ready_OC;

    assign next_valid_EX = valid_OC & launch_ready_OC;
    assign next_op_EX = op_OC;
    assign next_pred_info_EX = pred_info_OC;
    assign next_pred_lru_EX = pred_lru_OC;
    assign next_is_link_ra_EX = is_link_ra_OC;
    assign next_is_ret_ra_EX = is_ret_ra_OC;
    assign next_PC_EX = PC_OC;
    assign next_pred_PC_EX = pred_PC_OC;
    assign next_dest_PR_EX = dest_PR_OC;
    assign next_ROB_index_EX = ROB_index_OC;

    // A and B operand collection
    always_comb begin

        // collect A value to save OR pass to EX1
        if (A_unneeded_or_is_zero_OC) begin
            next_A_EX = 32'h0;
        end
        else if (A_saved_OC) begin
            next_A_EX = A_saved_data_OC;
        end
        else if (A_forward_OC) begin
            next_A_EX = forward_data_by_bank[A_bank_OC];
        end
        else begin
            next_A_EX = reg_read_data_by_bank_by_port[A_bank_OC][A_reg_read_port];
        end

        // collect B value to save OR pass to EX1
        if (B_unneeded_or_is_zero_OC) begin
            next_B_EX = 32'h0;
        end
        else if (B_saved_OC) begin
            next_B_EX = B_saved_data_OC;
        end
        else if (B_forward_OC) begin
            next_B_EX = forward_data_by_bank[B_bank_OC];
        end
        else begin
            next_B_EX = reg_read_data_by_bank_by_port[B_bank_OC][B_reg_read_port];
        end
    end

    // map imm20 -> imm32
        // used own instr -> imm20 mapping to allow I-imm, B-imm, U-imm, and J-imm in 20 bits
        // sign bit always at imm20[11]
    always_comb begin
        
        // sign bit always imm20[11]
        next_imm32_EX[31] = imm20_OC[11];

        // U-imm uses imm20[10:0]
        // else 11x imm20[11]
        if (op_OC[3:1] == 3'b011) begin
            next_imm32_EX[30:20] = imm20_OC[10:0];
        end else begin
            next_imm32_EX[30:20] = {11{imm20_OC[11]}};
        end

        // I-imm and B-imm use 8x imm20[11]
        // else imm20[19:12]
        if (op_OC == 4'b0000 | op_OC[3]) begin
            next_imm32_EX[19:12] = {8{imm20_OC[11]}};
        end else begin
            next_imm32_EX[19:12] = imm20_OC[19:12];
        end

        // I-imm uses imm20[11]
        // U-imm uses 0
        // else imm20[0]
        if (op_OC == 4'b0000) begin
            next_imm32_EX[11] = imm20_OC[11];
        end else if (op_OC[3:1] == 3'b011) begin
            next_imm32_EX[11] = 1'b0;
        end else begin
            next_imm32_EX[11] = imm20_OC[0];
        end

        // U-imm uses 0
        // else imm20[10:1]
        if (op_OC[3:1] == 3'b011) begin
            next_imm32_EX[10:1] = 10'h0;
        end else begin
            next_imm32_EX[10:1] = imm20_OC[10:1];
        end

        // I-imm uses imm20[0]
        // else 0
        if (op_OC == 4'b0000) begin
            next_imm32_EX[0] = imm20_OC[0];
        end else begin
            next_imm32_EX[0] = 1'b0;
        end
    end

    // ----------------------------------------------------------------
    // EX1 Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_EX <= 1'b0;
            op_EX <= 4'b0000;
            pred_info_EX <= 8'h0;
            pred_lru_EX <= 1'b0;
            is_link_ra_EX <= 1'b0;
            is_ret_ra_EX <= 1'b0;
            PC_EX <= 32'h0;
            pred_PC_EX <= 32'h0;
            imm32_EX <= 20'h0;
            A_EX <= 32'h0;
            B_EX <= 32'h0;
            dest_PR_EX <= '0;
            ROB_index_EX <= '0;
        end
        else if (stall_EX) begin
            valid_EX <= valid_EX;
            op_EX <= op_EX;
            pred_info_EX <= pred_info_EX;
            pred_lru_EX <= pred_lru_EX;
            is_link_ra_EX <= is_link_ra_EX;
            is_ret_ra_EX <= is_ret_ra_EX;
            PC_EX <= PC_EX;
            pred_PC_EX <= pred_PC_EX;
            imm32_EX <= imm32_EX;
            A_EX <= A_EX;
            B_EX <= B_EX;
            dest_PR_EX <= dest_PR_EX;
            ROB_index_EX <= ROB_index_EX;
        end
        else begin
            valid_EX <= next_valid_EX;
            op_EX <= next_op_EX;
            pred_info_EX <= next_pred_info_EX;
            pred_lru_EX <= next_pred_lru_EX;
            is_link_ra_EX <= next_is_link_ra_EX;
            is_ret_ra_EX <= next_is_ret_ra_EX;
            PC_EX <= next_PC_EX;
            pred_PC_EX <= next_pred_PC_EX;
            imm32_EX <= next_imm32_EX;
            A_EX <= next_A_EX;
            B_EX <= next_B_EX;
            dest_PR_EX <= next_dest_PR_EX;
            ROB_index_EX <= next_ROB_index_EX;
        end
    end

    // pass-through's:
    assign next_WB_stage_valid = valid_EX;
    assign next_WB_stage_op = op_EX;
    assign next_WB_stage_pred_info = pred_info_EX;
    assign next_WB_stage_pred_lru = pred_lru_EX;
    assign next_WB_stage_is_link_ra = is_link_ra_EX;
    assign next_WB_stage_is_ret_ra = is_ret_ra_EX;
    assign next_WB_stage_pred_PC = pred_PC_EX;
    assign next_WB_stage_dest_PR = dest_PR_EX;
    assign next_WB_stage_ROB_index = ROB_index_EX;

    // internal EX blocks:
    assign PC_plus_imm32_EX = PC_EX + imm32_EX;
    assign PC_plus_2_EX = PC_EX + 32'h2;
    assign PC_plus_4_EX = PC_EX + 32'h4;
    assign A_plus_imm32_EX = A_EX + imm32_EX;
    assign inner_A_lt_B_EX = A_EX[30:0] < B_EX[30:0];
    assign A_eq_B_EX = A_EX == B_EX;
    assign A_eq_zero_EX = A_EX == 32'h0;
    assign A_lts_B_EX = A_EX[31] & ~B_EX[31] | inner_A_lt_B_EX & ~(~A_EX[31] & B_EX[31]);
    assign A_ltu_B_EX = ~A_EX[31] & B_EX[31] | inner_A_lt_B_EX & ~(A_EX[31] & ~B_EX[31]);

    // op-wise behavior
        // next_WB_stage_target_PC
        // next_WB_stage_is_taken
        // next_WB_stage_start_PC
        // next_WB_stage_write_data
    always_comb begin
        
        case (op_EX)

            4'b0000: // JALR
            begin
                next_WB_stage_target_PC = A_plus_imm32_EX;
                next_WB_stage_is_taken = 1'b1;
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX;
            end

            4'b0001: // C.JALR
            begin
                next_WB_stage_target_PC = A_EX;
                next_WB_stage_is_taken = 1'b1;
                next_WB_stage_start_PC = PC_EX;
                next_WB_stage_write_data = PC_plus_2_EX;
            end

            4'b0010: // JAL
            begin
                next_WB_stage_target_PC = PC_plus_imm32_EX;
                next_WB_stage_is_taken = 1'b1;
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX;
            end

            4'b0011: // C.JAL
            begin
                next_WB_stage_target_PC = PC_plus_imm32_EX;
                next_WB_stage_is_taken = 1'b1;
                next_WB_stage_start_PC = PC_EX;
                next_WB_stage_write_data = PC_plus_2_EX;
            end

            4'b0100: // C.J
            begin
                next_WB_stage_target_PC = PC_plus_imm32_EX;
                next_WB_stage_is_taken = 1'b1;
                next_WB_stage_start_PC = PC_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b0101: // C.JR
            begin
                next_WB_stage_target_PC = A_EX;
                next_WB_stage_is_taken = 1'b1;
                next_WB_stage_start_PC = PC_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b0110: // LUI
            begin
                next_WB_stage_target_PC = PC_plus_imm32_EX; // don't care
                next_WB_stage_is_taken = 1'b0; // don't care
                next_WB_stage_start_PC = PC_plus_2_EX; // don't care
                next_WB_stage_write_data = imm32_EX;
            end

            4'b0111: // AUIPC
            begin
                next_WB_stage_target_PC = PC_plus_imm32_EX; // don't care
                next_WB_stage_is_taken = 1'b0; // don't care
                next_WB_stage_start_PC = PC_plus_2_EX; // don't care
                next_WB_stage_write_data = PC_plus_imm32_EX;
            end

            4'b1000: // BEQ
            begin
                if (A_eq_B_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b1001: // BNE
            begin
                if (~A_eq_B_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b1010: // C.BEQZ
            begin
                if (A_eq_zero_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b1011: // C.BNEZ
            begin
                if (~A_eq_zero_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b1100: // BLT
            begin
                if (A_lts_B_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b1101: // BGE
            begin
                if (~A_lts_B_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b1110: // BLTU
            begin
                if (A_ltu_B_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end

            4'b1111: // BGEU
            begin
                if (~A_ltu_B_EX) begin
                    next_WB_stage_target_PC = PC_plus_imm32_EX;
                    next_WB_stage_is_taken = 1'b1;
                end else begin
                    next_WB_stage_target_PC = PC_plus_4_EX;
                    next_WB_stage_is_taken = 1'b0;
                end
                next_WB_stage_start_PC = PC_plus_2_EX;
                next_WB_stage_write_data = PC_plus_4_EX; // don't care
            end
        endcase
    end

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            WB_stage_valid <= 1'b0;
            WB_stage_op <= 4'b0000;
            WB_stage_pred_info <= 8'h0;
            WB_stage_pred_lru <= 1'b0;
            WB_stage_is_link_ra <= 1'b0;
            WB_stage_is_ret_ra <= 1'b0;
            WB_stage_is_taken <= 1'b1;
            WB_stage_start_PC <= 32'h2;
            WB_stage_pred_PC <= 32'h0;
            WB_stage_target_PC <= 32'h0;
            WB_stage_write_data <= 32'h4;
            WB_stage_dest_PR <= 7'h0;
            WB_stage_ROB_index <= 7'h0;

            WB_stage_WB_acked <= 1'b0;
            WB_stage_branch_notif_acked <= 1'b0;
        end
        else if (stall_WB) begin
            WB_stage_valid <= WB_stage_valid;
            WB_stage_op <= WB_stage_op;
            WB_stage_pred_info <= WB_stage_pred_info;
            WB_stage_pred_lru <= WB_stage_pred_lru;
            WB_stage_is_link_ra <= WB_stage_is_link_ra;
            WB_stage_is_ret_ra <= WB_stage_is_ret_ra;
            WB_stage_is_taken <= WB_stage_is_taken;
            WB_stage_start_PC <= WB_stage_start_PC;
            WB_stage_pred_PC <= WB_stage_pred_PC;
            WB_stage_target_PC <= WB_stage_target_PC;
            WB_stage_write_data <= WB_stage_write_data;
            WB_stage_dest_PR <= WB_stage_dest_PR;
            WB_stage_ROB_index <= WB_stage_ROB_index;

            WB_stage_WB_acked <= WB_stage_WB_acked | WB_ready;
            WB_stage_branch_notif_acked <= WB_stage_branch_notif_acked | branch_notif_ready;
        end
        else begin
            WB_stage_valid <= next_WB_stage_valid;
            WB_stage_op <= next_WB_stage_op;
            WB_stage_pred_info <= next_WB_stage_pred_info;
            WB_stage_pred_lru <= next_WB_stage_pred_lru;
            WB_stage_is_link_ra <= next_WB_stage_is_link_ra;
            WB_stage_is_ret_ra <= next_WB_stage_is_ret_ra;
            WB_stage_is_taken <= next_WB_stage_is_taken;
            WB_stage_start_PC <= next_WB_stage_start_PC;
            WB_stage_pred_PC <= next_WB_stage_pred_PC;
            WB_stage_target_PC <= next_WB_stage_target_PC;
            WB_stage_write_data <= next_WB_stage_write_data;
            WB_stage_dest_PR <= next_WB_stage_dest_PR;
            WB_stage_ROB_index <= next_WB_stage_ROB_index;

            WB_stage_WB_acked <= 1'b0;
            WB_stage_branch_notif_acked <= 1'b0;
        end
    end

    assign WB_data = WB_stage_write_data;
    assign WB_PR = WB_stage_dest_PR;
    assign WB_ROB_index = WB_stage_ROB_index;
    
    assign branch_notif_ROB_index = WB_stage_ROB_index;
    assign branch_notif_is_mispredict = WB_stage_target_PC != WB_stage_pred_PC;
    assign branch_notif_is_taken = WB_stage_is_taken;
    assign branch_notif_pred_lru = WB_stage_pred_lru;
    assign branch_notif_start_PC = WB_stage_start_PC;
    assign branch_notif_target_PC = WB_stage_target_PC;

    // PC start to target range
    assign WB_stage_start_neq_target_upper_PC = WB_stage_target_PC[31:32-UPPER_PC_WIDTH] != WB_stage_start_PC[31:32-UPPER_PC_WIDTH];
    assign WB_stage_delta_start_target_upper_PC = WB_stage_target_PC[31:32-UPPER_PC_WIDTH] - WB_stage_start_PC[31:32-UPPER_PC_WIDTH];

    assign WB_stage_small_delta_upper_PC = 
        WB_stage_delta_start_target_upper_PC[UPPER_PC_WIDTH-1:2] == '0 
        | WB_stage_delta_start_target_upper_PC[UPPER_PC_WIDTH-1:2] == '1;
        // essentially, check can get delta with sign extension of 3-bit number
    
    assign branch_notif_use_upct = ~WB_stage_small_delta_upper_PC;

    // leave branch_notif_updated_pred_info to bru_pred_info_updater module
        // this way can easily change this logic and independently verify it
        // logic is independent from figuring out what the WB and branch notif interface values should be
            // besides of course branch_notif_updated_pred_info
        // the upper PC table index bits and the complex branch 2bc bits are handled by the frontend when the branch notif arrives
    bru_pred_info_updater BRU_PIU (
        // inputs
        .op(WB_stage_op),
        .start_pred_info(WB_stage_pred_info),
        .is_link_ra(WB_stage_is_link_ra),
        .is_ret_ra(WB_stage_is_ret_ra),
        .is_taken(WB_stage_is_taken),
        .is_mispredict(branch_notif_is_mispredict),
        .start_neq_target_upper_PC(WB_stage_start_neq_target_upper_PC),
        .delta_start_target_upper_PC(WB_stage_delta_start_target_upper_PC[2:0]),
        .large_delta_upper_PC(branch_notif_use_upct),
        // outputs
        .updated_pred_info(branch_notif_updated_pred_info)
    );

    // op-wise behavior
        // WB_valid
        // branch_notif_valid
    always_comb begin
        
        casez (WB_stage_op)

            4'b0000: // JALR
            begin
                WB_valid = WB_stage_valid;
                branch_notif_valid = WB_stage_valid;
            end

            4'b0001: // C.JALR
            begin
                WB_valid = WB_stage_valid;
                branch_notif_valid = WB_stage_valid;
            end

            4'b0010: // JAL
            begin
                WB_valid = WB_stage_valid;
                branch_notif_valid = WB_stage_valid;
            end

            4'b0011: // C.JAL
            begin
                WB_valid = WB_stage_valid;
                branch_notif_valid = WB_stage_valid;
            end

            4'b0100: // C.J
            begin
                WB_valid = 1'b0;
                branch_notif_valid = WB_stage_valid;
            end

            4'b0101: // C.JR
            begin
                WB_valid = 1'b0;
                branch_notif_valid = WB_stage_valid;
            end

            4'b0110: // LUI
            begin
                WB_valid = WB_stage_valid;
                branch_notif_valid = 1'b0;
            end

            4'b0111: // AUIPC
            begin
                WB_valid = WB_stage_valid;
                branch_notif_valid = 1'b0;
            end

            4'b1???: // BEQ, BNE, C.BEQZ, C.BNEZ, BLT, BGE, BLTU, BGEU
            begin
                WB_valid = 1'b0;
                branch_notif_valid = WB_stage_valid;
            end

        endcase

        WB_valid &= ~WB_stage_WB_acked;
        branch_notif_valid &= ~WB_stage_branch_notif_acked;
    end

endmodule