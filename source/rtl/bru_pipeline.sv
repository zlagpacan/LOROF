/*
    Filename: bru_pipeline.sv
    Author: zlagpacan
    Description: RTL for Branch Resolution Unit Pipeline
    Spec: LOROF/spec/design/bru_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pipeline #(
    parameter IS_OC_BUFFER_SIZE = 2,
    parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3
) (
    
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

    // reg read data from PRF
    input logic         A_reg_read_resp_valid,
    input logic [31:0]  A_reg_read_resp_data,
    input logic         B_reg_read_resp_valid,
    input logic [31:0]  B_reg_read_resp_data,

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
    logic                               A_forward_OC;
    logic                               A_is_reg_OC;
    logic                               B_forward_OC;
    logic                               B_is_reg_OC;
    logic [LOG_PR_COUNT-1:0]            dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]         ROB_index_OC;

    logic operands_ready_OC;

    logic           enq_A_reg_valid;
    logic [31:0]    enq_A_reg_data;
    // logic           enq_A_reg_ready; // should always be 1
    logic           deq_A_reg_valid;
    logic [31:0]    deq_A_reg_data;
    logic           deq_A_reg_ready;

    logic           enq_B_reg_valid;
    logic [31:0]    enq_B_reg_data;
    // logic           enq_B_reg_ready; // should always be 1
    logic           deq_B_reg_valid;
    logic [31:0]    deq_B_reg_data;
    logic           deq_B_reg_ready;

    logic [LOG_PRF_BANK_COUNT-1:0]  enq_A_forward_bank;
    logic [LOG_PRF_BANK_COUNT-1:0]  enq_B_forward_bank;

    logic           enq_A_forward_valid;
    logic [31:0]    enq_A_forward_data;
    // logic           enq_A_forward_ready; // should always be 1
    logic           deq_A_forward_valid;
    logic [31:0]    deq_A_forward_data;
    logic           deq_A_forward_ready;

    logic           enq_B_forward_valid;
    logic [31:0]    enq_B_forward_data;
    // logic           enq_B_forward_ready; // should always be 1
    logic           deq_B_forward_valid;
    logic [31:0]    deq_B_forward_data;
    logic           deq_B_forward_ready;

    logic                               next_valid_EX;
    logic [3:0]                         next_op_EX;
    logic [BTB_PRED_INFO_WIDTH-1:0]     next_pred_info_EX;
    logic                               next_pred_lru_EX;
    logic                               next_is_link_ra_EX;
    logic                               next_is_ret_ra_EX;
    logic [31:0]                        next_PC_EX;
    logic [31:0]                        next_pred_PC_EX;
    logic [31:0]                        next_imm32_EX;
    logic                               next_A_forward_EX;
    logic                               next_A_is_reg_EX;
    logic                               next_B_forward_EX;
    logic                               next_B_is_reg_EX;
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
    logic                               A_forward_EX;
    logic                               A_is_reg_EX;
    logic                               B_forward_EX;
    logic                               B_is_reg_EX;
    logic [LOG_PR_COUNT-1:0]            dest_PR_EX;
    logic [LOG_ROB_ENTRIES-1:0]         ROB_index_EX;

    logic [31:0] A_data_EX;
    logic [31:0] B_data_EX;

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

    logic WB_stage_need_WB;
    logic WB_stage_need_branch_notif;

    logic                       WB_stage_start_neq_target_upper_PC;
    logic [UPPER_PC_WIDTH-1:0]  WB_stage_delta_start_target_upper_PC;
    logic                       WB_stage_small_delta_upper_PC;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    // ----------------------------------------------------------------
    // Control Logic: 

    // propagate stalls backwards
    assign stall_WB = (WB_stage_need_WB & ~WB_ready) | (WB_stage_need_branch_notif & ~branch_notif_ready);
    assign stall_EX = valid_EX & stall_WB;

    // ----------------------------------------------------------------
    // IS -> OC Buffer Logic:

    q_fast_ready #(
        .DATA_WIDTH(4 + BTB_PRED_INFO_WIDTH + 1 + 1 + 1 + 32 + 32 + 20 + 1 + 1 + 1 + 1 + LOG_PR_COUNT + LOG_ROB_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_op,
            issue_pred_info,
            issue_pred_lru,
            issue_is_link_ra,
            issue_is_ret_ra,
            issue_PC,
            issue_pred_PC,
            issue_imm20,
            issue_A_forward,
            ~(issue_A_forward | issue_A_unneeded_or_is_zero),
            issue_A_forward,
            ~(issue_B_forward | issue_B_unneeded_or_is_zero),
            issue_dest_PR,
            issue_ROB_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            op_OC,
            pred_info_OC,
            pred_lru_OC,
            is_link_ra_OC,
            is_ret_ra_OC,
            PC_OC,
            pred_PC_OC,
            imm20_OC,
            A_forward_OC,
            A_is_reg_OC,
            B_forward_OC,
            B_is_reg_OC,
            dest_PR_OC,
            ROB_index_OC
        }),
        .deq_ready(~stall_EX & operands_ready_OC)
    );

    // ----------------------------------------------------------------
    // OC Stage Logic:

    assign operands_ready_OC = 
        // A operand present
        (~A_is_reg_OC | A_reg_read_resp_valid | deq_A_reg_valid)
        &
        // B operand present
        (~B_is_reg_OC | B_reg_read_resp_valid | deq_B_reg_valid)
    ;

    // reg read data buffers:

    always_comb begin
        enq_A_reg_valid = A_reg_read_resp_valid;
        enq_A_reg_data = A_reg_read_resp_data;

        enq_B_reg_valid = B_reg_read_resp_valid;
        enq_B_reg_data = B_reg_read_resp_data;
    end

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) A_REG_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_A_reg_valid),
        .enq_data(enq_A_reg_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_A_reg_valid),
        .deq_data(deq_A_reg_data),
        .deq_ready(deq_A_reg_ready)
    );

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) B_REG_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_B_reg_valid),
        .enq_data(enq_B_reg_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_B_reg_valid),
        .deq_data(deq_B_reg_data),
        .deq_ready(deq_B_reg_ready)
    );

    // forward data buffers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            enq_A_forward_valid <= 1'b0;
            enq_A_forward_bank <= 0;
            enq_B_forward_valid <= 1'b0;
            enq_B_forward_bank <= 0;
        end
        else begin
            enq_A_forward_valid <= issue_valid & issue_ready & issue_A_forward;
            enq_A_forward_bank <= issue_A_bank;
            enq_B_forward_valid <= issue_valid & issue_ready & issue_B_forward;
            enq_B_forward_bank <= issue_B_bank;
        end
    end

    always_comb begin
        enq_A_forward_data = forward_data_by_bank[enq_A_forward_bank];
        enq_B_forward_data = forward_data_by_bank[enq_B_forward_bank];
    end

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) A_FORWARD_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_A_forward_valid),
        .enq_data(enq_A_forward_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_A_forward_valid),
        .deq_data(deq_A_forward_data),
        .deq_ready(deq_A_forward_ready)
    );

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) B_FORWARD_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_B_forward_valid),
        .enq_data(enq_B_forward_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_B_forward_valid),
        .deq_data(deq_B_forward_data),
        .deq_ready(deq_B_forward_ready)
    );

    always_comb begin
        next_valid_EX = valid_OC & operands_ready_OC;
        next_op_EX = op_OC;
        next_pred_info_EX = pred_info_OC;
        next_pred_lru_EX = pred_lru_OC;
        next_is_link_ra_EX = is_link_ra_OC;
        next_is_ret_ra_EX = is_ret_ra_OC;
        next_PC_EX = PC_OC;
        next_pred_PC_EX = pred_PC_OC;
        next_A_forward_EX = A_forward_OC;
        next_A_is_reg_EX = A_is_reg_OC;
        next_B_forward_EX = B_forward_OC;
        next_B_is_reg_EX = B_is_reg_OC;
        next_dest_PR_EX = dest_PR_OC;
        next_ROB_index_EX = ROB_index_OC;
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
    // EX Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
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
            A_forward_EX <= 1'b0;
            A_is_reg_EX <= 1'b0;
            B_forward_EX <= 1'b0;
            B_is_reg_EX <= 1'b0;
            dest_PR_EX <= '0;
            ROB_index_EX <= '0;
        end
        else if (~stall_EX) begin
            valid_EX <= next_valid_EX;
            op_EX <= next_op_EX;
            pred_info_EX <= next_pred_info_EX;
            pred_lru_EX <= next_pred_lru_EX;
            is_link_ra_EX <= next_is_link_ra_EX;
            is_ret_ra_EX <= next_is_ret_ra_EX;
            PC_EX <= next_PC_EX;
            pred_PC_EX <= next_pred_PC_EX;
            imm32_EX <= next_imm32_EX;
            A_forward_EX <= next_A_forward_EX;
            A_is_reg_EX <= next_A_is_reg_EX;
            B_forward_EX <= next_B_forward_EX;
            B_is_reg_EX <= next_B_is_reg_EX;
            dest_PR_EX <= next_dest_PR_EX;
            ROB_index_EX <= next_ROB_index_EX;
        end
    end

    // data gathering
    always_comb begin
        A_data_EX = ({32{A_is_reg_EX}} & deq_A_reg_data) | ({32{A_forward_EX}} & deq_A_forward_data);
        B_data_EX = ({32{B_is_reg_EX}} & deq_B_reg_data) | ({32{B_forward_EX}} & deq_B_forward_data);

        deq_A_reg_ready = valid_EX & A_is_reg_EX & ~stall_EX;
        deq_A_forward_ready = valid_EX & A_forward_EX & ~stall_EX;

        deq_B_reg_ready = valid_EX & B_is_reg_EX & ~stall_EX;
        deq_B_forward_ready = valid_EX & B_forward_EX & ~stall_EX;
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
    assign A_plus_imm32_EX = A_data_EX + imm32_EX;
    assign inner_A_lt_B_EX = A_data_EX[30:0] < B_data_EX[30:0];
    assign A_eq_B_EX = A_data_EX == B_data_EX;
    assign A_eq_zero_EX = A_data_EX == 32'h0;
    assign A_lts_B_EX = A_data_EX[31] & ~B_data_EX[31] | inner_A_lt_B_EX & ~(~A_data_EX[31] & B_data_EX[31]);
    assign A_ltu_B_EX = ~A_data_EX[31] & B_data_EX[31] | inner_A_lt_B_EX & ~(A_data_EX[31] & ~B_data_EX[31]);

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
                next_WB_stage_target_PC = A_data_EX;
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
                next_WB_stage_target_PC = A_data_EX;
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
                    next_WB_stage_target_PC = PC_plus_2_EX;
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
                    next_WB_stage_target_PC = PC_plus_2_EX;
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
    // always_ff @ (posedge CLK) begin
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
        // WB_stage_need_WB
        // WB_stage_need_branch_notif
    always_comb begin
        
        casez (WB_stage_op)

            4'b0000: // JALR
            begin
                WB_stage_need_WB = WB_stage_valid;
                WB_stage_need_branch_notif = WB_stage_valid;
            end

            4'b0001: // C.JALR
            begin
                WB_stage_need_WB = WB_stage_valid;
                WB_stage_need_branch_notif = WB_stage_valid;
            end

            4'b0010: // JAL
            begin
                WB_stage_need_WB = WB_stage_valid;
                WB_stage_need_branch_notif = WB_stage_valid;
            end

            4'b0011: // C.JAL
            begin
                WB_stage_need_WB = WB_stage_valid;
                WB_stage_need_branch_notif = WB_stage_valid;
            end

            4'b0100: // C.J
            begin
                WB_stage_need_WB = 1'b0;
                WB_stage_need_branch_notif = WB_stage_valid;
            end

            4'b0101: // C.JR
            begin
                WB_stage_need_WB = 1'b0;
                WB_stage_need_branch_notif = WB_stage_valid;
            end

            4'b0110: // LUI
            begin
                WB_stage_need_WB = WB_stage_valid;
                WB_stage_need_branch_notif = 1'b0;
            end

            4'b0111: // AUIPC
            begin
                WB_stage_need_WB = WB_stage_valid;
                WB_stage_need_branch_notif = 1'b0;
            end

            4'b1???: // BEQ, BNE, C.BEQZ, C.BNEZ, BLT, BGE, BLTU, BGEU
            begin
                WB_stage_need_WB = 1'b0;
                WB_stage_need_branch_notif = WB_stage_valid;
            end

        endcase

        // don't assert valid's until both ready
        WB_valid = WB_stage_need_WB & ~stall_WB;
        branch_notif_valid = WB_stage_need_branch_notif & ~stall_WB;
    end

endmodule