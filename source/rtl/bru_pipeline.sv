/*
    Filename: bru_pipeline.sv
    Author: zlagpacan
    Description: RTL for Branch Resolution Unit Pipeline
    Spec: LOROF/spec/design/bru_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module bru_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // BRU op issue to BRU IQ
    input logic                             issue_valid,
    input logic [3:0]                       issue_op,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   issue_pred_info,
    input logic                             issue_is_link_ra,
    input logic                             issue_is_ret_ra,
    input logic [31:0]                      issue_PC,
    input logic [31:0]                      issue_pred_PC,
    input logic [19:0]                      issue_imm20,
    input logic                             issue_A_unneeded,
    input logic                             issue_A_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_bank,
    input logic                             issue_B_unneeded,
    input logic                             issue_B_forward,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_B_bank,
    input logic [LOG_PR_COUNT-1:0]          issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       issue_ROB_index,

    // output feedback to BRU IQ
    output logic issue_ready,

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
    input logic WB_ready,

    // branch notification to ROB
    output logic                            branch_notif_valid,
    output logic [LOG_ROB_ENTRIES-1:0]      branch_notif_ROB_index,
    output logic                            branch_notif_mispredict,
    output logic                            branch_notif_taken,
    output logic [BTB_PRED_INFO_WIDTH-1:0]  branch_notif_updated_pred_info,
    output logic                            branch_notif_upper_PC_out_of_range,
    output logic [31:0]                     branch_notif_start_PC,
    output logic [31:0]                     branch_notif_target_PC,

    // branch notification backpressure from ROB
    input logic branch_notif_ready
);

    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_WB;
    logic stall_EX2;
    logic stall_EX1;
    logic stall_OC;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                               valid_OC;
    logic [3:0]                         op_OC;
    logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info_OC;
    logic                               is_link_ra_OC;
    logic                               is_ret_ra_OC;
    logic [31:0]                        PC_OC;
    logic [31:0]                        pred_PC_OC;
    logic [19:0]                        imm20_OC;
    logic                               A_unneeded_OC;
    logic                               A_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]      A_bank_OC;
    logic                               B_unneeded_OC;
    logic                               B_forward_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]      B_bank_OC;
    logic [LOG_PR_COUNT-1:0]            dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]         ROB_index_OC;

    logic [31:0] A_saved_data_OC;
    logic [31:0] B_saved_data_OC;

    logic launch_ready_OC;

    logic                               next_valid_EX1;
    logic [3:0]                         next_op_EX1;
    logic [BTB_PRED_INFO_WIDTH-1:0]     next_pred_info_EX1;
    logic                               next_is_link_ra_EX1;
    logic                               next_is_ret_ra_EX1;
    logic [31:0]                        next_PC_EX1;
    logic [31:0]                        next_pred_PC_EX1;
    logic [31:0]                        next_imm32_EX1;
    logic [31:0]                        next_A_EX1;
    logic [31:0]                        next_B_EX1;
    logic [LOG_PR_COUNT-1:0]            next_dest_PR_EX1;
    logic [LOG_ROB_ENTRIES-1:0]         next_ROB_index_EX1;

    // ----------------------------------------------------------------
    // EX1 Stage Signals:

    logic                               valid_EX1;
    logic [3:0]                         op_EX1;
    logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info_EX1;
    logic                               is_link_ra_EX1;
    logic                               is_ret_ra_EX1;
    logic [31:0]                        PC_EX1;
    logic [31:0]                        pred_PC_EX1;
    logic [31:0]                        imm32_EX1;
    logic [31:0]                        A_EX1;
    logic [31:0]                        B_EX1;
    logic [LOG_PR_COUNT-1:0]            dest_PR_EX1;
    logic [LOG_ROB_ENTRIES-1:0]         ROB_index_EX1;

    logic [31:0]    PC_plus_imm32_EX1;
    logic [31:0]    seq_2_4_EX1;
    logic [31:0]    PC_plus_2_4_EX1;
    logic [31:0]    A_plus_imm32_EX1;
    logic           inner_A_lt_B_EX1;
    logic           A_eq_B_EX1;
    logic           A_lts_B_EX1;
    logic           A_ltu_B_EX1;

    logic                               next_valid_EX2;
    logic [3:0]                         next_op_EX2;
    logic [BTB_PRED_INFO_WIDTH-1:0]     next_pred_info_EX2;
    logic                               next_is_link_ra_EX2;
    logic                               next_is_ret_ra_EX2;
    logic [31:0]                        next_PC_EX2;
    logic [31:0]                        next_pred_PC_EX2;
    logic [31:0]                        next_target_PC_EX2;
    logic [31:0]                        next_write_data_EX2;
    logic [LOG_PR_COUNT-1:0]            next_dest_PR_EX2;
    logic [LOG_ROB_ENTRIES-1:0]         next_ROB_index_EX2;

    // ----------------------------------------------------------------
    // EX2 Stage Signals:

    logic                               valid_EX2;
    logic [3:0]                         op_EX2;
    logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info_EX2;
    logic                               is_link_ra_EX2;
    logic                               is_ret_ra_EX2;
    logic [31:0]                        PC_EX2;
    logic [31:0]                        pred_PC_EX2;
    logic [31:0]                        target_PC_EX2;
    logic [31:0]                        write_data_EX2;
    logic [LOG_PR_COUNT-1:0]            dest_PR_EX2;
    logic [LOG_ROB_ENTRIES-1:0]         ROB_index_EX2;

    logic                           next_WB_valid;
    logic [31:0]                    next_WB_data;
    logic [LOG_PR_COUNT-1:0]        next_WB_PR;
    logic [LOG_ROB_ENTRIES-1:0]     next_WB_ROB_index;

    logic                               next_branch_notif_valid;
    logic [LOG_ROB_ENTRIES-1:0]         next_branch_notif_ROB_index;
    logic                               next_branch_notif_mispredict;
    logic                               next_branch_notif_taken;
    logic [BTB_PRED_INFO_WIDTH-1:0]     next_branch_notif_updated_pred_info;
    logic                               next_branch_notif_upper_PC_out_of_range;
    logic [31:0]                        next_branch_notif_start_PC;
    logic [31:0]                        next_branch_notif_target_PC;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    // ----------------------------------------------------------------
    // Control Logic: 

    // propagate stalls backwards
    assign stall_WB = (WB_valid & ~WB_ready) | (branch_notif_valid & ~branch_notif_ready);
    assign stall_EX2 = valid_EX2 & stall_WB;
    assign stall_EX1 = valid_EX1 & stall_EX2;
    assign stall_OC = valid_OC & stall_EX1;

    // ----------------------------------------------------------------
    // OC Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_OC <= 1'b0;
            op_OC <= 4'b0000;
            pred_info_OC <= 8'h0;
            is_link_ra_OC <= 1'b0;
            is_ret_ra_OC <= 1'b0;
            PC_OC <= 32'h0;
            pred_PC_OC <= 32'h0;
            imm20_OC <= 20'h0;
            A_unneeded_OC <= 1'b0;
            A_forward_OC <= 1'b0;
            A_saved_OC <= 1'b0;
            A_saved_data_OC <= 32'h0;
            A_bank_OC <= 2'h0;
            B_unneeded_OC <= 1'b0;
            B_forward_OC <= 1'b0;
            B_bank_OC <= 2'h0;
            B_saved_OC <= 1'b0;
            B_saved_data_OC <= 32'h0;
            dest_PR_OC <= 7'h0;
            ROB_index_OC <= 7'h0;
        end
        // stall OC stage when have valid op which can't move on: issue_ready == 1'b0
        else if (~issue_ready) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            pred_info_OC <= pred_info_OC;
            is_link_ra_OC <= is_link_ra_OC;
            is_ret_ra_OC <= is_ret_ra_OC;
            PC_OC <= PC_OC;
            pred_PC_OC <= pred_PC_OC;
            imm20_OC <= imm20_OC;
            A_unneeded_OC <= A_unneeded_OC;
            A_forward_OC <= 1'b0;
            A_saved_OC <= A_saved_OC | A_forward_OC | A_reg_read_ack;
            A_saved_data_OC <= next_A_EX1;
            A_bank_OC <= A_bank_OC;
            B_unneeded_OC <= B_unneeded_OC;
            B_forward_OC <= 1'b0;
            B_saved_OC <= B_saved_OC | B_forward_OC | B_reg_read_ack;
            B_saved_data_OC <= next_B_EX1;
            B_bank_OC <= B_bank_OC;
            dest_PR_OC <= dest_PR_OC;
            ROB_index_OC <= ROB_index_OC;
        end
        // pass input issue to OC
        else begin
            valid_OC <= issue_valid;
            op_OC <= issue_op;
            pred_info_OC <= issue_pred_info;
            is_link_ra_OC <= issue_is_link_ra;
            is_ret_ra_OC <= issue_is_ret_ra;
            PC_OC <= issue_PC;
            pred_PC_OC <= issue_pred_PC;
            imm20_OC <= issue_imm20;
            A_unneeded_OC <= issue_A_unneeded;
            A_forward_OC <= issue_A_forward;
            A_saved_OC <= 1'b0;
            A_saved_data_OC <= next_A_EX1;
            A_bank_OC <= issue_A_bank;
            B_unneeded_OC <= issue_B_unneeded;
            B_forward_OC <= issue_B_forward;
            B_saved_OC <= 1'b0;
            B_saved_data_OC <= next_B_EX1;
            B_bank_OC <= issue_B_bank;
            dest_PR_OC <= issue_dest_PR;
            ROB_index_OC <= issue_ROB_index;
        end
    end

    assign launch_ready_OC = 
        // no backpressure
        ~stall_OC
        &
        // A operand present
        (A_unneeded_OC | A_saved_OC | A_forward_OC | A_reg_read_ack)
        &
        // B operand present
        (B_unneeded_OC | B_saved_OC | B_forward_OC | B_reg_read_ack)
    ;
    assign issue_ready = ~valid_OC | launch_ready_OC;

    assign next_valid_EX1 = valid_OC & launch_ready_OC;
    assign next_op_EX1 = op_OC;
    assign next_pred_info_EX1 = pred_info_OC;
    assign next_is_link_ra_EX1 = is_link_ra_OC;
    assign next_is_ret_ra_EX1 = is_ret_ra_OC;
    assign next_PC_EX1 = PC_OC;
    assign next_pred_PC_EX1 = pred_PC_OC;
    assign next_dest_PR_EX1 = dest_PR_OC;
    assign next_ROB_index_EX1 = ROB_index_OC;

    // A and B operand collection
    always_comb begin

        // collect A value to save OR pass to EX1
        if (A_saved_OC) begin
            next_A_EX1 = A_saved_data_OC;
        end
        else if (A_forward_OC) begin
            next_A_EX1 = forward_data_by_bank[A_bank_OC];
        end
        else begin
            next_A_EX1 = reg_read_data_by_bank_by_port[A_bank_OC][A_reg_read_port];
        end

        // collect B value to save OR pass to EX1
        if (B_saved_OC) begin
            next_B_EX1 = B_saved_data_OC;
        end
        else if (B_forward_OC) begin
            next_B_EX1 = forward_data_by_bank[B_bank_OC];
        end
        else begin
            next_B_EX1 = reg_read_data_by_bank_by_port[B_bank_OC][B_reg_read_port];
        end
    end

    // map imm20 -> imm32
        // used own instr -> imm20 mapping to allow I-imm, B-imm, U-imm, and J-imm in 20 bits
        // sign bit always at imm20[11]
    always_comb begin
        
        // sign bit always imm20[11]
        next_imm32_EX1[31] = imm20_OC[11];

        // U-imm uses imm20[10:0]
        // else 11x imm20[11]
        if (op_OC[3:1] == 3'b011) begin
            next_imm32_EX1[30:20] = imm20_OC[10:0];
        end else begin
            next_imm32_EX1[30:20] = {11{imm20_OC[11]}};
        end

        // I-imm and B-imm use 8x imm20[11]
        // else imm20[19:12]
        if (op_OC == 4'b0000 | op_OC[3]) begin
            next_imm32_EX1[19:12] = {8{imm20_OC[11]}};
        end else begin
            next_imm32_EX1[19:12] = imm20_OC[19:12];
        end

        // I-imm uses imm20[11]
        // U-imm uses 0
        // else imm20[0]
        if (op_OC == 4'b0000) begin
            next_imm32_EX1[11] = imm20_OC[11];
        end else if (op_OC[3:1] == 3'b011) begin
            next_imm32_EX1[11] = 1'b0;
        end else begin
            next_imm32_EX1[11] = imm20_OC[0];
        end

        // U-imm uses 0
        // else imm20[10:1]
        if (op_OC[3:1] == 3'b011) begin
            next_imm32_EX1[10:1] = 10'h0;
        end else begin
            next_imm32_EX1[10:1] = imm20_OC[10:1];
        end

        // I-imm uses imm20[0]
        // else 0
        if (op_OC == 4'b0000) begin
            next_imm32_EX1[0] = imm20_OC[0];
        end else begin
            next_imm32_EX1[0] = 1'b0;
        end
    end

    // ----------------------------------------------------------------
    // EX1 Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_EX1 <= 1'b0;
            op_EX1 <= 4'b0000;
            pred_info_EX1 <= 8'h0;
            is_link_ra_EX1 <= 1'b0;
            is_ret_ra_EX1 <= 1'b0;
            PC_EX1 <= 32'h0;
            pred_PC_EX1 <= 32'h0;
            imm32_EX1 <= 20'h0;
            A_EX1 <= 32'h0;
            B_EX1 <= 32'h0;
            dest_PR_EX1 <= '0;
            ROB_index_EX1 <= '0;
        end
        else if (stall_EX1) begin
            valid_EX1 <= valid_EX1;
            op_EX1 <= op_EX1;
            pred_info_EX1 <= pred_info_EX1;
            is_link_ra_EX1 <= is_link_ra_EX1;
            is_ret_ra_EX1 <= is_ret_ra_EX1;
            PC_EX1 <= PC_EX1;
            pred_PC_EX1 <= pred_PC_EX1;
            imm32_EX1 <= imm32_EX1;
            A_EX1 <= A_EX1;
            B_EX1 <= B_EX1;
            dest_PR_EX1 <= dest_PR_EX1;
            ROB_index_EX1 <= ROB_index_EX1;
        end
        else begin
            valid_EX1 <= next_valid_EX1;
            op_EX1 <= next_op_EX1;
            pred_info_EX1 <= next_pred_info_EX1;
            is_link_ra_EX1 <= next_is_link_ra_EX1;
            is_ret_ra_EX1 <= next_is_ret_ra_EX1;
            PC_EX1 <= next_PC_EX1;
            pred_PC_EX1 <= next_pred_PC_EX1;
            imm32_EX1 <= next_imm32_EX1;
            A_EX1 <= next_A_EX1;
            B_EX1 <= next_B_EX1;
            dest_PR_EX1 <= next_dest_PR_EX1;
            ROB_index_EX1 <= next_ROB_index_EX1;
        end
    end

    // pass-through's:
    assign next_valid_EX2 = valid_EX1;
    assign next_op_EX2 = op_EX1;
    assign next_pred_info_EX2 = pred_info_EX1;
    assign next_is_link_ra_EX2 = is_link_ra_EX1;
    assign next_is_ret_ra_EX2 = is_ret_ra_EX1;
    assign next_next_PC_EX2 = PC_EX1;
    assign next_pred_PC_EX2 = pred_PC_EX1;
    assign next_dest_PR_EX2 = dest_PR_EX1;
    assign next_ROB_index_EX2 = ROB_index_EX1;

    // internal EX1 blocks:
    assign PC_plus_imm32_EX1 = PC_EX1 + imm32_EX1;
    always_comb begin
        // PC+2 vs. PC+4
            // PC+2 definitely C.BEQZ, C.BNEZ, C.JAL, C.JALR
                // LUI, AUIPC, C.J, C.JR don't cares
        if (op_EX1[3:1] == 3'b101 | (~op_EX[3] & op_EX[0])) begin
            seq_2_4_EX1 = 32'h2;
        end else begin
            seq_2_4_EX1 = 32'h4;
        end
    end
    assign PC_plus_2_4_EX1 = PC_EX1 + seq_2_4_EX1;
    assign A_plus_imm32_EX1 = A_EX1 + imm32_EX1;
    assign inner_A_lt_B_EX1 = A_EX1[30:0] < B_EX1[30:0];
    assign A_eq_B_EX1 = A_EX1 == B_EX1;
    assign A_lts_B_EX1 = A_EX1[31] & ~B_EX1[31] | inner_A_lt_B_EX1 & ~(~A_EX1[31] & B_EX1[31]);
    assign A_ltu_B_EX1 = ~A_EX1[31] & B_EX1[31] | inner_A_lt_B_EX1 & ~(A_EX1[31] & ~B_EX1[31]);

    // op-wise behavior
    always_comb begin
        
    end

    // ----------------------------------------------------------------
    // EX2 Stage Logic:

    assign next_WB_PR = dest_PR_EX2;
    assign next_WB_ROB_index = ROB_index_EX2;
    
    assign next_branch_notif_ROB_index = ROB_index_EX2;

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            WB_valid <= 1'b0;
            WB_data <= 32'h4;
            WB_PR <= '0;
            WB_ROB_index <= '0;
            restart_req_valid <= 1'b0;
            restart_req_mispredict <= 1'b0;
            restart_req_ROB_index <= '0;
            restart_req_PC <= 32'h0;
            restart_req_taken <= 1'b1;
        end
        else if (stall_WB) begin
            WB_valid <= WB_valid & ~WB_ready;
            WB_data <= WB_data;
            WB_PR <= WB_PR;
            WB_ROB_index <= WB_ROB_index;
            restart_req_valid <= restart_req_valid & ~restart_req_ready;
            restart_req_mispredict <= restart_req_mispredict;
            restart_req_ROB_index <= restart_req_ROB_index;
            restart_req_PC <= restart_req_PC;
            restart_req_taken <= restart_req_taken;
        end
        else begin
            WB_valid <= next_WB_valid;
            WB_data <= next_WB_data;
            WB_PR <= next_WB_PR;
            WB_ROB_index <= next_WB_ROB_index;
            restart_req_valid <= next_restart_req_valid;
            restart_req_mispredict <= next_restart_req_mispredict;
            restart_req_ROB_index <= next_restart_req_ROB_index;
            restart_req_PC <= next_restart_req_PC;
            restart_req_taken <= next_restart_req_taken;
        end
    end

endmodule