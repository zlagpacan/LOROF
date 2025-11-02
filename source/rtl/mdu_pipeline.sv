/*
    Filename: mdu_pipeline.sv
    Author: zlagpacan
    Description: RTL for Mul-Div Unit Pipeline
    Spec: LOROF/spec/design/mdu_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module mdu_pipeline (

    // seq
    input logic CLK,
    input logic nRST,

    // MDU pipeline issue
    input logic                             issue_valid,
    input logic [2:0]                       issue_op,
    input logic                             issue_A_forward,
    input logic                             issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_PR,
    input logic                             issue_B_forward,
    input logic                             issue_B_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_B_PR,
    input logic [LOG_PR_COUNT-1:0]          issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       issue_ROB_index,

    // MDU pipeline feedback to IQ
    output logic                            issue_ready,

    // writeback bus by bank
    input logic [PRF_BANK_COUNT-1:0]                                        WB_bus_valid_by_bank,
    input logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   WB_bus_upper_PR_by_bank,

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

    // writeback feedback from
    input logic WB_ready
);
    // ----------------------------------------------------------------
    // Control Signals:

    logic stall_WB;
    logic stall_OC;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                           valid_OC;
    logic [2:0]                     op_OC;
    logic                           A_saved_OC;
    logic                           A_forward_OC;
    logic                           A_is_zero_OC;
    logic [LOG_PR_COUNT-1:0]        A_PR_OC;
    logic                           B_saved_OC;
    logic                           B_forward_OC;
    logic                           B_is_zero_OC;
    logic [LOG_PR_COUNT-1:0]        B_PR_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

    logic [31:0] A_saved_data_OC;
    logic [31:0] B_saved_data_OC;

    logic launch_ready_OC;

    logic                           next_valid_WB;
    logic [2:0]                     next_op_WB;
    logic [LOG_PR_COUNT-1:0]        next_A_PR_WB;
    logic [31:0]                    next_A_data_WB;
    logic                           next_A_msb_WB;
    logic [LOG_PR_COUNT-1:0]        next_B_PR_WB;
    logic [31:0]                    next_B_data_WB;
    logic                           next_B_msb_WB;
    logic [LOG_PR_COUNT-1:0]        next_dest_PR_WB;
    logic [LOG_ROB_ENTRIES-1:0]     next_ROB_index_WB;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    logic                           valid_WB;
    logic [2:0]                     op_WB;
    logic [LOG_PR_COUNT-1:0]        A_PR_WB;
    logic [31:0]                    A_data_WB;
    logic                           A_msb_WB;
    logic [LOG_PR_COUNT-1:0]        B_PR_WB;
    logic [31:0]                    B_data_WB;
    logic                           B_msb_WB;
    logic [LOG_PR_COUNT-1:0]        dest_PR_WB;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_WB;

    // ----------------------------------------------------------------
    // Multiplier Signals:

    logic [32:0] multiplier_A33;
    logic [32:0] multiplier_B33;
    logic [63:0] multiplier_result;

    // ----------------------------------------------------------------
    // Divider Signals:

    logic divider_clear;
    logic divider_is_signed;
    logic divider_done;

    logic [31:0] divider_quotient;
    logic [31:0] divider_remainder;

    // ----------------------------------------------------------------
    // Result Cache Signals:

    typedef struct packed {
        logic                       valid;
        logic [LOG_PR_COUNT-1:0]    A_PR;
        logic [LOG_PR_COUNT-1:0]    B_PR;
        logic [31:0]                div_result;
        logic [31:0]                rem_result;
    } result_cache_entry_t;

    result_cache_entry_t [MDU_RESULT_CACHE_ENTRIES-1:0] result_cache_array;

    logic [LOG_MDU_RESULT_CACHE_ENTRIES-1:0] result_cache_write_index;
    
    logic result_cache_hit;

    logic [31:0] result_cache_div_result;
    logic [31:0] result_cache_rem_result;

    // ----------------------------------------------------------------
    // Control Logic: 

    assign stall_WB = valid_WB & (~WB_ready | (op_WB[2] & ~(divider_done | result_cache_hit)));
    assign stall_OC = stall_WB & valid_OC;

    // ----------------------------------------------------------------
    // OC Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_OC <= 1'b0;
            op_OC <= 3'b0000;
            A_saved_OC <= 1'b0;
            A_forward_OC <= 1'b0;
            A_is_zero_OC <= 1'b0;
            A_PR_OC <= '0;
            B_saved_OC <= 1'b0;
            B_forward_OC <= 1'b0;
            B_is_zero_OC <= 1'b0;
            B_PR_OC <= '0;
            dest_PR_OC <= '0;
            ROB_index_OC <= '0;
        end
        // stall OC stage when have valid op which can't move on: issue_ready == 1'b0
        else if (~issue_ready) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            A_saved_OC <= A_saved_OC | A_forward_OC | A_reg_read_ack;
            A_forward_OC <= 1'b0;
            A_is_zero_OC <= A_is_zero_OC;
            A_PR_OC <= A_PR_OC;
            B_saved_OC <= B_saved_OC | B_forward_OC | B_reg_read_ack;
            B_forward_OC <= 1'b0;
            B_is_zero_OC <= B_is_zero_OC;
            B_PR_OC <= B_PR_OC;
            dest_PR_OC <= dest_PR_OC;
            ROB_index_OC <= ROB_index_OC;
        end
        // pass input issue to OC
        else begin
            valid_OC <= issue_valid;
            op_OC <= issue_op;
            A_saved_OC <= 1'b0;
            A_forward_OC <= issue_A_forward;
            A_is_zero_OC <= issue_A_is_zero;
            A_PR_OC <= issue_A_PR;
            B_saved_OC <= 1'b0;
            B_forward_OC <= issue_B_forward;
            B_is_zero_OC <= issue_B_is_zero;
            B_PR_OC <= issue_B_PR;
            dest_PR_OC <= issue_dest_PR;
            ROB_index_OC <= issue_ROB_index;
        end
    end

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            A_saved_data_OC <= 32'h0;
            B_saved_data_OC <= 32'h0;
        end
        else begin
            A_saved_data_OC <= next_A_data_WB;
            B_saved_data_OC <= next_B_data_WB;
        end
    end

    assign launch_ready_OC = 
        // no backpressure
        ~stall_OC
        &
        // A operand present
        (A_saved_OC | A_forward_OC | A_reg_read_ack | A_is_zero_OC)
        &
        // B operand present
        (B_saved_OC | B_forward_OC | B_reg_read_ack | B_is_zero_OC)
    ;

    assign issue_ready = ~valid_OC | launch_ready_OC;

    assign next_valid_WB = valid_OC & launch_ready_OC;
    assign next_op_WB = op_OC;
    assign next_A_PR_WB = A_PR_OC;
    assign next_B_PR_WB = B_PR_OC;
    assign next_dest_PR_WB = dest_PR_OC;
    assign next_ROB_index_WB = ROB_index_OC;

    always_comb begin

        // collect A value to save OR pass to EX
        if (A_is_zero_OC) begin
            next_A_data_WB = 32'h0;
        end
        else if (A_saved_OC) begin
            next_A_data_WB = A_saved_data_OC;
        end
        else if (A_forward_OC) begin
            next_A_data_WB = forward_data_by_bank[A_PR_OC[LOG_PRF_BANK_COUNT-1:0]];
        end
        else begin
            next_A_data_WB = reg_read_data_by_bank_by_port[A_PR_OC[LOG_PRF_BANK_COUNT-1:0]][A_reg_read_port];
        end

        // collect B value to save OR pass to EX
        if (B_is_zero_OC) begin
            next_B_data_WB = 32'h0;
        end
        else if (B_saved_OC) begin
            next_B_data_WB = B_saved_data_OC;
        end
        else if (B_forward_OC) begin
            next_B_data_WB = forward_data_by_bank[B_PR_OC[LOG_PRF_BANK_COUNT-1:0]];
        end
        else begin
            next_B_data_WB = reg_read_data_by_bank_by_port[B_PR_OC[LOG_PRF_BANK_COUNT-1:0]][B_reg_read_port];
        end

        // get bit 32 for signed 33b mul:

        // MULHU
        if (op_OC[1] & op_OC[0]) begin
            next_A_msb_WB = 1'b0;
            next_B_msb_WB = 1'b0;
        end
        // MULHSU
        else if (op_OC[1]) begin
            next_A_msb_WB = next_A_data_WB[31];
            next_B_msb_WB = 1'b0;
        end
        // MUL/MULHU
        else begin
            next_A_msb_WB = next_A_data_WB[31];
            next_B_msb_WB = next_B_data_WB[31];
        end
    end

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_WB <= 1'b0;
        end
        else if (~stall_WB) begin
            valid_WB <= next_valid_WB;
        end
    end
    
    always_ff @ (posedge CLK) begin
        if (~stall_WB) begin
            op_WB <= next_op_WB;
            A_PR_WB <= next_A_PR_WB;
            A_data_WB <= next_A_data_WB;
            A_msb_WB <= next_A_msb_WB;
            B_PR_WB <= next_B_PR_WB;
            B_data_WB <= next_B_data_WB;
            B_msb_WB <= next_B_msb_WB;
            dest_PR_WB <= next_dest_PR_WB;
            ROB_index_WB <= next_ROB_index_WB;
        end
    end

    always_comb begin
        WB_valid = valid_WB & (~op_WB[2] | divider_done | result_cache_hit);

        // mul
        if (~op_WB[2]) begin
            // MUL
            if (op_WB[1:0] == 2'b00) begin
                WB_data = multiplier_result[31:0];
            end
            // MULH*
            else begin
                WB_data = multiplier_result[63:32];
            end
        end
        // div
        else begin
            // result cache
            if (result_cache_hit) begin
                // DIV[U]
                if (~op_WB[1]) begin
                    WB_data = result_cache_div_result;
                end
                // REM[U]
                else begin
                    WB_data = result_cache_rem_result;
                end
            end
            // divider
            else begin
                // DIV[U]
                if (~op_WB[1]) begin
                    WB_data = divider_quotient;
                end
                // REM[U]
                else begin
                    WB_data = divider_remainder;
                end
            end
        end

        WB_PR = dest_PR_WB;
        WB_ROB_index = ROB_index_WB;
    end

    // ----------------------------------------------------------------
    // Multiplier Logic:

    // always_comb begin
    //     multiplier_A33[31:0] = A_data_WB;
    //     multiplier_B33[31:0] = B_data_WB;

    //     // MULHU
    //     if (op_WB[1] & op_WB[0]) begin
    //         multiplier_A33[32] = 1'b0;
    //         multiplier_B33[32] = 1'b0;
    //     end
    //     // MULHSU
    //     else if (op_WB[1]) begin
    //         multiplier_A33[32] = multiplier_A33[31];
    //         multiplier_B33[32] = 1'b0;
    //     end
    //     // MUL/MULH
    //     else begin
    //         multiplier_A33[32] = multiplier_A33[31];
    //         multiplier_B33[32] = multiplier_B33[31];
    //     end
    // end

    assign multiplier_A33 = {A_msb_WB, A_data_WB};
    assign multiplier_B33 = {B_msb_WB, B_data_WB};

    assign multiplier_result = $signed(multiplier_A33) * $signed(multiplier_B33);
    
    // ----------------------------------------------------------------
    // Divider Logic:

    assign divider_clear = ~valid_WB | ~op_WB[2] | ~stall_WB | result_cache_hit;
    assign divider_is_signed = ~op_WB[0];

    div32_nonrestoring_skip DIVIDER (
        .CLK(CLK),
        .nRST(nRST),

        .clear(divider_clear),
        .is_signed(divider_is_signed),
        .done(divider_done),

        .A32_in(A_data_WB),
        .B32_in(B_data_WB),
        
        .quotient_out(divider_quotient),
        .remainder_out(divider_remainder)
    );

    // ----------------------------------------------------------------
    // Result Cache Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            result_cache_array <= '0;
            result_cache_write_index <= '0;
        end
        else begin
            for (int entry = 0; entry < MDU_RESULT_CACHE_ENTRIES; entry++) begin
                if (
                    (
                        WB_bus_valid_by_bank[result_cache_array[entry].A_PR[LOG_PRF_BANK_COUNT-1:0]]
                        & WB_bus_upper_PR_by_bank[result_cache_array[entry].A_PR[LOG_PRF_BANK_COUNT-1:0]] == result_cache_array[entry].A_PR[LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT]
                    ) | (
                        WB_bus_valid_by_bank[result_cache_array[entry].B_PR[LOG_PRF_BANK_COUNT-1:0]]
                        & WB_bus_upper_PR_by_bank[result_cache_array[entry].B_PR[LOG_PRF_BANK_COUNT-1:0]] == result_cache_array[entry].B_PR[LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT]
                    )
                ) begin
                    result_cache_array[entry].valid <= 1'b0;
                end
            end

            if (divider_done) begin
                result_cache_array[result_cache_write_index].valid <= 1'b1;
                result_cache_array[result_cache_write_index].A_PR <= A_PR_WB;
                result_cache_array[result_cache_write_index].B_PR <= A_PR_WB;
                result_cache_array[result_cache_write_index].div_result <= divider_quotient;
                result_cache_array[result_cache_write_index].rem_result <= divider_remainder[31:0];
                result_cache_write_index <= result_cache_write_index + 1;
            end
        end
    end

    always_comb begin
        result_cache_hit = 1'b0;
        result_cache_div_result = result_cache_array[0].div_result;
        result_cache_rem_result = result_cache_array[0].rem_result;

        for (int entry = 0; entry < MDU_RESULT_CACHE_ENTRIES; entry++) begin
            if (
                result_cache_array[entry].valid
                & A_PR_WB == result_cache_array[entry].A_PR
                & B_PR_WB == result_cache_array[entry].B_PR
            ) begin
                result_cache_hit = 1'b1;
                result_cache_div_result = result_cache_array[entry].div_result;
                result_cache_rem_result = result_cache_array[entry].rem_result;
            end
        end
    end

endmodule