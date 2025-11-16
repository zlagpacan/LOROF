/*
    Filename: alu_reg_pipeline.sv
    Author: zlagpacan
    Description: RTL for ALU Register-Register Pipeline
    Spec: LOROF/spec/design/alu_reg_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_reg_pipeline #(
    parameter IS_OC_BUFFER_SIZE = 2,
    parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3
) (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU reg op issue from IQ
    input logic                             issue_valid,
    input logic [3:0]                       issue_op,
    input logic                             issue_A_forward,
    input logic                             issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_bank,
    input logic                             issue_B_forward,
    input logic                             issue_B_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_B_bank,
    input logic [LOG_PR_COUNT-1:0]          issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]       issue_ROB_index,

    // ready feedback to IQ
    output logic                            issue_ready,

    // reg read info and data from PRF
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

    // writeback feedback from PRF
    input logic WB_ready
);
    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_WB;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                           valid_OC;
    logic [3:0]                     op_OC;
    logic                           A_forward_OC;
    logic                           A_is_reg_OC;
    logic                           B_forward_OC;
    logic                           B_is_reg_OC;
    logic [LOG_PR_COUNT-1:0]        dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]     ROB_index_OC;

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

    logic                           next_WB_valid;
    logic [3:0]                     next_WB_op;
    logic                           next_WB_A_forward;
    logic                           next_WB_A_is_reg;
    logic                           next_WB_B_forward;
    logic                           next_WB_B_is_reg;
    logic [LOG_PR_COUNT-1:0]        next_WB_PR;
    logic [LOG_ROB_ENTRIES-1:0]     next_WB_ROB_index;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    logic [3:0]     WB_op;
    logic           WB_A_forward;
    logic           WB_A_is_reg;
    logic           WB_B_forward;
    logic           WB_B_is_reg;

    logic [31:0]    WB_A;
    logic [31:0]    WB_B;

    // ----------------------------------------------------------------
    // Control Logic: 

    assign stall_WB = WB_valid & ~WB_ready;

    // ----------------------------------------------------------------
    // IS -> OC Buffer Logic:

    q_fast_ready #(
        .DATA_WIDTH(4 + 1 + 1 + 1 + 1 + LOG_PR_COUNT + LOG_ROB_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_op,
            issue_A_forward,
            ~(issue_A_forward | issue_A_is_zero),
            issue_B_forward,
            ~(issue_B_forward | issue_B_is_zero),
            issue_dest_PR,
            issue_ROB_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            op_OC,
            A_forward_OC,
            A_is_reg_OC,
            B_forward_OC,
            B_is_reg_OC,
            dest_PR_OC,
            ROB_index_OC
        }),
        .deq_ready(~stall_WB & operands_ready_OC)
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
        next_WB_valid = valid_OC & operands_ready_OC;
        next_WB_op = op_OC;
        next_WB_A_forward = A_forward_OC;
        next_WB_A_is_reg = A_is_reg_OC;
        next_WB_B_forward = B_forward_OC;
        next_WB_B_is_reg = B_is_reg_OC;
        next_WB_PR = dest_PR_OC;
        next_WB_ROB_index = ROB_index_OC;
    end

    // ----------------------------------------------------------------
    // WB Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            WB_valid <= 1'b0;
            WB_op <= 4'b0000;
            WB_A_forward <= 1'b0;
            WB_A_is_reg <= 1'b0;
            WB_B_forward <= 1'b0;
            WB_B_is_reg <= 1'b0;
            WB_PR <= '0;
            WB_ROB_index <= '0;
        end
        else if (~stall_WB) begin
            WB_valid <= next_WB_valid;
            WB_op <= next_WB_op;
            WB_A_forward <= next_WB_A_forward;
            WB_A_is_reg <= next_WB_A_is_reg;
            WB_B_forward <= next_WB_B_forward;
            WB_B_is_reg <= next_WB_B_is_reg;
            WB_PR <= next_WB_PR;
            WB_ROB_index <= next_WB_ROB_index;
        end
    end

    // data gathering
    always_comb begin
        WB_A = ({32{WB_A_is_reg}} & deq_A_reg_data) | ({32{WB_A_forward}} & deq_A_forward_data);
        WB_B = ({32{WB_B_is_reg}} & deq_B_reg_data) | ({32{WB_B_forward}} & deq_B_forward_data);

        deq_A_reg_ready = WB_valid & WB_A_is_reg & WB_ready;
        deq_A_forward_ready = WB_valid & WB_A_forward & WB_ready;

        deq_B_reg_ready = WB_valid & WB_B_is_reg & WB_ready;
        deq_B_forward_ready = WB_valid & WB_B_forward & WB_ready;
    end

    // actual ALU
    alu ALU (
        .op(WB_op),
        .A(WB_A),
        .B(WB_B),
        .out(WB_data)
    );

endmodule