/*
    Filename: alu_imm_pipeline.sv
    Author: zlagpacan
    Description: RTL for ALU Register-Immediate Pipeline
    Spec: LOROF/spec/design/alu_imm_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module alu_imm_pipeline #(
    parameter IS_OC_BUFFER_SIZE = 2,
    parameter OC_ENTRIES = IS_OC_BUFFER_SIZE + 1,
    parameter FAST_FORWARD_PIPE_COUNT = 4,
    parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // ALU imm op issue from IQ
    input logic                                     issue_valid,
    input logic [3:0]                               issue_op,
    input logic [11:0]                              issue_imm12,
    input logic                                     issue_A_is_reg,
    input logic                                     issue_A_is_bus_forward,
    input logic                                     issue_A_is_fast_forward,
    input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]   issue_A_fast_forward_pipe,
    input logic [LOG_PRF_BANK_COUNT-1:0]            issue_A_bank,
    input logic [LOG_PR_COUNT-1:0]                  issue_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]               issue_ROB_index,

    // ready feedback to IQ
    output logic                                    issue_ready,

    // reg read data from PRF
    input logic         A_reg_read_resp_valid,
    input logic [31:0]  A_reg_read_resp_data,

    // bus forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] bus_forward_data_by_bank,

    // fast forward data
    input logic [FAST_FORWARD_PIPE_COUNT-1:0]           fast_forward_data_valid_by_pipe,
    input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0]     fast_forward_data_by_pipe,

    // writeback data to PRF
    output logic                        WB_valid,
    output logic [31:0]                 WB_data,
    output logic [LOG_PR_COUNT-1:0]     WB_PR,
    output logic [LOG_ROB_ENTRIES-1:0]  WB_ROB_index,

    // writeback backpressure from PRF
    input logic                         WB_ready,

    // this pipe's fast forward notif
    output logic                        pipe_fast_forward_notif_valid,
    output logic [LOG_PR_COUNT-1:0]     pipe_fast_forward_notif_PR,

    output logic                        pipe_fast_forward_data_valid,
    output logic [31:0]                 pipe_fast_forward_data
);
    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_WB;

    // ----------------------------------------------------------------
    // OC Stage Signals:

    logic                                       valid_OC;
    logic [3:0]                                 op_OC;
    logic [11:0]                                imm12_OC;
    logic [LOG_PR_COUNT-1:0]                    dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]                 ROB_index_OC;

    logic A_collected_OC;

    logic                           next_WB_valid;
    logic [3:0]                     next_WB_op;
    logic [11:0]                    next_WB_imm12;
    logic [LOG_PR_COUNT-1:0]        next_WB_PR;
    logic [LOG_ROB_ENTRIES-1:0]     next_WB_ROB_index;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    logic [3:0]     WB_op;
    logic [11:0]    WB_imm12;
    
    logic [31:0]    WB_A;
    logic [31:0]    WB_B;

    logic WB_first_cycle;

    // ----------------------------------------------------------------
    // Control Logic: 

    assign stall_WB = WB_valid & ~WB_ready;

    // ----------------------------------------------------------------
    // IS -> OC Buffer Logic:

    q_fast_ready #(
        .DATA_WIDTH(4 + 12 + LOG_PR_COUNT + LOG_ROB_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_op,
            issue_imm12,
            issue_dest_PR,
            issue_ROB_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            op_OC,
            imm12_OC,
            dest_PR_OC,
            ROB_index_OC
        }),
        .deq_ready(~stall_WB & A_collected_OC)
    );

    // ----------------------------------------------------------------
    // OC Stage Logic:
    
    operand_collector #(
        .OC_ENTRIES(OC_ENTRIES),
        .FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT)
    ) A_OPERAND_COLLECTOR (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid & issue_ready),
        .enq_is_reg(issue_A_is_reg),
        .enq_is_bus_forward(issue_A_is_bus_forward),
        .enq_is_fast_forward(issue_A_is_fast_forward),
        .enq_fast_forward_pipe(issue_A_fast_forward_pipe),
        .enq_bank(issue_A_bank),
        .reg_read_resp_valid(A_reg_read_resp_valid),
        .reg_read_resp_data(A_reg_read_resp_data),
        .bus_forward_data_by_bank(bus_forward_data_by_bank),
        .fast_forward_data_valid_by_pipe(fast_forward_data_valid_by_pipe),
        .fast_forward_data_by_pipe(fast_forward_data_by_pipe),
        .operand_collected(A_collected_OC),
        .operand_collected_ack(next_WB_valid & ~stall_WB),
        .operand_data(WB_A),
        .operand_data_ack(WB_valid & WB_ready)
    );
    
    always_comb begin
        next_WB_valid = valid_OC & A_collected_OC;
        next_WB_op = op_OC;
        next_WB_imm12 = imm12_OC;
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
            WB_imm12 <= 12'h0;
            WB_PR <= '0;
            WB_ROB_index <= '0;
        end
        else if (~stall_WB) begin
            WB_valid <= next_WB_valid;
            WB_op <= next_WB_op;
            WB_imm12 <= next_WB_imm12;
            WB_PR <= next_WB_PR;
            WB_ROB_index <= next_WB_ROB_index;
        end
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            WB_first_cycle <= 1'b0;
        end
        else begin
            WB_first_cycle <= next_WB_valid & ~stall_WB;
        end
    end

    // data gathering
    always_comb begin
        WB_B = {{20{WB_imm12[11]}}, WB_imm12};
    end

    // actual ALU
    alu ALU (
        .op(WB_op),
        .A(WB_A),
        .B(WB_B),
        .out(WB_data)
    );

    // this pipe's fast forward
        // passing OC -> WB
    always_comb begin
        pipe_fast_forward_notif_valid = valid_OC & (dest_PR_OC != 0);
            // always notif fast forward if in notif stage at beginning of cycle, 
                // and operand collector will be able to pick up data value when broadcasted first cycle in data stage
        pipe_fast_forward_notif_PR = dest_PR_OC;

        pipe_fast_forward_data_valid = WB_first_cycle & (WB_PR != 0);
            // must be first cycle
            // can't be last cycle as fast forward can pick up notif stage younger op forward but if there is stall it might pick up
                // later cycle where still older unwanted op still in data stage
        pipe_fast_forward_data = WB_data;
    end

endmodule