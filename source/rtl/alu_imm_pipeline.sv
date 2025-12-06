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
    parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3,
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
    input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0] fast_forward_data_by_pipe,

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
    logic                                       A_is_reg_OC;
    logic                                       A_is_bus_forward_OC;
    logic                                       A_is_fast_forward_OC;
    logic [LOG_PR_COUNT-1:0]                    dest_PR_OC;
    logic [LOG_ROB_ENTRIES-1:0]                 ROB_index_OC;

    logic operands_collected_OC;

    logic           enq_A_reg_valid;
    logic [31:0]    enq_A_reg_data;
    // logic           enq_A_reg_ready; // should always be 1
    logic           deq_A_reg_valid;
    logic [31:0]    deq_A_reg_data;
    logic           deq_A_reg_ready;

    logic [LOG_PRF_BANK_COUNT-1:0]  enq_A_bus_forward_bank;

    logic           enq_A_bus_forward_valid;
    logic [31:0]    enq_A_bus_forward_data;
    // logic           enq_A_bus_forward_ready; // should always be 1
    logic           deq_A_bus_forward_valid;
    logic [31:0]    deq_A_bus_forward_data;
    logic           deq_A_bus_forward_ready;

    logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0] enq_A_fast_forward_pipe;

    logic           enq_A_fast_forward_valid;
    logic [31:0]    enq_A_fast_forward_data;
    // logic           enq_A_fast_forward_ready; // should always be 1
    logic           deq_A_fast_forward_valid;
    logic [31:0]    deq_A_fast_forward_data;
    logic           deq_A_fast_forward_ready;

    logic                           next_WB_valid;
    logic [3:0]                     next_WB_op;
    logic [11:0]                    next_WB_imm12;
    logic                           next_WB_A_is_reg;
    logic                           next_WB_A_is_bus_forward;
    logic                           next_WB_A_is_fast_forward;
    logic [LOG_PR_COUNT-1:0]        next_WB_PR;
    logic [LOG_ROB_ENTRIES-1:0]     next_WB_ROB_index;

    // ----------------------------------------------------------------
    // WB Stage Signals:

    logic [3:0]     WB_op;
    logic [11:0]    WB_imm12;
    logic           WB_A_is_reg;
    logic           WB_A_is_bus_forward;
    logic           WB_A_is_fast_forward;
    
    logic [31:0]    WB_A;
    logic [31:0]    WB_B;

    // ----------------------------------------------------------------
    // Control Logic: 

    assign stall_WB = WB_valid & ~WB_ready;

    // ----------------------------------------------------------------
    // IS -> OC Buffer Logic:

    q_fast_ready #(
        .DATA_WIDTH(4 + 12 + 1 + 1 + 1 + LOG_PR_COUNT + LOG_ROB_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_op,
            issue_imm12,
            issue_A_is_reg,
            issue_A_is_bus_forward,
            issue_A_is_fast_forward,
            issue_dest_PR,
            issue_ROB_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            op_OC,
            imm12_OC,
            A_is_reg_OC,
            A_is_bus_forward_OC,
            A_is_fast_forward_OC,
            dest_PR_OC,
            ROB_index_OC
        }),
        .deq_ready(~stall_WB & operands_collected_OC)
    );

    // ----------------------------------------------------------------
    // OC Stage Logic:

    assign operands_collected_OC = 
        // A operand present
        (~A_is_reg_OC | A_reg_read_resp_valid | deq_A_reg_valid)
    ;

    // reg read data buffers:

    always_comb begin
        enq_A_reg_valid = A_reg_read_resp_valid;
        enq_A_reg_data = A_reg_read_resp_data;
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

    // bus forward data buffers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            enq_A_bus_forward_valid <= 1'b0;
            enq_A_bus_forward_bank <= 0;
        end
        else begin
            enq_A_bus_forward_valid <= issue_valid & issue_ready & issue_A_is_bus_forward;
            enq_A_bus_forward_bank <= issue_A_bank;
        end
    end

    always_comb begin
        enq_A_bus_forward_data = bus_forward_data_by_bank[enq_A_bus_forward_bank];
    end

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) A_BUS_FORWARD_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_A_bus_forward_valid),
        .enq_data(enq_A_bus_forward_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_A_bus_forward_valid),
        .deq_data(deq_A_bus_forward_data),
        .deq_ready(deq_A_bus_forward_ready)
    );

    // fast forward data buffers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            enq_A_fast_forward_valid <= 1'b0;
            enq_A_fast_forward_pipe <= 0;
        end
        else begin
            enq_A_fast_forward_valid <= issue_valid & issue_ready & issue_A_is_fast_forward;
            enq_A_fast_forward_pipe <= issue_A_fast_forward_pipe;
        end
    end

    always_comb begin
        enq_A_fast_forward_data = fast_forward_data_by_pipe[enq_A_fast_forward_pipe];
    end

    q_fast_ready #(
        .DATA_WIDTH(32),
        .NUM_ENTRIES(PRF_RR_OUTPUT_BUFFER_SIZE)
    ) A_FAST_FORWARD_DATA_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(enq_A_fast_forward_valid),
        .enq_data(enq_A_fast_forward_data),
        .enq_ready(), // should always be 1
        .deq_valid(deq_A_fast_forward_valid),
        .deq_data(deq_A_fast_forward_data),
        .deq_ready(deq_A_fast_forward_ready)
    );
    
    always_comb begin
        next_WB_valid = valid_OC & operands_collected_OC;
        next_WB_op = op_OC;
        next_WB_imm12 = imm12_OC;
        next_WB_A_is_reg = A_is_reg_OC;
        next_WB_A_is_bus_forward = A_is_bus_forward_OC;
        next_WB_A_is_fast_forward = A_is_fast_forward_OC;
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
            WB_A_is_reg <= 1'b0;
            WB_A_is_bus_forward <= 1'b0;
            WB_A_is_fast_forward <= 1'b0;
            WB_PR <= '0;
            WB_ROB_index <= '0;
        end
        else if (~stall_WB) begin
            WB_valid <= next_WB_valid;
            WB_op <= next_WB_op;
            WB_imm12 <= next_WB_imm12;
            WB_A_is_reg <= next_WB_A_is_reg;
            WB_A_is_bus_forward <= next_WB_A_is_bus_forward;
            WB_A_is_fast_forward <= next_WB_A_is_fast_forward;
            WB_PR <= next_WB_PR;
            WB_ROB_index <= next_WB_ROB_index;
        end
    end

    // data gathering
    always_comb begin
        WB_A = ({32{WB_A_is_reg}} & deq_A_reg_data) | ({32{WB_A_is_bus_forward}} & deq_A_bus_forward_data) | ({32{WB_A_is_fast_forward}} & deq_A_fast_forward_data);

        deq_A_reg_ready = WB_valid & WB_A_is_reg & WB_ready;
        deq_A_bus_forward_ready = WB_valid & WB_A_is_bus_forward & WB_ready;
        deq_A_fast_forward_ready = WB_valid & WB_A_is_fast_forward & WB_ready;

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
        pipe_fast_forward_notif_valid = valid_OC & operands_collected_OC & ~stall_WB;
            // from OC stage
            // potential issue w/ long comb path
                // have to wait on prf rr arbitration to know if stalled before can even start IQ arbitration
                // path:
                    // prf rr -> operands_collected_OC -> fast forward valid -> IQ arbitration's -> pipe issue's
                // for simplicity would want this as operands_collected_OC tells if guaranteed have data next cycle
                // maybe this not a big deal now that have buffer-based prf to split path
                // maybe not that different from old crit path:
                    // bus forward's -> IQ arbitration's -> prf rr
                    // may be pretty bad path compared to rest of buffer-based prf version now
                // solutions:
                    // delay fast forward by 1 cycle
                        // fast forwarding loses 1 cycle of crucial efficiency, especially for all the effort (gets closer to just bus forward)
                    // only do fast forward in pipelines where cycle before WB data is known early in stage before
                        // only works for LDU bank 0, LDU bank 1
                    // lengthen problem pipelines so cycle before WB data is known early in stage before
                        // would have to lengthen alu reg, alu imm

        pipe_fast_forward_notif_PR = next_WB_PR;
            // from OC stage

        pipe_fast_forward_data_valid = WB_valid;
            // TODO: need to fix this to be first cycle
                // can't be last cycle as fast forward can pick up OC stage younger op forward but if there is stall it might pick up
                    // later cycle where still older unwanted op still in WB stage
        pipe_fast_forward_data = WB_data;
            // from WB stage
    end

endmodule