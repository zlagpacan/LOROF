/*
    Filename: stamofu_addr_pipeline.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Address Pipeline
    Spec: LOROF/spec/design/stamofu_addr_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_addr_pipeline #(
    parameter IS_OC_BUFFER_SIZE = 2,
    parameter OC_ENTRIES = IS_OC_BUFFER_SIZE + 1,
    parameter FAST_FORWARD_PIPE_COUNT = 4,
    parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // op issue from IQ
    input logic                                     issue_valid,
    input logic                                     issue_is_store,
    input logic                                     issue_is_amo,
    input logic                                     issue_is_fence,
    input logic [3:0]                               issue_op,
    input logic [11:0]                              issue_imm12,
    input logic                                     issue_A_is_reg,
    input logic                                     issue_A_is_bus_forward,
    input logic                                     issue_A_is_fast_forward,
    input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]   issue_A_fast_forward_pipe,
    input logic [LOG_PRF_BANK_COUNT-1:0]            issue_A_bank,
    input logic                                     issue_B_is_reg,
    input logic                                     issue_B_is_bus_forward,
    input logic                                     issue_B_is_fast_forward,
    input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]   issue_B_fast_forward_pipe,
    input logic [LOG_PRF_BANK_COUNT-1:0]            issue_B_bank,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]        issue_cq_index,

    // output feedback to IQ
    output logic                                    issue_ready,

    // reg read data from PRF
    input logic         A_reg_read_resp_valid,
    input logic [31:0]  A_reg_read_resp_data,
    input logic         B_reg_read_resp_valid,
    input logic [31:0]  B_reg_read_resp_data,

    // bus forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] bus_forward_data_by_bank,

    // fast forward data
    input logic [FAST_FORWARD_PIPE_COUNT-1:0]           fast_forward_data_valid_by_pipe,
    input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0]     fast_forward_data_by_pipe,

    // REQ stage info
    output logic                                REQ_valid,
    output logic                                REQ_is_store,
    output logic                                REQ_is_amo,
    output logic                                REQ_is_fence,
    output logic [3:0]                          REQ_op,
    output logic                                REQ_is_mq,
    output logic                                REQ_misaligned,
    output logic                                REQ_misaligned_exception,
    output logic [VPN_WIDTH-1:0]                REQ_VPN,
    output logic [PO_WIDTH-3:0]                 REQ_PO_word,
    output logic [3:0]                          REQ_byte_mask,
    output logic [31:0]                         REQ_write_data,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   REQ_cq_index,

    // REQ stage feedback
    input logic                                 REQ_ack
);

    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_REQ;

    // ----------------------------------------------------------------
    // OC Stage Signals:
        // Operand Collection

    logic                               valid_OC;
    logic                               is_store_OC;
    logic                               is_amo_OC;
    logic                               is_fence_OC;
    logic [3:0]                         op_OC;
    logic [11:0]                        imm12_OC;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  cq_index_OC;

    logic A_collected_OC;
    logic B_collected_OC;
    logic operands_collected_OC;

    logic                               next_REQ_valid;
    logic                               next_REQ_is_store;
    logic                               next_REQ_is_amo;
    logic                               next_REQ_is_fence;
    logic [3:0]                         next_REQ_op;
    logic [11:0]                        next_REQ_imm12;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  next_REQ_cq_index;

    // ----------------------------------------------------------------
    // REQ Stage Signals:
        // Request
        
    logic [11:0]    REQ_imm12;

    logic [31:0]    REQ_A;
    logic [31:0]    REQ_B;

    typedef enum logic [1:0] {
        REQ_IDLE,
        REQ_ACTIVE,
        REQ_MISALIGNED
    } REQ_state_t;

    REQ_state_t REQ_state, next_REQ_state;

    logic [31:0]    REQ_VA32;
    logic [31:0]    REQ_saved_VA32;
    logic [31:0]    REQ_misaligned_VA32;

    // ----------------------------------------------------------------
    // Control Logic: 

    // propagate stalls backwards
        // handle REQ stall in REQ state machine

    // ----------------------------------------------------------------
    // IS -> OC Buffer Logic:

    q_fast_ready #(
        .DATA_WIDTH(1 + 1 + 1 + 4 + 12 + LOG_LDU_CQ_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_is_store,
            issue_is_amo,
            issue_is_fence,
            issue_op,
            issue_imm12,
            issue_cq_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            is_store_OC,
            is_amo_OC,
            is_fence_OC,
            op_OC,
            imm12_OC,
            cq_index_OC
        }),
        .deq_ready(~stall_REQ & operands_ready_OC)
    );

    // ----------------------------------------------------------------
    // OC Stage Logic:

    assign operands_collected_OC = A_collected_OC & B_collected_OC;
    
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
        .operand_collected_ack(next_REQ_valid & ~stall_REQ),
        .operand_data(REQ_A),
        .operand_data_ack(REQ_valid & REQ_ack)
    );
    
    operand_collector #(
        .OC_ENTRIES(OC_ENTRIES),
        .FAST_FORWARD_PIPE_COUNT(FAST_FORWARD_PIPE_COUNT)
    ) B_OPERAND_COLLECTOR (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid & issue_ready),
        .enq_is_reg(issue_B_is_reg),
        .enq_is_bus_forward(issue_B_is_bus_forward),
        .enq_is_fast_forward(issue_B_is_fast_forward),
        .enq_fast_forward_pipe(issue_B_fast_forward_pipe),
        .enq_bank(issue_B_bank),
        .reg_read_resp_valid(B_reg_read_resp_valid),
        .reg_read_resp_data(B_reg_read_resp_data),
        .bus_forward_data_by_bank(bus_forward_data_by_bank),
        .fast_forward_data_valid_by_pipe(fast_forward_data_valid_by_pipe),
        .fast_forward_data_by_pipe(fast_forward_data_by_pipe),
        .operand_collected(B_collected_OC),
        .operand_collected_ack(next_REQ_valid & ~stall_REQ),
        .operand_data(REQ_B),
        .operand_data_ack(REQ_valid & REQ_ack)
    );
    
    always_comb begin
        next_REQ_valid = valid_OC & operands_collected_OC;
        next_REQ_is_store = is_store_OC;
        next_REQ_is_amo = is_amo_OC;
        next_REQ_is_fence = is_fence_OC;
        next_REQ_op = op_OC;
        next_REQ_imm12 = imm12_OC;
        next_REQ_cq_index = cq_index_OC;
    end

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            REQ_state <= REQ_IDLE;

            REQ_is_store <= '0;
            REQ_is_amo <= '0;
            REQ_is_fence <= '0;
            REQ_op <= '0;
            REQ_imm12 <= '0;
            REQ_cq_index <= '0;
        end
        else begin
            REQ_state <= next_REQ_state;

            if (~stall_REQ) begin
                REQ_is_store <= next_REQ_is_store;
                REQ_is_amo <= next_REQ_is_amo;
                REQ_is_fence <= next_REQ_is_fence;
                REQ_op <= next_REQ_op;
                REQ_imm12 <= next_REQ_imm12;
                REQ_cq_index <= next_REQ_cq_index;
            end
        end
    end

    // internal REQ stage blocks
    always_comb begin
        if (is_amo_OC) begin
            REQ_VA32 = REQ_A;
        end
        else begin
            REQ_VA32 = REQ_A + {{20{REQ_imm12[11]}}, REQ_imm12};
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            REQ_saved_VA32 <= 32'h0;
        end
        else begin
            REQ_saved_VA32 <= REQ_VA32;
        end
    end

    assign REQ_misaligned_VA32 = REQ_saved_VA32 + 32'h4;

    always_comb begin

        if (REQ_is_store) begin

            // SW
            if (REQ_op[1]) begin

                // anything not word-aligned is misaligned
                REQ_misaligned = REQ_VA32[1:0] != 2'b00;

                // check first cycle
                if (REQ_state != REQ_MISALIGNED) begin
                    case (REQ_VA32[1:0]) 
                        2'b00:  REQ_byte_mask = 4'b1111;
                        2'b01:  REQ_byte_mask = 4'b1110;
                        2'b10:  REQ_byte_mask = 4'b1100;
                        2'b11:  REQ_byte_mask = 4'b1000;
                    endcase
                end

                // check misaligned cycle
                else begin
                    case (REQ_VA32[1:0])
                        2'b00:  REQ_byte_mask = 4'b0000;
                        2'b01:  REQ_byte_mask = 4'b0001;
                        2'b10:  REQ_byte_mask = 4'b0011;
                        2'b11:  REQ_byte_mask = 4'b0111;
                    endcase
                end
            end

            // SH
            else if (REQ_op[0]) begin

                // only 0x3->0x0 is misaligned
                REQ_misaligned = REQ_VA32[1:0] == 2'b11;

                // check first cycle
                if (REQ_state != REQ_MISALIGNED) begin
                    case (REQ_VA32[1:0]) 
                        2'b00:  REQ_byte_mask = 4'b0011;
                        2'b01:  REQ_byte_mask = 4'b0110;
                        2'b10:  REQ_byte_mask = 4'b1100;
                        2'b11:  REQ_byte_mask = 4'b1000;
                    endcase
                end

                // check misaligned cycle
                else begin
                    // guaranteed in 2'b11 case
                    REQ_byte_mask = 4'b0001;
                end
            end

            // SB
            else begin
                REQ_misaligned = 1'b0;

                // guaranteed not misaligned
                case (REQ_VA32[1:0]) 
                    2'b00:  REQ_byte_mask = 4'b0001;
                    2'b01:  REQ_byte_mask = 4'b0010;
                    2'b10:  REQ_byte_mask = 4'b0100;
                    2'b11:  REQ_byte_mask = 4'b1000;
                endcase
            end
        end
        
        else if (REQ_is_amo) begin
            // REQ misaligned exception is separately checked for AMO's
            REQ_misaligned = 1'b0;

            // keep OG byte mask encoding so can use for misaligned exception synthesis of VA
            case (REQ_VA32[1:0])
                2'b00:  REQ_byte_mask = 4'b1111;
                2'b01:  REQ_byte_mask = 4'b1110;
                2'b10:  REQ_byte_mask = 4'b1100;
                2'b11:  REQ_byte_mask = 4'b1000;
            endcase
        end

        else begin
            // fence guaranteed not misaligned
            REQ_misaligned = 1'b0;

            // default
            case (REQ_VA32[1:0])
                2'b00:  REQ_byte_mask = 4'b1111;
                2'b01:  REQ_byte_mask = 4'b1110;
                2'b10:  REQ_byte_mask = 4'b1100;
                2'b11:  REQ_byte_mask = 4'b1000;
            endcase
        end
    end

    always_comb begin
        case (REQ_VA32[1:0])
            2'b00:  REQ_write_data = REQ_B;
            2'b01:  REQ_write_data = {REQ_B[23:0], REQ_B[31:24]};
            2'b10:  REQ_write_data = {REQ_B[15:0], REQ_B[31:16]};
            2'b11:  REQ_write_data = {REQ_B[7:0], REQ_B[31:8]};
        endcase
    end

    // any amo not word-aligned is misaligned
    assign REQ_misaligned_exception = REQ_is_amo & (REQ_VA32[1:0] != 2'b00);

    // REQ state machine
    always_comb begin

        stall_REQ = 1'b0;

        REQ_valid = 1'b0;
        REQ_is_mq = 1'b0;
        REQ_VPN = REQ_VA32[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];
        REQ_PO_word = REQ_VA32[31-VPN_WIDTH:32-VPN_WIDTH-PO_WIDTH+2];
        
        next_REQ_state = REQ_ACTIVE;

        case (REQ_state)

            REQ_IDLE:
            begin
                stall_REQ = 1'b0;

                REQ_valid = 1'b0;
                REQ_is_mq = 1'b0;
                REQ_VPN = REQ_VA32[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];
                REQ_PO_word = REQ_VA32[31-VPN_WIDTH:32-VPN_WIDTH-PO_WIDTH+2];

                if (next_REQ_valid) begin
                    next_REQ_state = REQ_ACTIVE;
                end
                else begin
                    next_REQ_state = REQ_IDLE;
                end
            end

            REQ_ACTIVE:
            begin
                REQ_valid = 1'b1;
                REQ_is_mq = 1'b0;
                REQ_VPN = REQ_VA32[31:32-VPN_WIDTH];
                REQ_PO_word = REQ_VA32[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];

                if (REQ_ack & REQ_misaligned & ~REQ_misaligned_exception) begin
                    stall_REQ = 1'b1;

                    next_REQ_state = REQ_MISALIGNED;
                end
                else if ((REQ_ack & ~REQ_misaligned) | REQ_misaligned_exception) begin
                    stall_REQ = 1'b0;
                    
                    if (next_REQ_valid) begin
                        next_REQ_state = REQ_ACTIVE;
                    end
                    else begin
                        next_REQ_state = REQ_IDLE;
                    end
                end
                else begin
                    stall_REQ = 1'b1;

                    next_REQ_state = REQ_ACTIVE;
                end
            end

            REQ_MISALIGNED:
            begin
                REQ_valid = 1'b1;
                REQ_is_mq = 1'b1;
                REQ_VPN = REQ_misaligned_VA32[31:32-VPN_WIDTH];
                REQ_PO_word = REQ_misaligned_VA32[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];

                if (REQ_ack) begin
                    stall_REQ = 1'b0;

                    if (next_REQ_valid) begin
                        next_REQ_state = REQ_ACTIVE;
                    end
                    else begin
                        next_REQ_state = REQ_IDLE;
                    end
                end
                else begin
                    stall_REQ = 1'b1;

                    next_REQ_state = REQ_MISALIGNED;
                end
            end

        endcase
    end

endmodule