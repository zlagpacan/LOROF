/*
    Filename: ldu_addr_pipeline.sv
    Author: zlagpacan
    Description: RTL for Load Unit Address Pipeline
    Spec: LOROF/spec/design/ldu_addr_pipeline.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module ldu_addr_pipeline #(
    parameter IS_OC_BUFFER_SIZE = 2,
    parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3
) (

    // seq
    input logic CLK,
    input logic nRST,

    // op issue from IQ
    input logic                             issue_valid,
    input logic [3:0]                       issue_op,
    input logic [11:0]                      issue_imm12,
    input logic                             issue_A_forward,
    input logic                             issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]    issue_A_bank,
    input logic [LOG_LDU_CQ_ENTRIES-1:0]    issue_cq_index,

    // output feedback to IQ
    output logic                            issue_ready,

    // reg read data from PRF
    input logic         A_reg_read_resp_valid,
    input logic [31:0]  A_reg_read_resp_data,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,
    
    // REQ stage info
    output logic                            REQ_bank0_valid,
    output logic                            REQ_bank1_valid,

    output logic                            REQ_is_mq,
    output logic                            REQ_misaligned,
    output logic [VPN_WIDTH-1:0]            REQ_VPN,
    output logic [PO_WIDTH-3:0]             REQ_PO_word,
    output logic [3:0]                      REQ_byte_mask,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   REQ_cq_index,

    // REQ stage feedback
    input logic                             REQ_bank0_early_ready,
    input logic                             REQ_bank1_early_ready
);

    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_REQ;

    // ----------------------------------------------------------------
    // OC Stage Signals:
        // Operand Collection

    logic                           valid_OC;
    logic [3:0]                     op_OC;
    logic [11:0]                    imm12_OC;
    logic                           A_forward_OC;
    logic                           A_is_reg_OC;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  cq_index_OC;

    logic operands_ready_OC;

    logic           enq_A_reg_valid;
    logic [31:0]    enq_A_reg_data;
    // logic           enq_A_reg_ready; // should always be 1
    logic           deq_A_reg_valid;
    logic [31:0]    deq_A_reg_data;
    logic           deq_A_reg_ready;

    logic [LOG_PRF_BANK_COUNT-1:0]  enq_A_forward_bank;

    logic           enq_A_forward_valid;
    logic [31:0]    enq_A_forward_data;
    // logic           enq_A_forward_ready; // should always be 1
    logic           deq_A_forward_valid;
    logic [31:0]    deq_A_forward_data;
    logic           deq_A_forward_ready;

    logic                           next_REQ_valid;
    logic [3:0]                     next_REQ_op;
    logic [11:0]                    next_REQ_imm12;
    logic                           next_REQ_A_forward;
    logic                           next_REQ_A_is_reg;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  next_REQ_cq_index;

    // ----------------------------------------------------------------
    // REQ Stage Signals:
        // Request

    logic           REQ_valid;

    logic [3:0]     REQ_op;
    logic [11:0]    REQ_imm12;
    logic           REQ_A_forward;
    logic           REQ_A_is_reg;

    logic [31:0]    REQ_A;

    logic           REQ_ack;

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
        .DATA_WIDTH(4 + 12 + 1 + 1 + LOG_LDU_CQ_ENTRIES),
        .NUM_ENTRIES(IS_OC_BUFFER_SIZE)
    ) IS_OC_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(issue_valid),
        .enq_data({
            issue_op,
            issue_imm12,
            issue_A_forward,
            ~(issue_A_forward | issue_A_is_zero),
            issue_cq_index
        }),
        .enq_ready(issue_ready),
        .deq_valid(valid_OC),
        .deq_data({
            op_OC,
            imm12_OC,
            A_forward_OC,
            A_is_reg_OC,
            cq_index_OC
        }),
        .deq_ready(~stall_REQ & operands_ready_OC)
    );

    // ----------------------------------------------------------------
    // OC Stage Logic:

    assign operands_ready_OC = 
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

    // forward data buffers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            enq_A_forward_valid <= 1'b0;
            enq_A_forward_bank <= 0;
        end
        else begin
            enq_A_forward_valid <= issue_valid & issue_ready & issue_A_forward;
            enq_A_forward_bank <= issue_A_bank;
        end
    end

    always_comb begin
        enq_A_forward_data = forward_data_by_bank[enq_A_forward_bank];
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
    
    always_comb begin
        next_REQ_valid = valid_OC & operands_ready_OC;
        next_REQ_op = op_OC;
        next_REQ_imm12 = imm12_OC;
        next_REQ_A_forward = A_forward_OC;
        next_REQ_A_is_reg = A_is_reg_OC;
        next_REQ_cq_index = cq_index_OC;
    end

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            REQ_state <= REQ_IDLE;
            REQ_op <= '0;
            REQ_imm12 <= '0;
            REQ_A_forward <= 1'b0;
            REQ_A_is_reg <= 1'b0;
            REQ_cq_index <= '0;
        end
        else begin
            REQ_state <= next_REQ_state;

            if (~stall_REQ) begin
                REQ_op <= next_REQ_op;
                REQ_imm12 <= next_REQ_imm12;
                REQ_A_forward <= next_REQ_A_forward;
                REQ_A_is_reg <= next_REQ_A_is_reg;
                REQ_cq_index <= next_REQ_cq_index;
            end
        end
    end

    // data gathering
    always_comb begin
        REQ_A = ({32{REQ_A_is_reg}} & deq_A_reg_data) | ({32{REQ_A_forward}} & deq_A_forward_data);

        deq_A_reg_ready = REQ_valid & REQ_A_is_reg & ~stall_REQ;
        deq_A_forward_ready = REQ_valid & REQ_A_forward & ~stall_REQ;
    end

    // internal REQ stage blocks
    assign REQ_VA32 = REQ_A + {{20{REQ_imm12[11]}}, REQ_imm12};

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
        
        // LW
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

        // LH, LHU
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

        // LB, LBU
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

                if (REQ_ack & REQ_misaligned) begin
                    stall_REQ = 1'b1;

                    next_REQ_state = REQ_MISALIGNED;
                end
                else if (REQ_ack & ~REQ_misaligned) begin
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

    assign REQ_bank0_valid = REQ_valid & (REQ_PO_word[DCACHE_WORD_ADDR_BANK_BIT] == 1'b0);
    assign REQ_bank1_valid = REQ_valid & (REQ_PO_word[DCACHE_WORD_ADDR_BANK_BIT] == 1'b1);

    assign REQ_ack = REQ_bank0_early_ready & REQ_bank1_early_ready;
        // be careful for perf hit here, where can't move around a slow bank since both banks must be ready
        // actually this prolly fine since on MSHR fill-up, both banks will be stalled
        // only source of specific bank stall is on WB, exception, or mispred stall
            // WB stalls may be common 

endmodule