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
    parameter PRF_RR_OUTPUT_BUFFER_SIZE = 3
) (

    // seq
    input logic CLK,
    input logic nRST,

    // op issue from IQ
    input logic                                 issue_valid,
    input logic                                 issue_is_store,
    input logic                                 issue_is_amo,
    input logic                                 issue_is_fence,
    input logic [3:0]                           issue_op,
    input logic [11:0]                          issue_imm12,
    input logic                                 issue_A_forward,
    input logic                                 issue_A_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_A_bank,
    input logic                                 issue_B_forward,
    input logic                                 issue_B_is_zero,
    input logic [LOG_PRF_BANK_COUNT-1:0]        issue_B_bank,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    issue_cq_index,

    // output feedback to IQ
    output logic                                issue_ready,

    // reg read data from PRF
    input logic         A_reg_read_resp_valid,
    input logic [31:0]  A_reg_read_resp_data,
    input logic         B_reg_read_resp_valid,
    input logic [31:0]  B_reg_read_resp_data,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,

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
    logic                               A_forward_OC;
    logic                               A_is_reg_OC;
    logic                               B_forward_OC;
    logic                               B_is_reg_OC;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  cq_index_OC;

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

    logic                               next_REQ_valid;
    logic                               next_REQ_is_store;
    logic                               next_REQ_is_amo;
    logic                               next_REQ_is_fence;
    logic [3:0]                         next_REQ_op;
    logic [11:0]                        next_REQ_imm12;
    logic                               next_REQ_A_forward;
    logic                               next_REQ_A_is_reg;
    logic                               next_REQ_B_forward;
    logic                               next_REQ_B_is_reg;
    logic [LOG_STAMOFU_CQ_ENTRIES-1:0]  next_REQ_cq_index;

    // ----------------------------------------------------------------
    // REQ Stage Signals:
        // Request
        
    logic [11:0]    REQ_imm12;
    logic           REQ_A_forward;
    logic           REQ_A_is_reg;
    logic           REQ_B_forward;
    logic           REQ_B_is_reg;

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
        .DATA_WIDTH(1 + 1 + 1 + 4 + 12 + 1 + 1 + 1 + 1 + LOG_LDU_CQ_ENTRIES),
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
            issue_A_forward,
            ~(issue_A_forward | issue_A_is_zero),
            issue_B_forward,
            ~(issue_B_forward | issue_B_is_zero),
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
            A_forward_OC,
            A_is_reg_OC,
            B_forward_OC,
            B_is_reg_OC,
            cq_index_OC
        }),
        .deq_ready(~stall_REQ & operands_ready_OC)
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
        next_REQ_valid = valid_OC & operands_ready_OC;
        next_REQ_is_store = is_store_OC;
        next_REQ_is_amo = is_amo_OC;
        next_REQ_is_fence = is_fence_OC;
        next_REQ_op = op_OC;
        next_REQ_imm12 = imm12_OC;
        next_REQ_A_forward = A_forward_OC;
        next_REQ_A_is_reg = A_is_reg_OC;
        next_REQ_B_forward = B_forward_OC;
        next_REQ_B_is_reg = B_is_reg_OC;
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
            REQ_A_forward <= 1'b0;
            REQ_A_is_reg <= 1'b0;
            REQ_B_forward <= 1'b0;
            REQ_B_is_reg <= 1'b0;
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
                REQ_A_forward <= next_REQ_A_forward;
                REQ_A_is_reg <= next_REQ_A_is_reg;
                REQ_B_forward <= next_REQ_B_forward;
                REQ_B_is_reg <= next_REQ_B_is_reg;
                REQ_cq_index <= next_REQ_cq_index;
            end
        end
    end

    // data gathering
    always_comb begin
        REQ_A = ({32{REQ_A_is_reg}} & deq_A_reg_data) | ({32{REQ_A_forward}} & deq_A_forward_data);
        REQ_B = ({32{REQ_B_is_reg}} & deq_B_reg_data) | ({32{REQ_B_forward}} & deq_B_forward_data);

        deq_A_reg_ready = REQ_valid & REQ_A_is_reg & ~stall_REQ;
        deq_A_forward_ready = REQ_valid & REQ_A_forward & ~stall_REQ;
        
        deq_B_reg_ready = REQ_valid & REQ_B_is_reg & ~stall_REQ;
        deq_B_forward_ready = REQ_valid & REQ_B_forward & ~stall_REQ;
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