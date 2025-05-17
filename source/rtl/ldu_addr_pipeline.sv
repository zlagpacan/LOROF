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

module ldu_addr_pipeline (

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

    // reg read info and data from PRF
    input logic                                     A_reg_read_ack,
    input logic                                     A_reg_read_port,
    input logic [PRF_BANK_COUNT-1:0][1:0][31:0]     reg_read_data_by_bank_by_port,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank,
    
    // REQ stage info
    output logic                            REQ_valid,
    output logic                            REQ_misaligned,
    output logic [VPN_WIDTH-1:0]            REQ_VPN,
    output logic [PO_WIDTH-3:0]             REQ_PO_word,
    output logic [3:0]                      REQ_byte_mask,
    output logic [LOG_LDU_CQ_ENTRIES-1:0]   REQ_cq_index,

    // REQ stage feedback
    input logic                             REQ_ack
);

    // ----------------------------------------------------------------
    // Control Signals: 

    logic stall_REQ;
    logic stall_AC;
    logic stall_OC;

    // ----------------------------------------------------------------
    // OC Stage Signals:
        // Operand Collection

    logic                           valid_OC;
    logic [3:0]                     op_OC;
    logic [11:0]                    imm12_OC;
    logic                           A_saved_OC;
    logic                           A_forward_OC;
    logic                           A_is_zero_OC;
    logic [LOG_PRF_BANK_COUNT-1:0]  A_bank_OC;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  cq_index_OC;

    logic [31:0]    A_saved_data_OC;

    logic launch_ready_OC;

    logic                           next_valid_AC;
    logic [3:0]                     next_op_AC;
    logic [11:0]                    next_imm12_AC;
    logic [31:0]                    next_A_AC;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  next_cq_index_AC;

    // ----------------------------------------------------------------
    // AC Stage Signals:
        // Address Calculation

    logic [3:0]                     op_AC;
    logic [11:0]                    imm12_AC;
    logic [31:0]                    A_AC;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  cq_index_AC;

    typedef enum logic [1:0] {
        AC_IDLE,
        AC_ACTIVE,
        AC_MISALIGNED
    } state_AC_t;

    state_AC_t state_AC, next_state_AC;

    logic [31:0]    VA32_AC;
    logic           detected_misaligned_AC;

    logic [31:0] saved_VA32_AC;
    logic [31:0] misaligned_VA32_AC;

    logic                           next_REQ_valid;
    logic                           next_REQ_misaligned;
    logic [VPN_WIDTH-1:0]           next_REQ_VPN;
    logic [(PO_WIDTH-2)-1:0]        next_REQ_PO_word;
    logic [3:0]                     next_REQ_byte_mask;
    logic [LOG_LDU_CQ_ENTRIES-1:0]  next_REQ_cq_index;

    // ----------------------------------------------------------------
    // REQ Stage Signals:
        // Request

    // ----------------------------------------------------------------
    // Control Logic: 

    // propagate stalls backwards
    assign stall_REQ = REQ_valid & ~REQ_ack;
    // assign stall_AC = (state_AC != AC_IDLE) & stall_REQ;
        // must be done in AC state machine so can take into account misaligned op insertion
    assign stall_OC = valid_OC & stall_AC;

    // ----------------------------------------------------------------
    // OC Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_OC <= '0;
            op_OC <= '0;
            imm12_OC <= '0;
            A_saved_OC <= '0;
            A_forward_OC <= '0;
            A_is_zero_OC <= '0;
            A_bank_OC <= '0;
            A_saved_data_OC <= '0;
            cq_index_OC <= '0;
        end
        else if (~issue_ready) begin
            valid_OC <= valid_OC;
            op_OC <= op_OC;
            imm12_OC <= imm12_OC;
            A_saved_OC <= A_saved_OC | A_forward_OC | A_reg_read_ack;
            A_forward_OC <= A_forward_OC;
            A_is_zero_OC <= A_is_zero_OC;
            A_bank_OC <= A_bank_OC;
            A_saved_data_OC <= next_A_AC;
            cq_index_OC <= cq_index_OC;
        end
        else begin
            valid_OC <= issue_valid;
            op_OC <= issue_op;
            imm12_OC <= issue_imm12;
            A_saved_OC <= 1'b0;
            A_forward_OC <= issue_A_forward;
            A_is_zero_OC <= issue_A_is_zero;
            A_bank_OC <= issue_A_bank;
            A_saved_data_OC <= next_A_AC;
            cq_index_OC <= issue_cq_index;
        end
    end

    assign launch_ready_OC = 
        // no backpressure
        ~stall_OC
        // A operand present
        & (A_is_zero_OC | A_saved_OC | A_forward_OC | A_reg_read_ack);
    
    assign issue_ready = ~valid_OC | launch_ready_OC;

    assign next_valid_AC = valid_OC & launch_ready_OC;
    assign next_op_AC = op_OC;
    assign next_imm12_AC = imm12_OC;
    assign next_cq_index_AC = cq_index_OC;

    // A operand collection
    always_comb begin

        // collect A value to save OR pass to AC
        if (A_is_zero_OC) begin
            next_A_AC = 32'h0;
        end
        else if (A_saved_OC) begin
            next_A_AC = A_saved_data_OC;
        end
        else if (A_forward_OC) begin
            next_A_AC = forward_data_by_bank[A_bank_OC];
        end
        else begin
            next_A_AC = reg_read_data_by_bank_by_port[A_bank_OC][A_reg_read_port];
        end
    end

    // ----------------------------------------------------------------
    // AC Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            state_AC <= AC_IDLE;
            op_AC <= '0;
            imm12_AC <= '0;
            A_AC <= '0;
            cq_index_AC <= '0;
        end
        else begin
            state_AC <= next_state_AC;

            if (~stall_AC) begin
                op_AC <= next_op_AC;
                imm12_AC <= next_imm12_AC;
                A_AC <= next_A_AC;
                cq_index_AC <= next_cq_index_AC;
            end
        end
    end

    // pass-through's:
    assign next_REQ_cq_index = cq_index_AC;

    // internal AC stage blocks
    assign VA32_AC = A_AC + {20'h0, imm12_AC};

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            saved_VA32_AC <= 32'h0;
        end
        else begin
            saved_VA32_AC <= VA32_AC;
        end
    end

    assign misaligned_VA32_AC = saved_VA32_AC + 32'h4;

    always_comb begin
        
        // LW
        if (op_AC[1]) begin

            // anything not word-aligned is misaligned
            detected_misaligned_AC = VA32_AC[1:0] != 2'b00;

            // check first cycle
            if (state_AC != AC_MISALIGNED) begin
                case (VA32_AC[1:0]) 
                    2'b00:  next_REQ_byte_mask = 4'b1111;
                    2'b01:  next_REQ_byte_mask = 4'b1110;
                    2'b10:  next_REQ_byte_mask = 4'b1100;
                    2'b11:  next_REQ_byte_mask = 4'b1000;
                endcase
            end

            // check misaligned cycle
            else begin
                case (VA32_AC[1:0])
                    2'b00:  next_REQ_byte_mask = 4'b0000;
                    2'b01:  next_REQ_byte_mask = 4'b0001;
                    2'b10:  next_REQ_byte_mask = 4'b0011;
                    2'b11:  next_REQ_byte_mask = 4'b0111;
                endcase
            end
        end

        // LH, LHU
        else if (op_AC[0]) begin

            // only 0x3->0x0 is misaligned
            detected_misaligned_AC = VA32_AC[1:0] == 2'b11;

            // check first cycle
            if (state_AC != AC_MISALIGNED) begin
                case (VA32_AC[1:0]) 
                    2'b00:  next_REQ_byte_mask = 4'b0011;
                    2'b01:  next_REQ_byte_mask = 4'b0110;
                    2'b10:  next_REQ_byte_mask = 4'b1100;
                    2'b11:  next_REQ_byte_mask = 4'b1000;
                endcase
            end

            // check misaligned cycle
            else begin
                // guaranteed in 2'b11 case
                next_REQ_byte_mask = 4'b0001;
            end
        end

        // LB, LBU
        else begin
            detected_misaligned_AC = 1'b0;

            // guaranteed not misaligned
            case (VA32_AC[1:0]) 
                2'b00:  next_REQ_byte_mask = 4'b0001;
                2'b01:  next_REQ_byte_mask = 4'b0010;
                2'b10:  next_REQ_byte_mask = 4'b0100;
                2'b11:  next_REQ_byte_mask = 4'b1000;
            endcase
        end
    end

    // AC state machine
    always_comb begin

        stall_AC = 1'b0;

        next_REQ_valid = 1'b0;
        next_REQ_misaligned = 1'b0;
        next_REQ_VPN = VA32_AC[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];
        next_REQ_PO_word = VA32_AC[31-VPN_WIDTH:32-VPN_WIDTH-PO_WIDTH+2];
        next_state_AC = AC_ACTIVE;

        case (state_AC)

            AC_IDLE:
            begin
                stall_AC = 1'b0;

                next_REQ_valid = 1'b0;
                next_REQ_misaligned = 1'b0;
                next_REQ_VPN = VA32_AC[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];
                next_REQ_PO_word = VA32_AC[31-VPN_WIDTH:32-VPN_WIDTH-PO_WIDTH+2];

                if (next_valid_AC) begin
                    next_state_AC = AC_ACTIVE;
                end
                else begin
                    next_state_AC = AC_IDLE;
                end
            end

            AC_ACTIVE:
            begin
                next_REQ_valid = 1'b1;
                next_REQ_misaligned = 1'b0;
                next_REQ_VPN = VA32_AC[31:32-VPN_WIDTH];
                next_REQ_PO_word = VA32_AC[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];

                if (~stall_REQ & detected_misaligned_AC) begin
                    stall_AC = 1'b1;

                    next_state_AC = AC_MISALIGNED;
                end
                else if (~stall_REQ & ~detected_misaligned_AC) begin
                    stall_AC = 1'b0;
                    
                    if (next_valid_AC) begin
                        next_state_AC = AC_ACTIVE;
                    end
                    else begin
                        next_state_AC = AC_IDLE;
                    end
                end
                else begin
                    stall_AC = 1'b1;

                    next_state_AC = AC_ACTIVE;
                end
            end

            AC_MISALIGNED:
            begin
                next_REQ_valid = 1'b1;
                next_REQ_misaligned = 1'b1;
                next_REQ_VPN = misaligned_VA32_AC[31:32-VPN_WIDTH];
                next_REQ_PO_word = misaligned_VA32_AC[31-VPN_WIDTH:32-VPN_WIDTH-(PO_WIDTH-2)];

                if (~stall_REQ) begin
                    stall_AC = 1'b0;
                    if (next_valid_AC) begin
                        next_state_AC = AC_ACTIVE;
                    end
                    else begin
                        next_state_AC = AC_IDLE;
                    end
                end
                else begin
                    stall_AC = 1'b1;
                    next_state_AC = AC_MISALIGNED;
                end
            end

        endcase
    end

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            REQ_valid <= '0;
            REQ_misaligned <= '0;
            REQ_VPN <= '0;
            REQ_PO_word <= '0;
            REQ_byte_mask <= '0;
            REQ_cq_index <= '0;
        end
        else if (~stall_REQ) begin
            REQ_valid <= next_REQ_valid;
            REQ_misaligned <= next_REQ_misaligned;
            REQ_VPN <= next_REQ_VPN;
            REQ_PO_word <= next_REQ_PO_word;
            REQ_byte_mask <= next_REQ_byte_mask;
            REQ_cq_index <= next_REQ_cq_index;
        end
    end

endmodule