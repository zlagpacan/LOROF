/*
    Filename: stamofu_lq.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Launch Queue
    Spec: LOROF/spec/design/stamofu_lq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_lq #(
    parameter STAMOFU_LQ_ENTRIES_PER_BANK = 2
) (
    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage enq info
    input logic                                 REQ_enq_valid,
    input logic                                 REQ_enq_is_store,
    input logic                                 REQ_enq_is_amo,
    input logic                                 REQ_enq_is_fence,
    input logic [3:0]                           REQ_enq_op,
    input logic                                 REQ_enq_is_mq,
    input logic                                 REQ_enq_misaligned,
    input logic                                 REQ_enq_misaligned_exception,
    input logic [VPN_WIDTH-1:0]                 REQ_enq_VPN,
    input logic [PO_WIDTH-3:0]                  REQ_enq_PO_word,
    input logic [3:0]                           REQ_enq_byte_mask,
    input logic [31:0]                          REQ_enq_write_data,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    REQ_enq_cq_index,

    // REQ stage enq feedback
    output logic                                REQ_enq_ack,

    // REQ stage deq info bank 0
    output logic                                REQ_deq_bank0_valid,

    output logic                                REQ_deq_bank0_is_store,
    output logic                                REQ_deq_bank0_is_amo,
    output logic                                REQ_deq_bank0_is_fence,
    output logic [3:0]                          REQ_deq_bank0_op,
    output logic                                REQ_deq_bank0_is_mq,
    output logic                                REQ_deq_bank0_misaligned,
    output logic                                REQ_deq_bank0_misaligned_exception,
    output logic [VPN_WIDTH-1:0]                REQ_deq_bank0_VPN,
    output logic [PO_WIDTH-3:0]                 REQ_deq_bank0_PO_word,
    output logic [3:0]                          REQ_deq_bank0_byte_mask,
    output logic [31:0]                         REQ_deq_bank0_write_data,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   REQ_deq_bank0_cq_index,

    // REQ stage deq feedback bank 0
    input logic                                 REQ_deq_bank0_ack,
    
    // REQ stage deq info bank 1
    output logic                                REQ_deq_bank1_valid,

    output logic                                REQ_deq_bank1_is_store,
    output logic                                REQ_deq_bank1_is_amo,
    output logic                                REQ_deq_bank1_is_fence,
    output logic [3:0]                          REQ_deq_bank1_op,
    output logic                                REQ_deq_bank1_is_mq,
    output logic                                REQ_deq_bank1_misaligned,
    output logic                                REQ_deq_bank1_misaligned_exception,
    output logic [VPN_WIDTH-1:0]                REQ_deq_bank1_VPN,
    output logic [PO_WIDTH-3:0]                 REQ_deq_bank1_PO_word,
    output logic [3:0]                          REQ_deq_bank1_byte_mask,
    output logic [31:0]                         REQ_deq_bank1_write_data,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   REQ_deq_bank1_cq_index,

    // REQ stage deq feedback bank 1
    input logic                                 REQ_deq_bank1_ack
);
    // wrapper around simple queue modules + a little extra bank logic

    logic REQ_enq_bank;
    logic REQ_enq_bank0_valid;
    logic REQ_enq_bank1_valid;
    logic REQ_enq_bank0_ack;
    logic REQ_enq_bank1_ack;

    assign REQ_enq_bank = REQ_enq_PO_word[DCACHE_WORD_ADDR_BANK_BIT];

    assign REQ_enq_bank0_valid = REQ_enq_valid & (REQ_enq_bank == 1'b0);
    assign REQ_enq_bank1_valid = REQ_enq_valid & (REQ_enq_bank == 1'b1);

    assign REQ_enq_ack = (REQ_enq_bank0_valid & REQ_enq_bank0_ack) | (REQ_enq_bank1_valid & REQ_enq_bank1_ack);

    q_fast_ready #(
        .DATA_WIDTH(1+1+1+4+1+1+1+VPN_WIDTH+PO_WIDTH-2+4+32+LOG_STAMOFU_CQ_ENTRIES),
        .NUM_ENTRIES(STAMOFU_LQ_ENTRIES_PER_BANK)
    ) REQ_Q_BANK0 (
        .CLK(CLK),
        .nRST(nRST),
        
        .enq_valid(REQ_enq_bank0_valid),
        .enq_data({
            REQ_enq_is_store,
            REQ_enq_is_amo,
            REQ_enq_is_fence,
            REQ_enq_op,
            REQ_enq_is_mq,
            REQ_enq_misaligned,
            REQ_enq_misaligned_exception,
            REQ_enq_VPN,
            REQ_enq_PO_word,
            REQ_enq_byte_mask,
            REQ_enq_write_data,
            REQ_enq_cq_index
        }),
        .enq_ready(REQ_enq_bank0_ack),

        .deq_valid(REQ_deq_bank0_valid),
        .deq_data({
            REQ_deq_bank0_is_store,
            REQ_deq_bank0_is_amo,
            REQ_deq_bank0_is_fence,
            REQ_deq_bank0_op,
            REQ_deq_bank0_is_mq,
            REQ_deq_bank0_misaligned,
            REQ_deq_bank0_misaligned_exception,
            REQ_deq_bank0_VPN,
            REQ_deq_bank0_PO_word,
            REQ_deq_bank0_byte_mask,
            REQ_deq_bank0_write_data,
            REQ_deq_bank0_cq_index
        }),
        .deq_ready(REQ_deq_bank0_ack)
    );

    q_fast_ready #(
        .DATA_WIDTH(1+1+1+4+1+1+1+VPN_WIDTH+PO_WIDTH-2+4+32+LOG_STAMOFU_CQ_ENTRIES),
        .NUM_ENTRIES(STAMOFU_LQ_ENTRIES_PER_BANK)
    ) REQ_Q_BANK1 (
        .CLK(CLK),
        .nRST(nRST),
        
        .enq_valid(REQ_enq_bank1_valid),
        .enq_data({
            REQ_enq_is_store,
            REQ_enq_is_amo,
            REQ_enq_is_fence,
            REQ_enq_op,
            REQ_enq_is_mq,
            REQ_enq_misaligned,
            REQ_enq_misaligned_exception,
            REQ_enq_VPN,
            REQ_enq_PO_word,
            REQ_enq_byte_mask,
            REQ_enq_write_data,
            REQ_enq_cq_index
        }),
        .enq_ready(REQ_enq_bank1_ack),

        .deq_valid(REQ_deq_bank1_valid),
        .deq_data({
            REQ_deq_bank1_is_store,
            REQ_deq_bank1_is_amo,
            REQ_deq_bank1_is_fence,
            REQ_deq_bank1_op,
            REQ_deq_bank1_is_mq,
            REQ_deq_bank1_misaligned,
            REQ_deq_bank1_misaligned_exception,
            REQ_deq_bank1_VPN,
            REQ_deq_bank1_PO_word,
            REQ_deq_bank1_byte_mask,
            REQ_deq_bank1_write_data,
            REQ_deq_bank1_cq_index
        }),
        .deq_ready(REQ_deq_bank1_ack)
    );

endmodule