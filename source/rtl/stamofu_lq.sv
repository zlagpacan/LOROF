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
    parameter STAMOFU_LQ_ENTRIES = 4
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

    // REQ stage deq info
    output logic                                REQ_deq_valid,
    output logic                                REQ_deq_is_store,
    output logic                                REQ_deq_is_amo,
    output logic                                REQ_deq_is_fence,
    output logic [3:0]                          REQ_deq_op,
    output logic                                REQ_deq_is_mq,
    output logic                                REQ_deq_misaligned,
    output logic                                REQ_deq_misaligned_exception,
    output logic [VPN_WIDTH-1:0]                REQ_deq_VPN,
    output logic [PO_WIDTH-3:0]                 REQ_deq_PO_word,
    output logic [3:0]                          REQ_deq_byte_mask,
    output logic [31:0]                         REQ_deq_write_data,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   REQ_deq_cq_index,

    // REQ stage deq feedback
    input logic                                 REQ_deq_ack
);

    // just a wrapper around simple queue module

    q_fast_ready #(
        .DATA_WIDTH(1+1+1+4+1+1+1+VPN_WIDTH+PO_WIDTH+4+32+LOG_STAMOFU_CQ_ENTRIES),
        .NUM_ENTRIES(STAMOFU_LQ_ENTRIES)
    ) REQ_Q (
        .CLK(CLK),
        .nRST(nRST),
        
        .enq_valid(REQ_enq_valid),
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
        .enq_ready(REQ_enq_ack),

        .deq_valid(REQ_deq_valid),
        .deq_data({
            REQ_deq_is_store,
            REQ_deq_is_amo,
            REQ_deq_is_fence,
            REQ_deq_op,
            REQ_deq_is_mq,
            REQ_deq_misaligned,
            REQ_deq_misaligned_exception,
            REQ_deq_VPN,
            REQ_deq_PO_word,
            REQ_deq_byte_mask,
            REQ_deq_write_data,
            REQ_deq_cq_index
        }),
        .deq_ready(REQ_deq_ack)
    );

endmodule