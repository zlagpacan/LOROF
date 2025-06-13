/*
    Filename: stamofu_launch_q.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Launch Queue
    Spec: LOROF/spec/design/stamofu_launch_q.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_launch_q (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage enq info
    output logic                                REQ_enq_valid,
    output logic                                REQ_enq_is_store,
    output logic                                REQ_enq_is_amo,
    output logic                                REQ_enq_is_fence,
    output logic [3:0]                          REQ_enq_op,
    output logic                                REQ_enq_is_mq,
    output logic                                REQ_enq_misaligned,
    output logic                                REQ_enq_misaligned_exception,
    output logic [VPN_WIDTH-1:0]                REQ_enq_VPN,
    output logic [PO_WIDTH-3:0]                 REQ_enq_PO_word,
    output logic [3:0]                          REQ_enq_byte_mask,
    output logic [31:0]                         REQ_enq_write_data,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   REQ_enq_cq_index,

    // REQ stage enq feedback
    input logic                                 REQ_enq_ack,

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

endmodule