/*
    Filename: stamofu_cq.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Central Queue
    Spec: LOROF/spec/design/stamofu_cq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module stamofu_cq #(
    parameter STAMOFU_CQ_ENTRIES = 24,
    parameter LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to central queue
    input logic                                 stamofu_cq_enq_valid,
    input logic                                 stamofu_cq_enq_killed,
    input logic                                 stamofu_cq_enq_is_store,
    input logic                                 stamofu_cq_enq_is_amo,
    input logic                                 stamofu_cq_enq_is_fence,
    input logic [3:0]                           stamofu_cq_enq_op,
    input logic [MDPT_INFO_WIDTH-1:0]           stamofu_cq_enq_mdp_info,
    input logic                                 stamofu_cq_enq_mem_aq,
    input logic                                 stamofu_cq_enq_io_aq,
    input logic                                 stamofu_cq_enq_mem_rl,
    input logic                                 stamofu_cq_enq_io_rl,
    input logic [LOG_PR_COUNT-1:0]              stamofu_cq_enq_dest_PR,
    input logic [LOG_ROB_ENTRIES-1:0]           stamofu_cq_enq_ROB_index,

    // central queue enqueue feedback
    output logic                                stamofu_cq_enq_ready,
    output logic [LOG_STAMOFU_CQ_ENTRIES-1:0]   stamofu_cq_enq_index,

    // central queue info grab
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_grab_cq_index,
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_cq_info_grab_mdp_info,
    output logic                                stamofu_cq_info_grab_mem_aq,
    output logic                                stamofu_cq_info_grab_io_aq,
    output logic                                stamofu_cq_info_grab_mem_rl,
    output logic                                stamofu_cq_info_grab_io_rl,
    output logic [LOG_ROB_ENTRIES-1:0]          stamofu_cq_info_grab_ROB_index,
);

endmodule