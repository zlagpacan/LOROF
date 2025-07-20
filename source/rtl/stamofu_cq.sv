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
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_grab_bank0_cq_index,
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_cq_info_grab_bank0_mdp_info,
    output logic                                stamofu_cq_info_grab_bank0_mem_aq,
    output logic                                stamofu_cq_info_grab_bank0_io_aq,
    output logic                                stamofu_cq_info_grab_bank0_mem_rl,
    output logic                                stamofu_cq_info_grab_bank0_io_rl,
    output logic [LOG_ROB_ENTRIES-1:0]          stamofu_cq_info_grab_bank0_ROB_index,
    
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_grab_bank1_cq_index,
    output logic [MDPT_INFO_WIDTH-1:0]          stamofu_cq_info_grab_bank1_mdp_info,
    output logic                                stamofu_cq_info_grab_bank1_mem_aq,
    output logic                                stamofu_cq_info_grab_bank1_io_aq,
    output logic                                stamofu_cq_info_grab_bank1_mem_rl,
    output logic                                stamofu_cq_info_grab_bank1_io_rl,
    output logic [LOG_ROB_ENTRIES-1:0]          stamofu_cq_info_grab_bank1_ROB_index,

    // central queue info ret
    input logic                                 stamofu_cq_info_ret_bank0_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_ret_bank0_cq_index,
    input logic                                 stamofu_cq_info_ret_bank0_dtlb_hit,
    input logic                                 stamofu_cq_info_ret_bank0_page_fault,
    input logic                                 stamofu_cq_info_ret_bank0_access_fault,
    input logic                                 stamofu_cq_info_ret_bank0_is_mem,
    input logic                                 stamofu_cq_info_ret_bank0_mem_aq,
    input logic                                 stamofu_cq_info_ret_bank0_io_aq,
    input logic                                 stamofu_cq_info_ret_bank0_mem_rl,
    input logic                                 stamofu_cq_info_ret_bank0_io_rl,
    input logic                                 stamofu_cq_info_ret_bank0_misaligned,
    input logic                                 stamofu_cq_info_ret_bank0_misaligned_exception,
    input logic [PA_WIDTH-2-1:0]                stamofu_cq_info_ret_bank0_PA_word,
    input logic [3:0]                           stamofu_cq_info_ret_bank0_byte_mask,
    input logic [31:0]                          stamofu_cq_info_ret_bank0_data,
    
    input logic                                 stamofu_cq_info_ret_bank1_valid,
    input logic [LOG_STAMOFU_CQ_ENTRIES-1:0]    stamofu_cq_info_ret_bank1_cq_index,
    input logic                                 stamofu_cq_info_ret_bank1_dtlb_hit,
    input logic                                 stamofu_cq_info_ret_bank1_page_fault,
    input logic                                 stamofu_cq_info_ret_bank1_access_fault,
    input logic                                 stamofu_cq_info_ret_bank1_is_mem,
    input logic                                 stamofu_cq_info_ret_bank1_mem_aq,
    input logic                                 stamofu_cq_info_ret_bank1_io_aq,
    input logic                                 stamofu_cq_info_ret_bank1_mem_rl,
    input logic                                 stamofu_cq_info_ret_bank1_io_rl,
    input logic                                 stamofu_cq_info_ret_bank1_misaligned,
    input logic                                 stamofu_cq_info_ret_bank1_misaligned_exception,
    input logic [PA_WIDTH-2-1:0]                stamofu_cq_info_ret_bank1_PA_word,
    input logic [3:0]                           stamofu_cq_info_ret_bank1_byte_mask,
    input logic [31:0]                          stamofu_cq_info_ret_bank1_data,
);

endmodule