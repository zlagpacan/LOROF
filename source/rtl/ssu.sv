/*
    Filename: ssu.sv
    Author: zlagpacan
    Description: RTL for Store Set Updater
    Spec: LOROF/spec/design/ssu.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ssu #(
    parameter STORE_SET_COUNT = 64,
    parameter SSID_WIDTH = $clog2(STORE_SET_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // ldu_cq CAM update
        // implied dep
    input logic                         ldu_cq_CAM_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   ldu_cq_CAM_update_ld_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_cq_CAM_update_ld_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]   ldu_cq_CAM_update_stamo_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_cq_CAM_update_stamo_ROB_index,

    // ldu_mq CAM update
        // implied dep
    input logic                         ldu_mq_CAM_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   ldu_mq_CAM_update_ld_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_mq_CAM_update_ld_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]   ldu_mq_CAM_update_stamo_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_mq_CAM_update_stamo_ROB_index,

    // ldu_cq commit update
        // implied no dep
        // incorporates ldu_mq commit update
    input logic                         ldu_cq_commit_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   ldu_cq_commit_update_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   ldu_cq_commit_update_ROB_index,

    // stamofu_cq CAM update bank 0
        // implied dep
        // incorporates stamofu_mq CAM update
    input logic                         stamofu_CAM_update_bank0_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_CAM_update_bank0_ld_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_CAM_update_bank0_ld_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_CAM_update_bank0_stamo_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_CAM_update_bank0_stamo_ROB_index,

    // stamofu_cq CAM update bank 1
        // implied dep
        // incorporates stamofu_mq CAM update
    input logic                         stamofu_CAM_update_bank1_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_CAM_update_bank1_ld_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_CAM_update_bank1_ld_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_CAM_update_bank1_stamo_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_CAM_update_bank1_stamo_ROB_index,

    // stamofu_cq commit update
        // implied no dep
        // incorporates stamofu_mq commit update
    input logic                         stamofu_commit_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_commit_update_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_commit_update_ROB_index,

    // update to rob
    output logic                        rob_mdp_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  rob_mdp_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_mdp_update_ROB_index
);

    // instantiate sst

    // simple circular buffers for incoming updates to prioritize younger updates
        // fine since not all updates have to be kept
            // just a prediction mechanism
            // not worth it to put backpressure on upstream CAM's and commit's

endmodule