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

    // ldu CAM update
        // implied dep
    output logic                        ldu_CAM_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ldu_CAM_update_ld_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ldu_CAM_update_ld_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]  ldu_CAM_update_stamo_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ldu_CAM_update_stamo_ROB_index,

    // ldu commit update
        // implied no dep
    output logic                        ldu_commit_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  ldu_commit_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  ldu_commit_update_ROB_index,

    // stamofu CAM update
        // implied dep
    output logic                        stamofu_CAM_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  stamofu_CAM_update_ld_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_CAM_update_ld_ROB_index,
    output logic [MDPT_INFO_WIDTH-1:0]  stamofu_CAM_update_stamo_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_CAM_update_stamo_ROB_index,

    // stamofu commit update
        // implied no dep
    output logic                        stamofu_commit_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  stamofu_commit_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_commit_update_ROB_index,

    // update to rob
    output logic                        rob_mdp_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  rob_mdp_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_mdp_update_ROB_index
);

    // instantiate sst

    // simple circular buffers for incoming updates to prioritize younger updates
        // fine since not all updates have to be kept

endmodule