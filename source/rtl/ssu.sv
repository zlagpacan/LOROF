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
    parameter SSID_WIDTH = $clog2(STORE_SET_COUNT),

    parameter SSU_INPUT_BUFFER_ENTRIES = 2,
    parameter SSU_FUNNEL_BUFFER_ENTRIES = 2
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
    input logic                         stamofu_cq_CAM_bank0_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_cq_CAM_bank0_update_ld_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_cq_CAM_bank0_update_ld_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_cq_CAM_bank0_update_stamo_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_cq_CAM_bank0_update_stamo_ROB_index,

    // stamofu_cq CAM update bank 1
        // implied dep
        // incorporates stamofu_mq CAM update
    input logic                         stamofu_cq_CAM_bank1_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_cq_CAM_bank1_update_ld_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_cq_CAM_bank1_update_ld_ROB_index,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_cq_CAM_bank1_update_stamo_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_cq_CAM_bank1_update_stamo_ROB_index,

    // stamofu_cq commit update
        // implied no dep
        // incorporates stamofu_mq commit update
    input logic                         stamofu_cq_commit_update_valid,
    input logic [MDPT_INFO_WIDTH-1:0]   stamofu_cq_commit_update_mdp_info,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_cq_commit_update_ROB_index,

    // mdp update to rob
    output logic                        rob_mdp_update_valid,
    output logic [MDPT_INFO_WIDTH-1:0]  rob_mdp_update_mdp_info,
    output logic [LOG_ROB_ENTRIES-1:0]  rob_mdp_update_ROB_index
);

    // instantiate sst

    // simple circular buffers for incoming updates to prioritize younger updates
        // fine since not all updates have to be kept
            // just a prediction mechanism
            // not worth it to put backpressure on upstream CAM's and commit's

    // ----------------------------------------------------------------
    // Signals:

    // ldu_cq CAM
    logic                           ldu_cq_CAM_req_valid;

    logic [MDPT_INFO_WIDTH-1:0]     ldu_cq_CAM_req_ld_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     ldu_cq_CAM_req_ld_ROB_index;
    logic [MDPT_INFO_WIDTH-1:0]     ldu_cq_CAM_req_stamo_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     ldu_cq_CAM_req_stamo_ROB_index;

    logic                           ldu_cq_CAM_req_ack;

    // ldu_mq CAM
    logic                           ldu_mq_CAM_req_valid;

    logic [MDPT_INFO_WIDTH-1:0]     ldu_mq_CAM_req_ld_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     ldu_mq_CAM_req_ld_ROB_index;
    logic [MDPT_INFO_WIDTH-1:0]     ldu_mq_CAM_req_stamo_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     ldu_mq_CAM_req_stamo_ROB_index;

    logic                           ldu_mq_CAM_req_ack;

    // ldu_cq commit
    logic                           ldu_cq_commit_req_valid;

    logic [MDPT_INFO_WIDTH-1:0]     ldu_cq_commit_req_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     ldu_cq_commit_req_ROB_index;

    logic                           ldu_cq_commit_req_ack;

    // stamofu_cq CAM bank 0
    logic                           stamofu_cq_CAM_bank0_req_valid;

    logic [MDPT_INFO_WIDTH-1:0]     stamofu_cq_CAM_bank0_req_ld_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     stamofu_cq_CAM_bank0_req_ld_ROB_index;
    logic [MDPT_INFO_WIDTH-1:0]     stamofu_cq_CAM_bank0_req_stamo_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     stamofu_cq_CAM_bank0_req_stamo_ROB_index;

    logic                           stamofu_cq_CAM_bank0_req_ack;

    // stamofu_cq CAM bank 1
    logic                           stamofu_cq_CAM_bank1_req_valid;

    logic [MDPT_INFO_WIDTH-1:0]     stamofu_cq_CAM_bank1_req_ld_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     stamofu_cq_CAM_bank1_req_ld_ROB_index;
    logic [MDPT_INFO_WIDTH-1:0]     stamofu_cq_CAM_bank1_req_stamo_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     stamofu_cq_CAM_bank1_req_stamo_ROB_index;

    logic                           stamofu_cq_CAM_bank1_req_ack;

    // stamofu_cq commit
    logic                           stamofu_cq_commit_req_valid;

    logic [MDPT_INFO_WIDTH-1:0]     stamofu_cq_commit_req_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     stamofu_cq_commit_req_ROB_index;

    logic                           stamofu_cq_commit_req_ack;

    // funnel buffer enq
    logic                           funnel_enq_valid;

    logic                           funnel_enq_is_CAM;
    logic                           funnel_enq_A_valid;
    logic [MDPT_INFO_WIDTH-1:0]     funnel_enq_A_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     funnel_enq_A_ROB_index;
    logic                           funnel_enq_B_valid;
    logic [MDPT_INFO_WIDTH-1:0]     funnel_enq_B_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     funnel_enq_B_ROB_index;

    logic                           funnel_enq_ready;
    
    // funnel buffer deq
    logic                           funnel_deq_valid;

    logic                           funnel_deq_is_CAM;
    logic                           funnel_deq_A_valid;
    logic [MDPT_INFO_WIDTH-1:0]     funnel_deq_A_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     funnel_deq_A_ROB_index;
    logic                           funnel_deq_B_valid;
    logic [MDPT_INFO_WIDTH-1:0]     funnel_deq_B_mdp_info;
    logic [LOG_ROB_ENTRIES-1:0]     funnel_deq_B_ROB_index;

    logic                           funnel_deq_ready;

    logic funnel_deq_disable_A, next_funnel_deq_disable_A;

    // sst
    logic           new_SSID_valid;
    logic [5:0]     new_SSID;
    logic           touch_SSID_valid;
    logic [5:0]     touch_SSID;

    // ----------------------------------------------------------------
    // Logic:

    // ldu_cq CAM
    cb #(
        .DATA_WIDTH(2*(MDPT_INFO_WIDTH+LOG_ROB_ENTRIES)),
        .NUM_ENTRIES(SSU_INPUT_BUFFER_ENTRIES)
    ) LDU_CQ_CAM_CB (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(
            ldu_cq_CAM_update_valid
            // ignore enq if no change -> already full mdp match
            & ~(
                (ldu_cq_CAM_update_ld_mdp_info[7:6] == 2'b11)
                & (ldu_cq_CAM_update_stamo_mdp_info[7:6] == 2'b11)
                & (ldu_cq_CAM_update_ld_mdp_info[5:0] == ldu_cq_CAM_update_stamo_mdp_info[5:0]))
        ), 
        .enq_data({
            ldu_cq_CAM_update_ld_mdp_info,
            ldu_cq_CAM_update_ld_ROB_index,
            ldu_cq_CAM_update_stamo_mdp_info,
            ldu_cq_CAM_update_stamo_ROB_index
        }),
        .deq_valid(ldu_cq_CAM_req_valid),
        .deq_data({
            ldu_cq_CAM_req_ld_mdp_info,
            ldu_cq_CAM_req_ld_ROB_index,
            ldu_cq_CAM_req_stamo_mdp_info,
            ldu_cq_CAM_req_stamo_ROB_index
        }),
        .deq_ready(ldu_cq_CAM_req_ack)
    );

    // ldu_mq CAM
    cb #(
        .DATA_WIDTH(2*(MDPT_INFO_WIDTH+LOG_ROB_ENTRIES)),
        .NUM_ENTRIES(SSU_INPUT_BUFFER_ENTRIES)
    ) LDU_MQ_CAM_CB (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(
            ldu_mq_CAM_update_valid
            // ignore enq if no change -> already full mdp match
            & ~(
                (ldu_mq_CAM_update_ld_mdp_info[7:6] == 2'b11)
                & (ldu_mq_CAM_update_stamo_mdp_info[7:6] == 2'b11)
                & (ldu_mq_CAM_update_ld_mdp_info[5:0] == ldu_mq_CAM_update_stamo_mdp_info[5:0]))
        ), 
        .enq_data({
            ldu_mq_CAM_update_ld_mdp_info,
            ldu_mq_CAM_update_ld_ROB_index,
            ldu_mq_CAM_update_stamo_mdp_info,
            ldu_mq_CAM_update_stamo_ROB_index
        }),
        .deq_valid(ldu_mq_CAM_req_valid),
        .deq_data({
            ldu_mq_CAM_req_ld_mdp_info,
            ldu_mq_CAM_req_ld_ROB_index,
            ldu_mq_CAM_req_stamo_mdp_info,
            ldu_mq_CAM_req_stamo_ROB_index
        }),
        .deq_ready(ldu_mq_CAM_req_ack)
    );

    // ldu_cq commit
    cb #(
        .DATA_WIDTH(MDPT_INFO_WIDTH+LOG_ROB_ENTRIES),
        .NUM_ENTRIES(SSU_INPUT_BUFFER_ENTRIES)
    ) LDU_CQ_COMMIT_CB (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(
            ldu_cq_commit_update_valid
            // ignore enq if no change -> already no mdp present
            & ~(ldu_cq_commit_update_mdp_info[7:6] == 2'b00)
        ), 
        .enq_data({
            ldu_cq_commit_update_mdp_info,
            ldu_cq_commit_update_ROB_index
        }),
        .deq_valid(ldu_cq_commit_req_valid),
        .deq_data({
            ldu_cq_commit_req_mdp_info,
            ldu_cq_commit_req_ROB_index
        }),
        .deq_ready(ldu_cq_commit_req_ack)
    );

    // stamofu_cq CAM bank 0
    cb #(
        .DATA_WIDTH(2*(MDPT_INFO_WIDTH+LOG_ROB_ENTRIES)),
        .NUM_ENTRIES(SSU_INPUT_BUFFER_ENTRIES)
    ) STAMOFU_CQ_CAM_BANK0_CB (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(
            stamofu_cq_CAM_bank0_update_valid
            // ignore enq if no change -> already full mdp match
            & ~(
                (stamofu_cq_CAM_bank0_update_ld_mdp_info[7:6] == 2'b11)
                & (stamofu_cq_CAM_bank0_update_stamo_mdp_info[7:6] == 2'b11)
                & (stamofu_cq_CAM_bank0_update_ld_mdp_info[5:0] == stamofu_cq_CAM_bank0_update_stamo_mdp_info[5:0]))
        ), 
        .enq_data({
            stamofu_cq_CAM_bank0_update_ld_mdp_info,
            stamofu_cq_CAM_bank0_update_ld_ROB_index,
            stamofu_cq_CAM_bank0_update_stamo_mdp_info,
            stamofu_cq_CAM_bank0_update_stamo_ROB_index
        }),
        .deq_valid(stamofu_cq_CAM_bank0_req_valid),
        .deq_data({
            stamofu_cq_CAM_bank0_req_ld_mdp_info,
            stamofu_cq_CAM_bank0_req_ld_ROB_index,
            stamofu_cq_CAM_bank0_req_stamo_mdp_info,
            stamofu_cq_CAM_bank0_req_stamo_ROB_index
        }),
        .deq_ready(stamofu_cq_CAM_bank0_req_ack)
    );

    // stamofu_cq CAM bank 1
    cb #(
        .DATA_WIDTH(2*(MDPT_INFO_WIDTH+LOG_ROB_ENTRIES)),
        .NUM_ENTRIES(SSU_INPUT_BUFFER_ENTRIES)
    ) STAMOFU_CQ_CAM_BANK1_CB (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(
            stamofu_cq_CAM_bank1_update_valid
            // ignore enq if no change -> already full mdp match
            & ~(
                (stamofu_cq_CAM_bank1_update_ld_mdp_info[7:6] == 2'b11)
                & (stamofu_cq_CAM_bank1_update_stamo_mdp_info[7:6] == 2'b11)
                & (stamofu_cq_CAM_bank1_update_ld_mdp_info[5:0] == stamofu_cq_CAM_bank1_update_stamo_mdp_info[5:0]))
        ), 
        .enq_data({
            stamofu_cq_CAM_bank1_update_ld_mdp_info,
            stamofu_cq_CAM_bank1_update_ld_ROB_index,
            stamofu_cq_CAM_bank1_update_stamo_mdp_info,
            stamofu_cq_CAM_bank1_update_stamo_ROB_index
        }),
        .deq_valid(stamofu_cq_CAM_bank1_req_valid),
        .deq_data({
            stamofu_cq_CAM_bank1_req_ld_mdp_info,
            stamofu_cq_CAM_bank1_req_ld_ROB_index,
            stamofu_cq_CAM_bank1_req_stamo_mdp_info,
            stamofu_cq_CAM_bank1_req_stamo_ROB_index
        }),
        .deq_ready(stamofu_cq_CAM_bank1_req_ack)
    );

    // stamofu_cq commit
    cb #(
        .DATA_WIDTH(MDPT_INFO_WIDTH+LOG_ROB_ENTRIES),
        .NUM_ENTRIES(SSU_INPUT_BUFFER_ENTRIES)
    ) STAMOFU_CQ_COMMIT_CB (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(
            stamofu_cq_commit_update_valid
            // ignore enq if no change -> already no mdp present
            & ~(stamofu_cq_commit_update_mdp_info[7:6] == 2'b00)
        ), 
        .enq_data({
            stamofu_cq_commit_update_mdp_info,
            stamofu_cq_commit_update_ROB_index
        }),
        .deq_valid(stamofu_cq_commit_req_valid),
        .deq_data({
            stamofu_cq_commit_req_mdp_info,
            stamofu_cq_commit_req_ROB_index
        }),
        .deq_ready(stamofu_cq_commit_req_ack)
    );

    // funnel buffer enq logic
    always_comb begin

        // defaults:
        ldu_cq_CAM_req_ack = 1'b0;
        ldu_mq_CAM_req_ack = 1'b0;
        stamofu_cq_CAM_bank0_req_ack = 1'b0;
        stamofu_cq_CAM_bank1_req_ack = 1'b0;
        ldu_cq_commit_req_ack = 1'b0;
        stamofu_cq_commit_req_ack = 1'b0;

        funnel_enq_valid = 1'b0;

        funnel_enq_is_CAM = 1'b0;
        funnel_enq_A_valid = 1'b0;
        funnel_enq_A_mdp_info = 8'h00;
        funnel_enq_A_ROB_index = 7'h00;
        funnel_enq_B_valid = 1'b0;
        funnel_enq_B_mdp_info = 8'h00;
        funnel_enq_B_ROB_index = 7'h00;

        // priority order:
        if (funnel_enq_ready) begin

            if (ldu_cq_CAM_req_valid) begin
                ldu_cq_CAM_req_ack = 1'b1;
                funnel_enq_valid = 1'b1;
                funnel_enq_is_CAM = 1'b1;

                funnel_enq_A_valid = 1'b1;
                funnel_enq_A_mdp_info = ldu_cq_CAM_req_ld_mdp_info;
                funnel_enq_A_ROB_index = ldu_cq_CAM_req_ld_ROB_index;
                funnel_enq_B_valid = 1'b1;
                funnel_enq_B_mdp_info = ldu_cq_CAM_req_stamo_mdp_info;
                funnel_enq_B_ROB_index = ldu_cq_CAM_req_stamo_ROB_index;
            end
            else if (ldu_mq_CAM_req_valid) begin
                ldu_mq_CAM_req_ack = 1'b1;
                funnel_enq_valid = 1'b1;
                funnel_enq_is_CAM = 1'b1;

                funnel_enq_A_valid = 1'b1;
                funnel_enq_A_mdp_info = ldu_mq_CAM_req_ld_mdp_info;
                funnel_enq_A_ROB_index = ldu_mq_CAM_req_ld_ROB_index;
                funnel_enq_B_valid = 1'b1;
                funnel_enq_B_mdp_info = ldu_mq_CAM_req_stamo_mdp_info;
                funnel_enq_B_ROB_index = ldu_mq_CAM_req_stamo_ROB_index;
            end
            else if (stamofu_cq_CAM_bank0_req_valid) begin
                stamofu_cq_CAM_bank0_req_ack = 1'b1;
                funnel_enq_valid = 1'b1;
                funnel_enq_is_CAM = 1'b1;

                funnel_enq_A_valid = 1'b1;
                funnel_enq_A_mdp_info = stamofu_cq_CAM_bank0_req_ld_mdp_info;
                funnel_enq_A_ROB_index = stamofu_cq_CAM_bank0_req_ld_ROB_index;
                funnel_enq_B_valid = 1'b1;
                funnel_enq_B_mdp_info = stamofu_cq_CAM_bank0_req_stamo_mdp_info;
                funnel_enq_B_ROB_index = stamofu_cq_CAM_bank0_req_stamo_ROB_index;
            end
            else if (stamofu_cq_CAM_bank1_req_valid) begin
                stamofu_cq_CAM_bank1_req_ack = 1'b1;
                funnel_enq_valid = 1'b1;
                funnel_enq_is_CAM = 1'b1;

                funnel_enq_A_valid = 1'b1;
                funnel_enq_A_mdp_info = stamofu_cq_CAM_bank1_req_ld_mdp_info;
                funnel_enq_A_ROB_index = stamofu_cq_CAM_bank1_req_ld_ROB_index;
                funnel_enq_B_valid = 1'b1;
                funnel_enq_B_mdp_info = stamofu_cq_CAM_bank1_req_stamo_mdp_info;
                funnel_enq_B_ROB_index = stamofu_cq_CAM_bank1_req_stamo_ROB_index;
            end
            else if (ldu_cq_commit_req_ack | stamofu_cq_commit_req_ack) begin
                // can take both commit's in same cycle
                ldu_cq_commit_req_ack = 1'b1;
                stamofu_cq_commit_req_ack = 1'b1;
                funnel_enq_valid = 1'b1;
                funnel_enq_is_CAM = 1'b0;

                funnel_enq_A_valid = ldu_cq_commit_req_valid;
                funnel_enq_A_mdp_info = ldu_cq_commit_req_mdp_info;
                funnel_enq_A_ROB_index = ldu_cq_commit_req_ROB_index;
                funnel_enq_B_valid = stamofu_cq_commit_req_valid;
                funnel_enq_B_mdp_info = stamofu_cq_commit_req_mdp_info;
                funnel_enq_B_ROB_index = stamofu_cq_commit_req_ROB_index;
            end
        end
    end

    // funnel buffer
    q_fast_ready #(
        .DATA_WIDTH(1+2*(1+MDPT_INFO_WIDTH+LOG_ROB_ENTRIES)),
        .NUM_ENTRIES(SSU_FUNNEL_BUFFER_ENTRIES)
    ) FUNNEL_BUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(funnel_enq_valid),
        .enq_data({
            funnel_enq_is_CAM,
            funnel_enq_A_valid,
            funnel_enq_A_mdp_info,
            funnel_enq_A_ROB_index,
            funnel_enq_B_valid,
            funnel_enq_B_mdp_info,
            funnel_enq_B_ROB_index
        }),
        .enq_ready(funnel_enq_ready),
        .deq_valid(funnel_deq_valid),
        .deq_data({
            funnel_deq_is_CAM,
            funnel_deq_A_valid,
            funnel_deq_A_mdp_info,
            funnel_deq_A_ROB_index,
            funnel_deq_B_valid,
            funnel_deq_B_mdp_info,
            funnel_deq_B_ROB_index
        }),
        .deq_ready(funnel_deq_ready)
    );

    // funnel buffer deq FSM
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            funnel_deq_disable_A <= 1'b0;
        end
        else begin
            funnel_deq_disable_A <= next_funnel_deq_disable_A;
        end
    end
    always_comb begin

        // defaults:
        funnel_deq_ready = 1'b0;
        next_funnel_deq_disable_A = 1'b0;

        new_SSID_valid = 1'b0;
        touch_SSID_valid = 1'b0;
        touch_SSID = funnel_deq_B_mdp_info[5:0];

        rob_mdp_update_valid = 1'b0;
        rob_mdp_update_mdp_info = {2'b11, funnel_deq_B_mdp_info[5:0]};
        rob_mdp_update_ROB_index = funnel_deq_A_ROB_index;

        if (funnel_deq_valid) begin
            
            // definitely update if have entry to deq
            rob_mdp_update_valid = 1'b1;

            // CAM
            if (funnel_deq_is_CAM) begin

                // A stage CAM
                if (funnel_deq_A_valid & ~funnel_deq_disable_A) begin
                    next_funnel_deq_disable_A = 1'b1;

                    rob_mdp_update_ROB_index = funnel_deq_A_ROB_index;

                    if (|funnel_deq_A_mdp_info[7:6] & |funnel_deq_B_mdp_info[7:6]) begin
                        if (funnel_deq_A_mdp_info[5:0] == funnel_deq_B_mdp_info[5:0]) begin
                            // matching mdp's -> use B (can use either)
                            rob_mdp_update_mdp_info = {2'b11, funnel_deq_B_mdp_info[5:0]};
                        end
                        else begin
                            // mismatched mdp's -> use B (merge to stamofu's)
                            rob_mdp_update_mdp_info = {2'b11, funnel_deq_B_mdp_info[5:0]};
                        end
                    end
                    else if (|funnel_deq_A_mdp_info[7:6]) begin
                        // only A mdp -> use A (ldu's)
                        rob_mdp_update_mdp_info = {2'b11, funnel_deq_A_mdp_info[5:0]};
                    end
                    else if (|funnel_deq_B_mdp_info[7:6]) begin
                        // only B mdp -> use B (stamofu's)
                        rob_mdp_update_mdp_info = {2'b11, funnel_deq_B_mdp_info[5:0]};
                    end
                    else begin
                        // no mdp -> use new
                        rob_mdp_update_mdp_info = {2'b11, new_SSID};
                    end
                end
                
                // B stage CAM
                else begin
                    funnel_deq_ready = 1'b1;

                    rob_mdp_update_ROB_index = funnel_deq_B_ROB_index;

                    if (|funnel_deq_A_mdp_info[7:6] & |funnel_deq_B_mdp_info[7:6]) begin
                        if (funnel_deq_A_mdp_info[5:0] == funnel_deq_B_mdp_info[5:0]) begin
                            // matching mdp's -> use B (can use either)
                            touch_SSID_valid = 1'b1;
                            touch_SSID = funnel_deq_B_mdp_info[5:0];

                            rob_mdp_update_mdp_info = {2'b11, funnel_deq_B_mdp_info[5:0]};
                        end
                        else begin
                            // mismatched mdp's -> use B (merge to stamofu's)
                            touch_SSID_valid = 1'b1;
                            touch_SSID = funnel_deq_B_mdp_info[5:0];

                            rob_mdp_update_mdp_info = {2'b11, funnel_deq_B_mdp_info[5:0]};
                        end
                    end
                    else if (|funnel_deq_A_mdp_info[7:6]) begin
                        // only A mdp -> use A (ldu's)
                        touch_SSID_valid = 1'b1;
                        touch_SSID = funnel_deq_A_mdp_info[5:0];

                        rob_mdp_update_mdp_info = {2'b11, funnel_deq_A_mdp_info[5:0]};
                    end
                    else if (|funnel_deq_B_mdp_info[7:6]) begin
                        // only B mdp -> use B (stamofu's)
                        touch_SSID_valid = 1'b1;
                        touch_SSID = funnel_deq_B_mdp_info[5:0];

                        rob_mdp_update_mdp_info = {2'b11, funnel_deq_B_mdp_info[5:0]};
                    end
                    else begin
                        // no mdp -> use new
                        new_SSID_valid = 1'b1;

                        rob_mdp_update_mdp_info = {2'b11, new_SSID};
                    end
                end
            end

            // commit
            else begin
                if (funnel_deq_A_valid & ~funnel_deq_disable_A) begin
                    // A stage commit -> subtract from A

                    // policy for now is 3 -> 1 -> 0
                    case (funnel_deq_A_mdp_info[7:6])
                        2'b00:  rob_mdp_update_mdp_info[7:6] = 2'b00;
                        2'b01:  rob_mdp_update_mdp_info[7:6] = 2'b00;
                        2'b10:  rob_mdp_update_mdp_info[7:6] = 2'b00;
                        2'b11:  rob_mdp_update_mdp_info[7:6] = 2'b01;
                    endcase
                    rob_mdp_update_mdp_info[5:0] = funnel_deq_A_mdp_info[5:0];
                    rob_mdp_update_ROB_index = funnel_deq_A_ROB_index;

                    // check for B stage commit next
                    if (funnel_deq_B_valid) begin
                        next_funnel_deq_disable_A = 1'b1;
                    end
                    else begin
                        funnel_deq_ready = 1'b1;
                    end
                end
                else if (funnel_deq_B_valid) begin
                    // B stage commit -> subtract from B

                    funnel_deq_ready = 1'b1;

                    // policy for now is 3 -> 1 -> 0
                    case (funnel_deq_B_mdp_info[7:6])
                        2'b00:  rob_mdp_update_mdp_info[7:6] = 2'b00;
                        2'b01:  rob_mdp_update_mdp_info[7:6] = 2'b00;
                        2'b10:  rob_mdp_update_mdp_info[7:6] = 2'b00;
                        2'b11:  rob_mdp_update_mdp_info[7:6] = 2'b01;
                    endcase
                    rob_mdp_update_mdp_info[5:0] = funnel_deq_B_mdp_info[5:0];
                    rob_mdp_update_ROB_index = funnel_deq_B_ROB_index;
                end
            end
        end
    end

    // sst
    sst #(
        .STORE_SET_COUNT(STORE_SET_COUNT),
        .SSID_WIDTH(SSID_WIDTH)
    ) SST (
        .CLK(CLK),
        .nRST(nRST),
        .new_SSID_valid(new_SSID_valid),
        .new_SSID(new_SSID),
        .touch_SSID_valid(touch_SSID_valid),
        .touch_SSID(touch_SSID)
    );

endmodule