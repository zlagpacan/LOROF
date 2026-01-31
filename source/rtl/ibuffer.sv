/*
    Filename: ibuffer.sv
    Author: zlagpacan
    Description: RTL for Instruction Buffer
    Spec: LOROF/spec/design/ibuffer.md
*/

`include "corep.vh"

module ibuffer (

    // seq
    input logic CLK,
    input logic nRST,

    // enq
    input logic                                         enq_valid,
    input logic [corep::FETCH_LANES-1:0]                enq_lane_mask,
    input logic                                         enq_btb_hit,
    input logic                                         enq_redirect_taken, // can have not taken branch, so redirect doesn't happen
    input corep::fetch_lane_t                           enq_redirect_lane,
    input corep::bcb_idx_t                              enq_bcb_idx,
    input corep::pc35_t                                 enq_src_pc35,
    input corep::pc35_t                                 enq_tgt_pc35,
    input logic                                         enq_page_fault,
    input logic                                         enq_access_fault,
    input logic                                         enq_icache_hit,
    input corep::fetch_unit_t [corep::FETCH_LANES-1:0]  enq_fetch_unit_by_lane,
    input corep::mdp_t [corep::FETCH_LANES-1:0]         enq_mdp_by_lane,

    // enq backpressure
    output logic                                        enq_ready,

    // miss id advertisement


    // miss return


    // deq


    // restart
    input logic restart_valid
);

endmodule