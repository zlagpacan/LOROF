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
    input logic                         enq_valid,
    input corep::ibuffer_enq_entry_t    enq_entry,

    // enq feedback
    output logic                        enq_ready,
    output corep::fmid_t                enq_fmid,

    // miss return
    input logic                                         miss_return_valid,
    input corep::fmid_t                                 miss_return_fmid,
    input corep::fetch2B_t [corep::FETCH_LANES-1:0]     miss_return_fetch2B_by_lane,

    // deq
    output logic                                deq_valid,
    output corep::ibuffer_deq_entry_t [3:0]     deq_entry_by_way,

    // def feedback
    input logic                                 deq_ready,

    // restart
    input logic restart_valid
);

    // to allow distram w/ 1 write port, can only do one of miss return or hit return on same-cycle
        // icache's choice if want to use
            // i.e. can use read port for miss access replay

    // ----------------------------------------------------------------
    // Signals:

    // main buffer
    corep::ibuffer_idx_t        distram_rindex;
    corep::ibuffer_enq_entry_t  distram_rdata;

    logic                       distram_wen;
    corep::ibuffer_idx_t        distram_windex;
    corep::ibuffer_enq_entry_t  distram_wdata;

    // 2x entry shift reg for dynamic deq


endmodule