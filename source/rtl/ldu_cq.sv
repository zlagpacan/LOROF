/*
    Filename: ldu_cq.sv
    Author: zlagpacan
    Description: RTL for Load Unit Central Queue
    Spec: LOROF/spec/design/ldu_cq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ldu_cq #(
    parameter LDU_CQ_ENTRIES = 4,
    parameter LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES)
) (

);
    
    // entry:
        // valid
        // killed
        // op
            // need for realignment of bytes and signed vs unsigned
        // mdp info
        // dest PR
        // ROB index
        // WB sent
        // misaligned
        // mq index
        // matching mdp count
        // mdp update req
        // forwarded
        // forwarded ROB index
        // nasty forward
        // PA word
        // byte mask
        // return data
        // return request
        // restart request

endmodule