/*
    Filename: lsq.sv
    Author: zlagpacan
    Description: RTL for Load-Store Queue
    Spec: LOROF/spec/design/lsq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module lsq #(
    parameter 
) (

    // seq
    input logic CLK,
    input logic nRST,
    
);
    // load path:
        // enqueue into ldu_dq
            // 4-way in-order
        // waiting to dequeue from ldu_dq
            // track operands becoming ready while in ldu_dq
                // no forwarding, only mark as individual operand ready
        // dequeue from ldu_dq, enqueue into ldu_cq
            // 1-way in-order
            // track operands becoming ready while in ldu_dq
                // no forwarding, only mark as individual operand ready
        // waiting to issue from ldu_cq
            // check next issue ready
                // check current operand state
                    // track next operand becoming ready while in ldu_cq
                        // no forwarding, only mark as operand ready
                    // if operand still not ready, still not issuable
            // while have issue ready, wait until turn to issue into ldu_addr_pipeline
        // issue from ldu_cq into ldu_addr_pipeline (IS stage)
            // no issue if ldu_addr_pipeline stalled
            // PE on issuable entries
            // select issuing entry following oldest issuable
                // masked lowest else unmasked lowest
            // mark next ldu_cq state as issued
        // ldu_addr_pipeline PR stage
            // prf Request stage
                // other FU's would do prf request on IS, 
                // but ldu_cq is too big to do issue and prf req same-cycle 
            // stall here and don't send request if OC stall
        // ldu_addr_pipeline OC stage
            // Operand Collection stage
            // wait for operand read ack, read it from the associated read (bank, port)
        // ldu_addr_pipeline AC stage
            // Address Calculation stage
            // operand + imm
            // mark relevant word addresses and bitmasks for dependence checking
            // determine if need 2x load launch
        // ldu_addr_pipeline L stage
            // Launch stage
            // dTLB req + dcache req + stamofu_cq CAM
            // can be stalled if there is a second-try launch this cycle
            // mark ldu_cq entry as launched and waiting for resp
            // need 2x load launch for misaligned 
        // ldu_cq first cycle after launch
            // if dTLB resp, collect PA, check  then dcache access is valid, mark as waiting for dcache
            // else, mark entry as waiting for second try launch after dTLB resp
        // ldu_cq second try launch
            // wait until late dTLB resp returns
        // ldu_cq 

    // store path:
        // 2x complete path dTLB cycles for misaligned
            // check both words separately, just like 2x load launches

    // AMO path:
        // what to do about AMO being in write buffer but gone from stamofu_cq?
            // maybe not gone from stamofu_cq
                // especially want to keep in stamofu_cq so that has ROB_index and dest PR info don't have
                // go to . and also want to dependent loads to wait until 
            // allow stores to commit after AMO if nothing before is exceptable
                // all regular instructions before are complete
                // loads before are marked unexceptable -> got dTLB, no exception
                // stores and amo's before are marked unexceptable -> got dTLB, no exception
            // so SQ launch head moves on, but still waiting for outstanding AMO's at true head to complete
                // can't enQ at or past true head
            // then what is point of SQ launch head?
                // just let ROB dequeue from its unexceptable head as it pleases and it is SQ's job
                // to correctly mark entries as unexceptable in ROB and to only dequeue from
                // SQ once 


    // fence path:

    // stamofu_cq CAM on load launch
        // comparator + age check stores dependent on
        // bit mask PE youngest version of each byte
            // this gets very nasty fast
            // if store bytes don't cover load bytes, consider just stalling until store commits

    // ldu_cq CAM on store/amo complete
        // comparator + age check for dependent loads
        // each dependent load checks for younger version of each byte
            // this gets very nasty fast
            // if store bytes don't cover load bytes, consider just stalling until store commits
        // oldest dependent load which didn't take dependence into account gets restart

    // dcache's job to deal with write buffer dependences
        // load launch CAM's write buffer checking for dependence
        // if write buffer has superset dependence, load can safely steal it as-is
        // if write buffer has matching partial dependence or AMO, need to wait for dependence to finish writing to cache array
            // can use MSHR to hold dependent read until last partial dependent or AMO write 
                // found by write buffer CAM index is completed into cache array
        // have backpressure by usual limiting of launches unless MSHR available

endmodule