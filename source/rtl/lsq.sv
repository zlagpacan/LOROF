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
                // misaligned such that need 2x word-aligned access
        // ldu_addr_pipeline PL stage
            // Pipeline Launch stage
            // dTLB req + dcache req
            // can be stalled if there is a second-try launch this cycle
            // mark ldu_cq entry as launched and waiting for dTLB resp
            // need 2x load launch for misaligned
                // first launch can stall if there is second-try launch this cycle
                // second launch can stall if there is no ldu_mq entry available
                // when second launch happens, allocate ldu_mq entry, set symmetric pointers b/w ldu_mq entry and ldu_cq entry
        // ldu_cq first cycle after launch
            // if dTLB resp, collect PA
                // if no applicable io nor mem fence then dcache launch from last cycle is valid, mark as waiting for dcache
                    // also launch stamofu_cq CAM
                // else, need to wait mark entry as waiting for second try launch after fence clear
            // else, mark entry as waiting for second try launch after dTLB resp
        // ldu_cq late dTLB resp
            // wait until late dTLB resp returns
                // if no applicable io nor mem fence then can do second try launch to dcache, mark as waiting for dcache if get launch arbitrated
                    // also launch stamofu_cq CAM
                // else, need to wait, mark entry as waiting for fence clear
        // ldu_cq fence clear
            // implies already got dTLB resp, on first cycle or late, and found applicable io or mem fence
            // wait until load older than oldest applicable io vs. mem fence
                // can do second try launch to dcache, mark as waiting for dcache if get launch arbitrated
        // ldu_cq dcache resp
            // implies already got dTLB resp and already waited for applicable io vs. mem fence
            // dcache hit means dcache resp might arrive before stamofu_cq CAM depending on how timing ends up working out
                // if have store set, or maybe always, buffer dcache val(s) 
            // wait until get dcache resp
                // if got forward from SQ CAM, ignore dcache resp
                // else, if entry has store set which is not resolved
                    // got ROB index to wait until in order for entry to be marked ready
                // else, free to perform dcache resp reg write
        // ldu_cq stamofu_cq CAM resp
            // launched after get dTLB resp(s)
                // need good PA
            // 

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
                // SQ once reg write value has been returned


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
        // if write buffer has superset dependence, load can safely steal write buffer entry value as-is
        // if write buffer has matching partial dependence or AMO:
            // option 1: wait for dependence to finish writing to cache array
                // can use MSHR to hold dependent read until last partial dependent or AMO write 
                    // found by write buffer CAM index is completed into cache array
            // option 2: deal with partial dependences
                // always perform regular dcache array read, then forward dependent bytes from write buffer
                    // as needed
                // if dcache miss, recheck write buffer on MSHR miss return 
        // have backpressure by stalling launches unless MSHR available or not currently trying miss return 
            // dcache array and write buffer lookups


    // structures:

        // ldu:

            // ldu_dq
                // Dispatch Queue

            // ldu_addr_pipeline

            // ldu_cq
                // Central Queue

            // ldu_mq
                // Misaligned Queue

        // stamofu:
        
            // stamofu_dq
                // Dispatch Queue

            // stamofu_addr_pipeline

            // stamofu_cq
                // Central Queue
            
            // stamofu_mq
                // Misaligned Queue

        // mem_aq_q
            // Mem Acquire Queue

        // io_aq_q
            // IO Acquire Queue

endmodule