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

module lsq (

    // seq
    input logic CLK,
    input logic nRST,

    input logic TODO

);
    // Load Path:
        // enqueue into ldu_dq
            // 4-way in-order
        // waiting to dequeue from ldu_dq
            // track operands becoming ready while in ldu_dq
                // no forwarding, only mark as individual operand ready
        // dequeue from ldu_dq, enqueue into ldu_cq + ldu_iq
            // 1-way in-order
            // track operands becoming ready while in ldu_dq
                // no forwarding, only mark as individual operand ready
            // ldu_cq and ldu_iq must be ready
            // ldu_cq entry initialization
                // mark as waiting on address
        // waiting to issue from ldu_iq
            // check current operand state
                // track next operand becoming ready while in ldu_cq
                    // no forwarding, only mark as operand ready
                // if operand still not ready, still not issuable
        // issue from ldu_iq into ldu_pipeline (IS stage)
            // no issue if ldu_pipeline stalled
            // regular IQ operation with PRF request upon issue
        // ldu_pipeline OC stage
            // Operand Collection stage
            // wait for operand read ack, read it from the associated read bank and port
        // ldu_pipeline AC stage
            // Address Calculation stage
            // operand + imm
            // mark relevant word addresses and bitmasks for dependence checking
            // determine if need 2x load launch
                // misaligned such that need 2x word-aligned access
                // when pipeline unstalled, send first launch to REQ stage, keep second launch in AC stage
        // ldu_pipeline REQ stage
            // Request stage
            // dTLB req + dcache req
                // can stall if dTLB or dcache ran out of MSHR's
            // can be stalled if there is a second-try launch this cycle
            // can be stalled if there will be a late dcache resp next cycle
            // need 2x load launch for misaligned
                // first launch can stall if there is second-try launch this cycle
                // second launch can stall if there is no ldu_mq entry available
                // when second launch happens, allocate ldu_mq entry, set symmetric pointers b/w ldu_mq entry and ldu_cq entry
        // ldu_pipeline RESP stage
            // Response stage
            // if dTLB resp, collect PA and give to ldu_cq/ldu_mq
                // check for page fault or access fault
                    // send exception using ldu_cq ROB_index
                    // just like a killed load op, writeback garbage to dest PR
                // if no applicable io nor mem fence then dcache launch from last cycle is valid, mark as waiting for dcache
                    // also launch stamofu_cq CAM
                    // when all launches done, also send complete to ROB
                // else, need to wait mark entry as waiting for second try launch after fence clear
            // else, mark entry as waiting for second try launch after dTLB resp
        // ldu_cq/ldu_mq late dTLB resp
            // wait until late dTLB resp returns
                // check for page fault or access fault
                    // send exception using ldu_cq ROB_index
                    // just like a killed load op, writeback garbage to dest PR
                // if no applicable io nor mem fence then can do second try launch to dcache, mark as waiting for dcache if get launch arbitrated
                    // also launch stamofu_cq CAM
                    // when all launches done, also send complete to ROB
                // else, need to wait, mark entry as waiting for fence clear
        // ldu_cq/ldu_mq fence clear
            // implies already got dTLB resp, on first cycle or late, and found applicable io or mem fence
            // wait until load older than oldest applicable io vs. mem fence
                // can do second try launch to dcache, mark as waiting for dcache if get launch arbitrated
        // ldu_cq/ldu_mq dcache resp
            // implies already got dTLB resp and already waited for applicable io vs. mem fence
            // dcache hit means dcache resp might arrive before stamofu_cq CAM depending on how timing ends up working out
                // if have store set, or maybe always, buffer dcache val(s)
            // wait until get dcache resp
                // if got forward from stamofu_cq + stamofu_mq CAM, ignore dcache resp
                    // must have been full match, else would have been completely restarted
                // else, if entry has store set which is not resolved
                    // buffer dcache resp data
                    // have ROB index to wait until in order for entry to be marked ready for reg write
                // else, free to perform dcache resp reg write
                    // buffer dcache resp data
                    // mark entry as ready for reg write
                // need 2x dcache resp if misaligned
                    // still perform single reg write
                        // must combine ldu_cq + ldu_mq values
                        // dcache needs to uniquely identify return, maybe designate to dcache if should write to mq vs. cq
        // ldu_cq CAM of stamofu_cq and stamofu_mq resp
            // launched after get dTLB resp(s)
                // so essentially, the official launch after pipeline launch is verified by dTLB
                    // REQ stage launch from pipeline if get immediate dTLB hit
                    // second try launch
                // need good PA
            // one CAM per aligned access
                // misaligned does 2 CAM's:
                    // 1 launched by ldu_cq on first launch dTLB resp
                    // 1 launched by ldu_mq on second launch dTLB resp
            // info given:
                // dependent data (partial or complete)
                // oldest ROB_index took dependent data from
                    // need so that if get restart check, know if restart has younger data
                // existence of remaining older ambigious stores to same store set
                    // indicates if should stay waiting for restart or commit of older store set
                    // wait to perform reg write
                    // keep current bufferred data and collect restart data accordingly
                // if any amo byte has youngest data, clear buffered data and mark entry as needing to wait for amo commit to do second launch
        // ldu_cq wait for CAM of preceding stamofu_cq entries
            // stamofu_cq CAM of ldu_cq + ldu_mq
                // check for oldest entry which has given reg write data
                    // if store: give new reg write data
                    // if amo: clear buffered data and mark entry as needing to wait for amo commit to do second launch
                    // restart after load
                // otherwise if no matching have given reg write data, entries are updated
                    // if store: update byte masked data if relevant to store
                        // updates must happen to all relevant stores, not just single of interest
                        // mark any ldu_cq/ldu_mq entries which misbehave and report if there is a restart case
                        // update cases:
                            // check for already have forward from younger stores -> ignore update
                                // from oldest ROB_index took dependent data from ^
                            // update of ldu_cq entry with full match
                                // freely accept update, which now is implied to be the youngest store seen so far
                            // update of ldu_cq entry with partial match
                                // check no dependent data from before
                                    // if have dcache data, can freely accept update
                                    // if don't have dcache data, completely restart this load
                                        // only have mechanism to update from dcache data,
                                        // not get update first then fill in non-updated after
                                        // uncommon case since misaligned forwarding with dcache miss
                                // otherwise, haven't kept track of which bytes are which ages, completely restart this load
                                    // don't know which bytes to update as only have oldest ROB_index took dependent from
                                    // uncommonish case since partial match and late store completion
                                // consider simplification: just completely restart all partial matches
                                // alternate simplification: partial matches lead to clear buffered data and mark entry as needing to wait for load commit to do second launch
                    // if amo: clear buffered data and mark entry as needing to wait for amo commit to do second launch
            // wait until get expected stamofu_cq entry CAM of interest following youngest older ROB_index in store set
                // ldu_cq and ldu_mq entries which were waiting on the stamofu_cq entry for store set
                    // independent check from CAM logic, where just check ldu_cq entries if this stamofu_cq entry is the ROB_index of interest
                    // mark ready for reg write
                        // regardless of if this entry CAM actually does update or not
        // ldu_cq wait for commit of this ldu_cq entry
            // ROB will broadcast upper5 ROB index to mark committed
                // unlike stores, no new functionality or launches, so want to delete entries in parallel if possible
                    // especially desired since pretty likely that have multiple loads in 4-way ROB entry
            // ldu_cq entry functionality now done
            // ldu_cq head will be allowed to advance on next cycle when see committed state


    // Store Path:
        // enqueue into stamofu_dq
            // 4-way in-order
        // waiting to dequeue from stamofu_dq
            // track operands becoming ready while in stamofu_dq
                // no forwarding, only mark as individual operand ready
        // dequeue from stamofu_dq, enqueue into stamofu_cq
            // 1-way in-order
            // track operands becoming ready while in ldu_dq
                // no forwarding, only mark as individual operand ready
        // waiting to issue from stamofu_cq
            // check next issue ready
                // check current operand states
                    // track next operand(s) becoming ready while in stamofu_cq
                        // no forwarding, only mark as operand(s) ready
                    // if operands still not ready, still not issuable
            // while have issue ready, wait until turn to issue into stamofu_pipeline
        // issue from stamofu_cq into stamofu_pipeline (IS stage)
            // no issue if stamofu_pipeline stalled
            // PE on issuable entries
            // select issuing entry following oldest issuable
                // masked lowest else unmasked lowest
            // mark next stamofu_cq state as issued
        // stamofu_pipeline PR stage
            // PRF Request stage
                // other FU's would do prf request on IS,
                // but stamofu_cq is too big to do issue and prf req same-cycle
            // this stage knows which operands needed given op
            // stall here and don't send request if OC stall
        // stamofu_pipeline OC stage
            // Operand Collection stage
            // wait for operand read ack, read it from the associated read bank and port
        // stamofu_pipeline AC stage
            // Address Calculation stage
            // A operand + imm, B operand
            // mark relevant word addresses and bitmasks for dependence checking
            // determine if need 2x store complete
                // misaligned such that need 2x word-aligned access
                // when pipeline unstalled, send first complete to PC stage, keep second complete in AC stage
        // stamofu_pipeline PC stage
            // Pipeline Complete stage
            // dTLB req
                // can stall if dTLB ran out of MSHR's
            // mark stamofu_cq entry as operands collected and waiting for dTLB resp
            // need 2x store complete for misaligned
                // first complete guaranteed
                // second complete can stall if there is no stamofu_mq entry
                // when second complete happens allocate stamofu_mq entry, set symmetric pointers b/w stamofu_mq entry and stamofu_cq entry
        // stamofu_cq + stamofu_mq dTLB resp
            // wait until dTLB resp returns
                // check for page fault or access fault
                    // send exception using stamofu_cq ROB_index
                // perform CAM of ldu_cq + ldu_mq
                    // described above
                    // this CAM'ing doesn't affect stamofu_cq + stamofu_mq
                // when all dTLB resp's come in (stamofu_cq entry and stamofu_mq entry if applicable), send complete to ROB
        // ldu_cq CAM of stamofu_cq + stamofu_mq
            // described above
            // this CAM'ing doesn't affect stamofu_cq + stamofu_mq entry values, only reads them
        // stamofu_cq wait for launch of this stamofu_cq (+ stamofu_mq) entry to dcache
            // ROB will signal commit for stamofu_cq head to launch
                // launch store to write buffer
                // dequeue from stamofu_cq and stamofu_mq
                // perform 2x launch if misaligned
                    // first launch from stamofu_cq
                    // second launch from stamofu_mq


    // AMO path:
        // enqueue into stamofu_dq
            // 4-way in-order
        // waiting to dequeue from stamofu_dq
            // track operands becoming ready while in stamofu_dq
                // no forwarding, only mark as individual operands ready
        // dequeue from stamofu_dq, enqueue into stamofu_cq
            // 1-way in-order
            // track operands becoming ready while in stamofu_dq
                // no forwarding, only mark as individual operands ready
            // stall if have mem_aq + io_aq and don't have open entry in both of mem_aq_q and io_aq_q
            // otherwise if not stall, enqueue onto mem_aq_q and io_aq_q if have
        // waiting to issue from stamofu_cq
            // check next issue ready
                // check current operand states
                    // track next operand(s) becoming ready while in stamofu_cq
                        // no forwarding, only mark as operand(s) ready
                    // if operands still not ready, still not issuable
            // while have issue ready, wait until turn to issue into stamofu_pipeline
        // issue from stamofu_cq into stamofu_pipeline (IS stage)
            // no issue if stamofu_pipeline stalled
            // PE on issuable entries
            // select issuing entry following oldest issuable
                // masked lowest else unmasked lowest
            // mark next stamofu_cq state as issued
        // stamofu_pipeline PR stage
            // PRF Request stage
                // other FU's would do prf request on IS,
                // but stamofu_cq is too big to do issue and prf req same-cycle
            // this stage knows which operands needed given op
            // stall here and don't send request if OC stall
        // stamofu_pipeline OC stage
            // Operand Collection stage
            // wait for operand read ack, read it from the associated read bank and port
        // stamofu_pipeline AC stage
            // Address Calculation stage
            // A operand, B operand
            // mark relevant word addresses and bitmaks for dependence checking
            // amo's not allowed to be misaligned
                // check if misaligned, prep to send misaligned exception on complete
        // stamofu_pipeline PC stage
            // Pipeline Complete stage
            // dTLB req
                // can stall if dTLB ran out of MSHR's
            // mark stamofu_cq entry as operands collected and waiting for dTLB resp
            // amo's not allowed to be misaligned
                // guaranteed single complete
                // if misaligned, use stamofu_cq entry ROB_index to send misaligned exception to ROB
        // stamofu_cq dTLB resp
            // wait until dTLB resp returns
                // check for page fault or access fault
                    // send exception using stamofu_cq ROB_index
                // perform CAM of ldu_cq + ldu_mq
                    // described above
                    // this CAM'ing doesn't affect stamofu_cq
                // now know specifically if in mem vs. io
                    // update mem_aq_q and io_aq_q
                        // if applicable, one will see dequeue, which loads will react to naturally when dequeue propagates,
                        // potentially enabling loads for second launch
                    // update stamofu_cq entry mem_rl and io_rl rules
                        // if applicable, one will be cleared
        // ldu_cq CAM of stamofu_cq
            // described above
            // this CAM'ing doesn't affect stamofu_cq entry values, only reads them
        // stamofu_cq wait for launch of this stamofu_cq entry to dcache
            // ROB will signal commit for stamofu_cq head to launch
            // stall following mem_rl and io_rl if write buffer has any mem or io entries, respectively
            // if no stall, launch amo to amo unit
        // stamofu_cq wait for dcache resp
            // send reg write
            // broadcast ROB_index so loads waiting for amo commit can do second launch
                // maybe can highjack stamofu_cq CAM of ldu_cq + ldu_mq
                // else, need additional broadcast just for this case (which should be rare)
            // clear associated mem_aq_q and io_aq_q entries
            // dequeue from stamofu_cq


    // fence path:
        // enqueue into stamofu_dq
            // 4-way in-order
        // waiting to dequeue from stamofu_deq
            // track operands becoming ready while in stamofu_dq
                // no forwarding, only mark as individual operands ready
        // dequeue from stamofu_dq, enqueue into stamofu_cq
            // 1-way in-order
            // track operands becoming ready while in stamofu_dq
                // no forwarding, only mark as individual operands ready
            // stall for relevant aq q(s) full
                // mem_aq -> mem_aq_q
                // io_aq -> io_aq_q
            // otherwise if not stall, enqueue onto mem_aq_q and/or io_aq_q if have
            // for non-sfence.vma, enter stamofu_cq as already complete, skip upcoming stamofu_pipeline steps
        // waiting to issue from stamofu_cq if sfence.vma
            // check next issue ready
                // check current operand states
                    // track next operand(s) becoming ready while in stamofu_cq
                        // no forwarding, only mark as operand(s) ready
                    // if operands still not ready, still not issuable
            // while have issue ready, wait until turn to issue into stamofu_pipeline
        // issue from stamofu_cq into stamofu_pipeline if sfence.vma (IS stage)
            // no issue if stamofu_pipeline stalled
            // PE on issuable entries
            // select issuing entry following oldest issuable
                // masked lowest else unmasked lowest
            // mark next stamofu_cq state as issued
        // stamofu_pipeline PR stage if sfence.vma
            // PRF Request stage
                // other FU's would do prf request on IS,
                // but stamofu_cq is too big to do issue and prf req same-cycle
            // this stage knows which operands needed given op
            // stall here and don't send request if OC stall
        // stamofu_pipeline OC stage if sfence.vma
            // Operand Collection stage
            // wait for operand read ack, read it from the associated read bank and port
        // stamofu_pipeline AC stage if sfence.vma
            // Address Calculation stage
            // A operand, B operand
        // stamofu_pipeline PC stage if sfence.vma
            // Pipeline Complete stage
            // mark stamofu_cq entry as complete
        // ldu_cq CAM of stamofu_cq
            // ignores fence's
        // stamofu_cq wait for commit of this stamofu_cq entry
            // ROB will signal commit for stamofu_cq head to clear fence
            // stall mem_rl and io_rl if write buffer has any mem or io entries, respectively
            // fence.i and sfence.vma send restart to frontend when done
                // sfence.vma sends iTLB + dTLB invalidation, stalls until invalidation done
            // if stalls done:
                // clear associated mem_aq_q and io_aq_q entries
                // dequeue from stamofu_cq


    // structures:

        // can check for queue wraparound but keep ROB index ordering:
            // mask off entries past queue head ptr, these are first priority as younger
                // lsb order among these
            // else, all unmasked entries
                // lsb order among these

        // ldu:

            // ldu_dq
                // Dispatch Queue

            // ldu_iq
                // Issue Queue

            // ldu_pipeline
                // pipeline for:
                    // operand collection
                    // address calculation
                    // ldu_mq allocation
                    // dTLB lookup
                    // (initial) dcache launch
                    // stamofu CAM

            // ldu_cq
                // Central Queue

            // ldu_mq
                // Misaligned Queue

        // stamofu:

            // stamofu_dq
                // Dispatch Queue

            // stamofu_iq
                // Issue Queue

            // stamofu_pipeline
                // pipeline for:
                    // operand collection
                    // address calculation
                    // stamofu_mq allocation
                    // dTLB lookup
                    // ldu CAM

            // stamofu_cq
                // Central Queue

            // stamofu_mq
                // Misaligned Queue

            // stamofu_aq
                // Acquire Queue
                // reference via ROB index
                // enq on dq launch
                // update after iq finds out address region via ROB index
                // on commit, delete from entry 0 if still in aq -> check matching ROB index


    // misc:

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

        // seriously consider using LQ_index, SQ_index paradigm as this makes the age check much simpler for the CAM's
            // in theory is tractable as have only 1-way launch to each *_cq each cycle
            // issue is can get things OoO b/w *_cq's due to time in *_dq's
            // maybe can use counters to infer indexes
                // can get issues w/ full buffer
                    // if either full, stall both *_dq's?
                // analyze

        // probably want specific dTLB miss queue so that can localize determination of next dcache launch
            // dTLB miss queue right after pipeline
            // hold PA's right there, can choose between short list of dTLB misses which are currently returning vs. pipeline output
            // can easily freeze pipeline if have dTLB miss return
            // uncommon case anyway

        // killed loads need to complete their writes so that dependent garbage instructions in other pipelines can finish
            // mark if load or store killed in dispatch queue, pass info to central queue's accordingly
                // can skip issue queues if killed this early

endmodule
