/*
    Filename: rob.sv
    Author: zlagpacan
    Description: RTL for Reorder Buffer
    Spec: LOROF/spec/design/rob.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module rob #(
    parameter 
) (

    // seq
    input logic CLK,
    input logic nRST,
    
);

    // unexceptable head and true head
        // unexceptable head used to launch stores and AMO's
        // true head used to free registers and verify instruction completion
            // also safe to roll back architecture state with since know garbage value done being written
        // true head must wait for all instr's to be complete
        // unexceptable head just waits until no exception or misprediction possible for instr
            // ALU: technically don't need to wait as none are ever exceptable
            // BRU: when resolved
            // LDU: unexceptable once get dTLB resp
                // unless strict with when load marked as complete, (e.g. when no earlier stores are ambigious,
                // which means need another SQ CAM -> NO) then all loads are exceptable until the stores
                // older than them are all complete
                    // this functionality relies on stores only being marked as complete
            // STAMOFU: 
                // stores: once get dTLB resp
                    // need to make sure loads behind are restarted
                    // dTLB resp implies ldu_cq + ldu_mq CAM
                // AMO's: once get reg write
                    // dependent loads behind must wait until AMO returns so that can read updated value in dcache 
                    // heavy stall here
                // fence's: 
            // SYS: when CSR resolved

    // pretty sure just need unexceptable head, which can then be the true head
        // potential consequences
            // registers are freed earlier
                // this is good if possible
                // ALL INSTR'S MUST BE DONE WITH OLD VALUES
            // ROB commit from head no longer means can check expected processor state for instr
                // e.g. load may eventually come in after dcache miss but value isn't there yet, may have to wait fairly arbitrary time
                // actually I don't think this will work then because loads must wait stay in LQ until value comes back
                    // wait no it's fine because loads have commit broadcasted, just delay dequeue from LQ until also have returned value
                // this is solid reason not to do this
        // "unexceptable" for this purpose then requires that operands have been read
        // since doing no instr kills in non-mem and non-sys pipelines, seems like forced to just wait for non-mem and non-sys to be fully complete before move on unexceptable head
            // maybe not since guaranteed reg write happens
    
    // solid plan for now: use true head
        // perform commit when 4-way @ head complete
            // perform free's if exist
            // clear checkpoint if exists
            // launch stamofu
                // can only do 1 per cycle
                    // repeat as needed
                        // prolly invalidating entries as go anyway so will naturally move onto the next store on the next cycle
                // AMO's not fully complete until read returned, so head stalled
                // multiple stores in 4-way and AMO's are rare case, just eat the (potential) perf hit
                    // only a perf hit if ejection rate of stores/amos/fences or ROB capacity are limiters for program

    // on restart
        // can treat early and late restart the same
        // restore oldest checkpoint younger than restart if exists
        // then take control of map table to finish off rollback
            // serial rollback of 4-way entries get to desired 4-way entry
            // make changes required to get to state within desired 4-way entry 
            // this process should probably use head port
                // save head for later continuing of true commit
                // keep tail where it is so that younger garbage register writes and checkpoints
                // can get cleared out when they reach the head
                // i.e. never trample over anything in the ROB, let everything get to head, including garbage
                // head actions are now: 
                    // good instr, commit -> free old PR
                    // bad instr, rollback -> free new PR
                    // NO MAP TABLE CHANGES HERE

endmodule