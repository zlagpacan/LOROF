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
        // true head must wait for all instr's to be complete
        // unexceptable head just waits until no exception or misprediction possible for instr
            // ALU
            // for sys, when marked complete
                // unless strict with when load marked as complete, (e.g. when no earlier stores are ambigious,
                // which means need another SQ CAM -> NO) then all loads are exceptable until the stores
                // older than them are all complete
                    // this functionality relies on stores only being marked as complete 

    // pretty sure just need unexceptable head, which can then be the true head
        // potential consequences
            // registers are freed earlier
                // this is good if possible
                // ALL INSTR'S MUST BE DONE WITH OLD VALUES
        // "unexceptable" for this purpose then requires that operands have been read
        // since doing no instr kills in non-mem and non-sys pipelines, seems like forced to just wait
            // for non-mem and non-sys to be fully complete before move on unexceptable head

endmodule