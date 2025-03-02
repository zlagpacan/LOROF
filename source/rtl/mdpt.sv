/*
    Filename: mdpt.sv
    Author: zlagpacan
    Description: RTL for Memory Dependence Prediction Table
    Spec: LOROF/spec/design/mdpt.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module mdpt (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage
    input logic                     valid_REQ,
    input logic [31:0]              full_PC_REQ,
    input logic [ASID_WIDTH-1:0]    ASID_REQ,

    // RESP stage
    output logic [MDPT_ENTRIES_PER_BLOCK-1:0]   dep_pred_by_instr_RESP,

    // Dep Update 0 stage
    input logic                     dep_update0_valid,
    input logic [31:0]              dep_update0_start_full_PC,
    input logic [ASID_WIDTH-1:0]    dep_update0_ASID,
    input logic                     dep_update0_dep_truth 
);

    // ----------------------------------------------------------------
    // Signals:

    // REQ Stage:
    logic [MDPT_INDEX_WIDTH-1:0] hashed_index_REQ;

    // RESP Stage:
    logic [MDPT_ENTRIES_PER_BLOCK-1:0][1:0] array_dep_pred_2bc_by_instr_RESP;

    // Dep Update 0:
    logic [MDPT_INDEX_WIDTH-1:0]            dep_update0_hashed_index;
    logic [LOG_MDPT_ENTRIES_PER_BLOCK-1:0]  dep_update0_instr;

    // Dep Update 1:
    logic                                   dep_update1_valid;
    logic [MDPT_INDEX_WIDTH-1:0]            dep_update1_hashed_index;
    logic [LOG_MDPT_ENTRIES_PER_BLOCK-1:0]  dep_update1_instr;
    logic                                   dep_update1_dep_truth;

    logic [MDPT_ENTRIES_PER_BLOCK-1:0][1:0]     dep_update1_array_old_dep_pred_2bc_by_instr;
    logic [MDPT_ENTRIES_PER_BLOCK-1:0][1:0]     dep_update1_array_new_dep_pred_2bc_by_instr;

    logic                                       last_dep_update1_conflict;
    logic [MDPT_ENTRIES_PER_BLOCK-1:0][1:0]     last_dep_update1_array_new_dep_pred_2bc_by_instr;

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    mdpt_index_hash MDPT_REQ_INDEX_HASH (
        .PC(full_PC_REQ),
        .ASID(ASID_REQ),
        .index(hashed_index_REQ)
    );

    // ----------------------------------------------------------------
    // RESP Stage Logic:

    always_comb begin
        for (int i = 0; i < 8; i++) begin
            // dep pred if bit 1 or bit 0 are asserted
            dep_pred_by_instr_RESP[i] = |array_dep_pred_2bc_by_instr_RESP[i][1:0];
        end
    end

    // ----------------------------------------------------------------
    // Dep Update 0 Logic:

    assign dep_update0_instr = dep_update0_start_full_PC[LOG_MDPT_ENTRIES_PER_BLOCK + 1 - 1: 1];

    mdpt_index_hash MDPT_DEP_UPDATE0_INDEX_HASH(
        .PC(dep_update0_start_full_PC),
        .ASID(dep_update0_ASID),
        .index(dep_update0_hashed_index)
    );

    // ----------------------------------------------------------------
    // Update 1 Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            dep_update1_valid <= 1'b0;
            dep_update1_hashed_index <= '0;
            dep_update1_instr <= '0;
            dep_update1_dep_truth <= 1'b0;

            last_dep_update1_conflict <= 1'b0;
            last_dep_update1_array_new_dep_pred_2bc_by_instr <= '0;
        end
        else begin
            dep_update1_valid <= dep_update0_valid;
            dep_update1_hashed_index <= dep_update0_hashed_index;
            dep_update1_instr <= dep_update0_instr;
            dep_update1_dep_truth <= dep_update0_dep_truth;

            last_dep_update1_conflict <= dep_update0_valid & dep_update1_valid & dep_update0_hashed_index == dep_update1_hashed_index;
            last_dep_update1_array_new_dep_pred_2bc_by_instr <= dep_update1_array_new_dep_pred_2bc_by_instr;
        end
    end

    always_comb begin

        // RMW dep pred 2bc for this set
            // make 2bc state update
            // if conflicted last cycle, use update value from last cycle
        if (last_dep_update1_conflict) begin
            dep_update1_array_new_dep_pred_2bc_by_instr = last_dep_update1_array_new_dep_pred_2bc_by_instr;
        end else begin
            dep_update1_array_new_dep_pred_2bc_by_instr = dep_update1_array_old_dep_pred_2bc_by_instr;
        end

        // update 2bc entry of interest
        case ({dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr], dep_update1_dep_truth})
            3'b000: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b00; // stay no dep
            3'b001: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b11; // skip to full dep
            3'b010: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b00; // decrement to no dep
            3'b011: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b11; // skip to full dep
            3'b100: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b01; // decrement to 01 dep
            3'b101: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b11; // skip to full dep
            3'b110: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b10; // decrement to 10 dep
            3'b111: dep_update1_array_new_dep_pred_2bc_by_instr[dep_update1_instr] = 2'b11; // stay in full dep
        endcase
    end

    // ----------------------------------------------------------------
    // RAM Arrays:

    /////////////////////////////////////
    // BRAM Array shared over Entries: //
    /////////////////////////////////////

    bram_2rport_1wport #(
        .INNER_WIDTH(
            MDPT_ENTRIES_PER_BLOCK *
            2
        ),
        .OUTER_WIDTH(MDPT_SETS)
    ) MDPT_BRAM_ARRAY (
        .CLK(CLK),
        .nRST(nRST),
        
        .port0_ren(valid_REQ),
        .port0_rindex(hashed_index_REQ),
        .port0_rdata(array_dep_pred_2bc_by_instr_RESP),
        
        .port1_ren(dep_update0_valid),
        .port1_rindex(dep_update0_hashed_index),
        .port1_rdata(dep_update1_array_old_dep_pred_2bc_by_instr),

        .wen_byte({2{dep_update1_valid}}),
        .windex(dep_update1_hashed_index),
        .wdata(dep_update1_array_new_dep_pred_2bc_by_instr)
    );

endmodule