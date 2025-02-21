/*
    Filename: lbpt.sv
    Author: zlagpacan
    Description: RTL for Local Branch Prediction Table
    Spec: LOROF/spec/design/lbpt.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module lbpt (

    // seq
    input logic CLK,
    input logic nRST,

    // RESP stage
    input logic                     valid_RESP,
    input logic [31:0]              full_PC_RESP,
    input logic [LH_LENGTH-1:0]     LH_RESP,
    input logic [ASID_WIDTH-1:0]    ASID_RESP,

    // RESTART stage
    output logic pred_taken_RESTART,

    // Update 0
    input logic                     update0_valid,
    input logic [31:0]              update0_start_full_PC,
    input logic [LH_LENGTH-1:0]     update0_LH,
    input logic [ASID_WIDTH-1:0]    update0_ASID,
    input logic                     update0_taken,

    // Update 1
    output logic update1_correct
);

    // ----------------------------------------------------------------
    // Signals:

    // RESP Stage:
    logic [LBPT_INDEX_WIDTH-1:0]            hashed_index_RESP;
    logic [LOG_LBPT_ENTRIES_PER_BLOCK-1:0]  entry_RESP;

    // RESTART Stage:
    logic [LOG_LBPT_ENTRIES_PER_BLOCK-1:0]      entry_RESTART;
    logic [LBPT_ENTRIES_PER_BLOCK-1:0][1:0]     array_pred_2bc_by_entry_RESTART;

    // Update 0:
    logic [LBPT_INDEX_WIDTH-1:0]            update0_hashed_index;
    logic [LOG_LBPT_ENTRIES_PER_BLOCK-1:0]  update0_entry;

    // Update 1:
    logic                                       update1_valid; // use instead of byte mask
    logic [LBPT_INDEX_WIDTH-1:0]                update1_hashed_index;
    logic [LOG_LBPT_ENTRIES_PER_BLOCK-1:0]      update1_entry;
    logic                                       update1_taken;

    logic [LBPT_ENTRIES_PER_BLOCK-1:0][1:0]     update1_array_old_pred_2bc_by_entry;
    logic [LBPT_ENTRIES_PER_BLOCK-1:0][1:0]     update1_array_new_pred_2bc_by_entry;

    // ----------------------------------------------------------------
    // RESP Stage Logic:

    assign entry_RESP = full_PC_RESP[LOG_LBPT_ENTRIES_PER_BLOCK+1-1 : 1];

    lbpt_index_hash LBPT_RESP_INDEX_HASH (
        .PC(full_PC_RESP),
        .LH(LH_RESP),
        .ASID(ASID_RESP),
        .index(hashed_index_RESP)
    );

    // ----------------------------------------------------------------
    // RESTART Stage Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            entry_RESTART <= '0;
        end
        else begin
            entry_RESTART <= entry_RESP;
        end
    end

    // bit 1 of 2bc is taken vs. not taken prediction
    assign pred_taken_RESTART = array_pred_2bc_by_entry_RESTART[entry_RESTART][1];

    // ----------------------------------------------------------------
    // Update 0 Logic:

    assign update0_entry = update0_start_full_PC[LOG_LBPT_ENTRIES_PER_BLOCK+1-1 : 1];

    lbpt_index_hash LBPT_UPDATE0_INDEX_HASH (
        .PC(update0_start_full_PC),
        .LH(update0_LH),
        .ASID(update0_ASID),
        .index(update0_hashed_index)
    );

    // ----------------------------------------------------------------
    // Update 1 Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            update1_valid <= 1'b0;
            update1_hashed_index <= '0;
            update1_entry <= '0;
            update1_taken <= 1'b0;
        end
        else begin
            update1_valid <= update0_valid;
            update1_hashed_index <= update0_hashed_index;
            update1_entry <= update0_entry;
            update1_taken <= update0_taken;
        end
    end

    // bit 1 of 2bc is taken vs. not taken prediction
    assign update1_correct = update1_array_old_pred_2bc_by_entry[update1_entry][1] == update1_taken;

    always_comb begin

        // copy old 2bc entries
        update1_array_new_pred_2bc_by_entry = update1_array_old_pred_2bc_by_entry;
        
        // update 2bc entry of interest
        case ({update1_array_old_pred_2bc_by_entry[update1_entry], update1_taken})
            3'b000: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b00; // SN -> N -> SN
            3'b001: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b01; // SN -> T -> WN
            3'b010: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b00; // WN -> N -> SN
            3'b011: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b11; // WN -> T -> ST
            3'b100: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b00; // WT -> N -> SN
            3'b101: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b11; // WT -> T -> ST
            3'b110: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b10; // ST -> N -> WT
            3'b111: update1_array_new_pred_2bc_by_entry[update1_entry] = 2'b11; // ST -> T -> ST
        endcase
    end

    // ----------------------------------------------------------------
    // RAM Arrays:

    /////////////////////////////////////
    // BRAM Array shared over Entries: //
    /////////////////////////////////////

    bram_2rport_1wport #(
        .INNER_WIDTH(
            LBPT_ENTRIES_PER_BLOCK *
            2
        ),
        .OUTER_WIDTH(LBPT_SETS)
    ) LBPT_BRAM_ARRAY (
        .CLK(CLK),
        .nRST(nRST),
        
        .port0_ren(valid_RESP),
        .port0_rindex(hashed_index_RESP),
        .port0_rdata(array_pred_2bc_by_entry_RESTART),
        
        .port1_ren(update0_valid),
        .port1_rindex(update0_hashed_index),
        .port1_rdata(update1_array_old_pred_2bc_by_entry),

        .wen_byte(update1_valid),
        .windex(update1_hashed_index),
        .wdata(update1_array_new_pred_2bc_by_entry)
    );

endmodule