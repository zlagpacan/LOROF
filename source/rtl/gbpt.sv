/*
    Filename: gbpt.sv
    Author: zlagpacan
    Description: RTL for Global Branch Prediction Table
    Spec: LOROF/spec/design/gbpt.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module gbpt (

    // seq
    input logic CLK,
    input logic nRST,

    // RESP stage
    input logic                     valid_RESP,
    input logic [31:0]              full_PC_RESP,
    input logic [GH_LENGTH-1:0]     GH_RESP,
    input logic [ASID_WIDTH-1:0]    ASID_RESP,

    // RESTART stage
    output logic pred_taken_RESTART,

    // Update 0
    input logic                     update0_valid,
    input logic [31:0]              update0_start_full_PC,
    input logic [GH_LENGTH-1:0]     update0_GH,
    input logic [ASID_WIDTH-1:0]    update0_ASID,
    input logic                     update0_taken,

    // Update 1
    output logic update1_correct
);

    // ----------------------------------------------------------------
    // Signals:

    // RESP Stage:
    logic [GBPT_INDEX_WIDTH-1:0]            hashed_index_RESP;
    logic [LOG_GBPT_ENTRIES_PER_BLOCK-1:0]  entry_RESP;

    // RESTART Stage:
    logic [LOG_GBPT_ENTRIES_PER_BLOCK-1:0]      entry_RESTART;
    logic [GBPT_ENTRIES_PER_BLOCK-1:0][1:0]     array_pred_2bc_by_entry_RESTART;

    // Update 0:
    logic [GBPT_INDEX_WIDTH-1:0]            update0_hashed_index;
    logic [LOG_GBPT_ENTRIES_PER_BLOCK-1:0]  update0_hashed_entry;

    // Update 1:
    logic                                       update1_valid; // use instead of byte mask
    logic [GBPT_INDEX_WIDTH-1:0]                update1_hashed_index;
    logic [LOG_GBPT_ENTRIES_PER_BLOCK-1:0]      update1_hashed_entry;
    logic                                       update1_taken;

    logic [GBPT_ENTRIES_PER_BLOCK-1:0][1:0]     update1_array_old_pred_2bc_by_entry;
    logic [GBPT_ENTRIES_PER_BLOCK-1:0][1:0]     update1_array_new_pred_2bc_by_entry;

    logic                                       last_update1_conflict;
    logic [GBPT_ENTRIES_PER_BLOCK-1:0][1:0]     last_update1_array_new_pred_2bc_by_entry;

    // ----------------------------------------------------------------
    // RESP Stage Logic:

    gbpt_index_hash GBPT_RESP_INDEX_HASH (
        .PC(full_PC_RESP),
        .GH(GH_RESP),
        .ASID(ASID_RESP),
        .index({hashed_index_RESP, entry_RESP})
    );

    // ----------------------------------------------------------------
    // RESTART Stage Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
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

    gbpt_index_hash GBPT_UPDATE0_INDEX_HASH (
        .PC(update0_start_full_PC),
        .GH(update0_GH),
        .ASID(update0_ASID),
        .index({update0_hashed_index, update0_hashed_entry})
    );

    // ----------------------------------------------------------------
    // Update 1 Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            update1_valid <= 1'b0;
            update1_hashed_index <= '0;
            update1_hashed_entry <= '0;
            update1_taken <= 1'b0;

            last_update1_conflict <= 1'b0;
            last_update1_array_new_pred_2bc_by_entry <= '0;
        end
        else begin
            update1_valid <= update0_valid;
            update1_hashed_index <= update0_hashed_index;
            update1_hashed_entry <= update0_hashed_entry;
            update1_taken <= update0_taken;

            last_update1_conflict <= update0_valid & update1_valid & update0_hashed_index == update1_hashed_index;
            last_update1_array_new_pred_2bc_by_entry <= update1_array_new_pred_2bc_by_entry;
        end
    end

    // bit 1 of 2bc is taken vs. not taken prediction
    assign update1_correct = update1_array_old_pred_2bc_by_entry[update1_hashed_entry][1] == update1_taken;

    always_comb begin

        // RMW pred 2bc for this set
            // make 2bc state update
            // if conflicted last cycle, use update value from last cycle
        if (last_update1_conflict) begin
            update1_array_new_pred_2bc_by_entry = last_update1_array_new_pred_2bc_by_entry;
        end else begin
            update1_array_new_pred_2bc_by_entry = update1_array_old_pred_2bc_by_entry;
        end
        
        // update 2bc entry of interest
        case ({update1_array_new_pred_2bc_by_entry[update1_hashed_entry], update1_taken})
            3'b000: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b00; // SN -> N -> SN
            3'b001: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b01; // SN -> T -> WN
            3'b010: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b00; // WN -> N -> SN
            3'b011: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b11; // WN -> T -> ST
            3'b100: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b00; // WT -> N -> SN
            3'b101: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b11; // WT -> T -> ST
            3'b110: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b10; // ST -> N -> WT
            3'b111: update1_array_new_pred_2bc_by_entry[update1_hashed_entry] = 2'b11; // ST -> T -> ST
        endcase
    end

    // ----------------------------------------------------------------
    // RAM Arrays:

    /////////////////////////////////////
    // BRAM Array shared over Entries: //
    /////////////////////////////////////

    bram_2rport_1wport #(
        .INNER_WIDTH(
            GBPT_ENTRIES_PER_BLOCK *
            2
        ),
        .OUTER_WIDTH(GBPT_SETS)
    ) GBPT_BRAM_ARRAY (
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