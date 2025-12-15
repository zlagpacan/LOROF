/*
    Filename: upct.sv
    Author: zlagpacan
    Description: RTL for Upper Program Counter Table
    Spec: LOROF/spec/design/upct.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module upct #(
    parameter UPCT_ENTRIES = 8,
    parameter LOG_UPCT_ENTRIES = $clog2(UPCT_ENTRIES)
) (

    // seq
    input logic CLK,
    input logic nRST,

    // RESP stage
    input logic                         read_valid_RESP,
    input logic [LOG_UPCT_ENTRIES-1:0]  read_index_RESP,

    output logic [UPCT_ENTRIES-1:0][UPPER_PC_WIDTH-1:0] upct_array,

    // Update 0
    input logic         update0_valid,
    input logic [31:0]  update0_target_full_PC,

    // Update 1
    output logic [LOG_UPCT_ENTRIES-1:0] update1_upct_index
);

    // ----------------------------------------------------------------
    // Signals:

    // FF Array:
    logic [UPCT_ENTRIES-1:0][UPPER_PC_WIDTH-1:0] next_upct_array;

    // PLRU:
    logic [UPCT_ENTRIES-2:0]        plru, next_plru;

    logic                           plru_new_valid;
    logic [LOG_UPCT_ENTRIES-1:0]    plru_new_index;
    logic                           plru_touch_valid;
    logic [LOG_UPCT_ENTRIES-1:0]    plru_touch_index;

    // Update 0:
    logic [UPPER_PC_WIDTH-1:0]  update0_upper_PC;
    logic [UPCT_ENTRIES-1:0]    update0_matching_upper_PC_by_entry;

    // Update 1:
    logic                           update1_valid;
    logic [UPPER_PC_WIDTH-1:0]      update1_upper_PC;
    logic                           update1_have_match;
    logic [UPCT_ENTRIES-1:0]        update1_matching_upper_PC_by_entry;
    logic [LOG_UPCT_ENTRIES-1:0]    update1_matching_index;

    // ----------------------------------------------------------------
    // Logic: 

    // FF's:
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            upct_array <= '0;

            plru <= '0;

            update1_valid <= 1'b0;
            update1_upper_PC <= '0;
            update1_matching_upper_PC_by_entry <= '1;
        end
        else begin
            upct_array <= next_upct_array;
            
            plru <= next_plru;

            update1_valid <= update0_valid;
            update1_upper_PC <= update0_upper_PC;
            update1_matching_upper_PC_by_entry <= update0_matching_upper_PC_by_entry;
        end
    end

    // Update 0 Logic:

    assign update0_upper_PC = update0_target_full_PC[31:32-UPPER_PC_WIDTH];

    always_comb begin

        // CAM over entries
        for (int i = 0; i < UPCT_ENTRIES; i++) begin
            update0_matching_upper_PC_by_entry[i] = upct_array[i] == update0_upper_PC;
        end
    end

    // Update 1 and RESP logic:

    assign update1_have_match = |update1_matching_upper_PC_by_entry;

    pe_lsb #(
        .WIDTH(8),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) CAM_PE (
        .req_vec(update1_matching_upper_PC_by_entry),
        .ack_index(update1_matching_index)
    );

    plru_updater #(
        .NUM_ENTRIES(8)
    ) PLRU (
        .plru_in(plru),
        .new_valid(plru_new_valid),
        .new_index(plru_new_index),
        .touch_valid(plru_touch_valid),
        .touch_index(plru_touch_index),
        .plru_out(next_plru)
    );

    always_comb begin

        // hold array and pointers by default
        next_upct_array = upct_array;

        // hold plru by default
        plru_new_valid = 1'b0;
        plru_touch_valid = 1'b0;
        plru_touch_index = update1_matching_index;

        // advertize PLRU index by default
        update1_upct_index = plru_new_index;

        // check update 1 hit
        if (update1_valid & update1_have_match) begin

            // advertize CAM matching index
            update1_upct_index = update1_matching_index;

            // adjust PLRU following matching index
            plru_touch_valid = 1'b1;
            plru_touch_index = update1_matching_index;
        end

        // check update 1 miss
        else if (update1_valid & ~update1_have_match) begin

            // advertize PLRU index
            update1_upct_index = plru_new_index;

            // update PLRU array entry
            next_upct_array[update1_upct_index] = update1_upper_PC;

            // adjust PLRU following current PLRU
            plru_new_valid = 1'b1;
        end

        // check RESP access
        else if (read_valid_RESP) begin

            // adjust PLRU following RESP index
            plru_touch_valid = 1'b1;
            plru_touch_index = read_index_RESP;
        end
    end

endmodule