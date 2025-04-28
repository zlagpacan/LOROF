/*
    Filename: checkpoint_array.sv
    Author: zlagpacan
    Description: RTL for Checkpoint Array
    Spec: LOROF/spec/design/checkpoint_array.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module checkpoint_array #(
    parameter CHECKPOINT_COUNT = 8,
    parameter CHECKPOINT_INDEX_WIDTH = $clog2(CHECKPOINT_COUNT),
    parameter CHECKPOINT_THRESHOLD = 4
) (
    // seq
    input logic CLK,
    input logic nRST,

    // checkpoint save
    input logic                                     save_valid,
    input logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]    save_map_table,
    input logic [LH_LENGTH-1:0]                     save_LH,
    input logic [GH_LENGTH-1:0]                     save_GH,
    input logic [RAS_INDEX_WIDTH-1:0]               save_ras_index,

    output logic                                    save_ready,
    output logic [CHECKPOINT_INDEX_WIDTH-1:0]       save_index,

    // checkpoint restore
    input logic [CHECKPOINT_INDEX_WIDTH-1:0]        restore_index,
    input logic                                     restore_clear,

    output logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]   restore_map_table,
    output logic [LH_LENGTH-1:0]                    restore_LH,
    output logic [GH_LENGTH-1:0]                    restore_GH,
    output logic [RAS_INDEX_WIDTH-1:0]              restore_ras_index,

    // advertized threshold
    output logic above_threshold
);

    // ----------------------------------------------------------------
    // Signals:

    logic save_success;

    logic [CHECKPOINT_COUNT-1:0] valid_array;
    logic [CHECKPOINT_COUNT-1:0] new_valid_array;
    logic [CHECKPOINT_COUNT-1:0] keep_valid_array;

    // ----------------------------------------------------------------
    // Helper Logic:

    pe_lsb #(
        .WIDTH(CHECKPOINT_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(1)
    ) SAVE_PE (
        .req_vec(~valid_array & {CHECKPOINT_COUNT{save_valid}}),
        .ack_one_hot(new_valid_array),
        .ack_index(save_index)
    );

    majority #(
        .WIDTH(CHECKPOINT_COUNT),
        .THRESHOLD(CHECKPOINT_THRESHOLD)
    ) AVAILABLE_MAJORITY (
        .vec(~valid_array),
        .above_threshold(above_threshold)
    );

    assign save_ready = |(~valid_array);
    assign save_success = save_valid & save_ready;

    always_comb begin
        keep_valid_array = '1;
        if (restore_clear) begin
            keep_valid_array[restore_index] = 1'b0;
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            valid_array <= '0;
        end
        else begin
            valid_array <= (valid_array | new_valid_array) & keep_valid_array;
        end
    end
    
    // ----------------------------------------------------------------
    // Mem Array:

    distram_1rport_1wport #(
        .INNER_WIDTH(
            AR_COUNT*LOG_PR_COUNT
            + LH_LENGTH
            + GH_LENGTH
            + RAS_INDEX_WIDTH
        ),
        .OUTER_WIDTH(CHECKPOINT_COUNT)
    ) CHECKPOINT_ARRAY (
        .CLK(CLK),

        .rindex(restore_index),
        .rdata({restore_map_table, restore_LH, restore_GH, restore_ras_index}),

        .wen(save_success),
        .windex(save_index),
        .wdata({save_map_table, save_LH, save_GH, save_ras_index})
    );

endmodule