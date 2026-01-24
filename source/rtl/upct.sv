/*
    Filename: upct.sv
    Author: zlagpacan
    Description: RTL for Upper Program Counter Table
    Spec: LOROF/spec/design/upct.md
*/

`include "corep.vh"

module upct (

    // seq
    input logic CLK,
    input logic nRST,

    // read in
    input logic                 read_valid,
    input corep::UPCT_idx_t     read_index,

    // read out
    output corep::UPC_t         read_upc,

    // update in
    input logic                 update_valid,
    input corep::UPC_t          update_upc,

    // update out
    output corep::UPCT_idx_t    update_upct_index
);

    // ----------------------------------------------------------------
    // Signals:

    // FF Array:
    corep::UPC_t [corep::UPCT_ENTRIES-1:0] upct_array, next_upct_array;

    // PLRU:
    logic [corep::UPCT_ENTRIES-2:0] plru, next_plru;

    logic               plru_new_valid;
    corep::UPCT_idx_t   plru_new_index;
    logic               plru_touch_valid;
    corep::UPCT_idx_t   plru_touch_index;

    // Updater:
    logic [corep::UPCT_ENTRIES-1:0]     update_matching_upc_by_entry;
    logic                               update_have_match;
    corep::UPCT_idx_t                   update_matching_index;

    // ----------------------------------------------------------------
    // Logic: 

    // FF's:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            upct_array <= '0;
            plru <= '0;
        end
        else begin
            upct_array <= next_upct_array;
            plru <= next_plru;
        end
    end

    // pc_gen read logic
    always_comb begin
        read_upc = upct_array[read_index];
    end

    // update logic:
    always_comb begin
        // CAM over entries
        for (int i = 0; i < corep::UPCT_ENTRIES; i++) begin
            update_matching_upc_by_entry[i] = upct_array[i] == update_upc;
        end
    end
    // pe_lsb_tree #(
    //     .WIDTH(corep::UPCT_ENTRIES)
    // ) CAM_PE (
    //     .req_vec(update_matching_upc_by_entry),
    //     .ack_valid(update_have_match),
    //     .ack_index(update_matching_index)
    // );
    one_hot_enc #(
        .WIDTH(corep::UPCT_ENTRIES)
    ) CAM_ONE_HOT_ENC (
        .one_hot_in(update_matching_upc_by_entry),
        .valid_out(update_have_match),
        .index_out(update_matching_index)
    );

    // array control:
    always_comb begin

        // hold array and pointers by default
        next_upct_array = upct_array;

        // hold plru by default
        plru_new_valid = 1'b0;
        plru_touch_valid = 1'b0;
        plru_touch_index = update_matching_index;

        // advertize PLRU index by default
        update_upct_index = plru_new_index;

        // check update hit
        if (update_valid & update_have_match) begin

            // advertize CAM matching index
            update_upct_index = update_matching_index;

            // adjust PLRU following matching index
            plru_touch_valid = 1'b1;
            plru_touch_index = update_matching_index;
        end

        // check update miss
        else if (update_valid) begin

            // advertize new PLRU index
            update_upct_index = plru_new_index;

            // update PLRU array entry
            next_upct_array[plru_new_index] = update_upc;

            // adjust PLRU following current PLRU
            plru_new_valid = 1'b1;
        end

        // check pc_gen access
        else if (read_valid) begin

            // adjust PLRU following pc_gen access index
            plru_touch_valid = 1'b1;
            plru_touch_index = read_index;
        end
    end

    plru_updater #(
        .NUM_ENTRIES(8)
    ) PLRU_UPDATER (
        .plru_in(plru),
        .new_valid(plru_new_valid),
        .new_index(plru_new_index),
        .touch_valid(plru_touch_valid),
        .touch_index(plru_touch_index),
        .plru_out(next_plru)
    );

endmodule