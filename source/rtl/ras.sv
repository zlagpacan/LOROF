/*
    Filename: ras.sv
    Author: zlagpacan
    Description: RTL for Return Address Stack
    Spec: LOROF/spec/design/ras.md
*/

`include "corep.vh"

module ras (

    // seq
    input logic CLK,
    input logic nRST,

    // pc_gen link control
    input logic                 link_valid,
    input corep::PC38_t         link_pc38,

    // pc_gen return control
    input logic                 ret_valid,
    output corep::PC38_t        ret_pc38,
    output corep::RAS_idx_t     ret_ras_index,

    // update control
    input logic                 update_valid,
    input corep::RAS_idx_t      update_ras_index
);

    // ----------------------------------------------------------------
    // Signals:

    // FF Array:
    corep::PC38_t [corep::RAS_ENTRIES-1:0] ras_array, next_ras_array;

    // RESP Stage:
    corep::RAS_idx_t sp, next_sp, sp_plus_1, sp_minus_1;

    // ----------------------------------------------------------------
    // Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            ras_array <= '0;
            sp <= 0;
        end
        else begin
            ras_array <= next_ras_array;
            sp <= next_sp;
        end
    end

    always_comb begin
        sp_plus_1 = sp + 1;
        sp_minus_1 = sp - 1;
    end

    always_comb begin

        // hold array by default
        next_ras_array = ras_array;

        // default hold sp
        next_sp = sp;

        // first priority: update
        if (update_valid) begin

            // take update sp
            next_sp = update_ras_index;
        end

        // otherwise, check for link and ret
        else if (link_valid & ret_valid) begin

            // link addr at current sp
            next_ras_array[sp] = link_pc38;
        end

        // otherwise, check for just link
        else if (link_valid) begin

            // link addr at next sp
            next_ras_array[sp_plus_1] = link_pc38;

            // incr sp
            next_sp = sp_plus_1;
        end

        // otherwise, check for just ret
        else if (ret_valid) begin

            // decr sp
            next_sp = sp_minus_1;
        end
    end

    // always read out current sp and current addr and sp
    always_comb begin
        ret_ras_index = sp;
        ret_pc38 = ras_array[sp];
    end

endmodule
