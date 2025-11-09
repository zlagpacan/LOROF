/*
    Filename: ras.sv
    Author: zlagpacan
    Description: RTL for Return Address Stack
    Spec: LOROF/spec/design/ras.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ras (

    // seq
    input logic CLK,
    input logic nRST,

    // RESP stage
    input logic                         link_RESP,
    input logic [31:0]                  link_full_PC_RESP,
    input logic                         ret_RESP,

    output logic [31:0]                 ret_full_PC_RESP,
    output logic [RAS_INDEX_WIDTH-1:0]  ras_index_RESP,

    // Update 0
    input logic                         update0_valid,
    input logic [RAS_INDEX_WIDTH-1:0]   update0_ras_index
);

    // ----------------------------------------------------------------
    // Signals:

    // FF Array:
    logic [RAS_ENTRIES-1:0][RAS_TARGET_WIDTH-1:0] ras_array, next_ras_array;

    // RESP Stage:
    logic [RAS_INDEX_WIDTH-1:0] sp, next_sp;

    // ----------------------------------------------------------------
    // Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
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

        // hold array by default
        next_ras_array = ras_array;

        // default hold sp
        next_sp = sp;

        // first priority: update
        if (update0_valid) begin

            // take Update 0 sp
            next_sp = update0_ras_index;
        end

        // otherwise, check for link and ret
        else if (link_RESP & ret_RESP) begin

            // link addr at current sp
            next_ras_array[sp] = link_full_PC_RESP[31:1];
        end

        // otherwise, check for just link
        else if (link_RESP) begin

            // link addr at next sp
            next_ras_array[sp + 1] = link_full_PC_RESP[31:1];

            // incr sp
            next_sp = sp + 1;
        end

        // otherwise, check for just ret
        else if (ret_RESP) begin

            // decr sp
            next_sp = sp - 1;
        end
    end

    // always read out current sp and current addr and sp
    assign ras_index_RESP = sp;
    assign ret_full_PC_RESP = {ras_array[sp], 1'b0};

endmodule
