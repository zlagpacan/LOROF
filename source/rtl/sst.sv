/*
    Filename: sst.sv
    Author: zlagpacan
    Description: RTL for Store Set Tracker
    Spec: LOROF/spec/design/sst.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module sst #(
    parameter STORE_SET_COUNT = 64,
    parameter SSID_WIDTH = $clog2(STORE_SET_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // new SSID check
    input logic                     new_SSID_valid,
    output logic [SSID_WIDTH-1:0]   new_SSID,

    // touch check
    input logic                     touch_SSID_valid,
    input logic [SSID_WIDTH-1:0]    touch_SSID
);

    // ----------------------------------------------------------------
    // Signals:

    // PLRU:
    logic [STORE_SET_COUNT-2:0] plru, next_plru;

    // ----------------------------------------------------------------
    // Logic: 

    plru_updater #(
        .NUM_ENTRIES(STORE_SET_COUNT)
    ) PLRU_UPDATER (
        .plru_in(plru),
        .new_valid(new_SSID_valid),
        .new_index(new_SSID),
        .touch_valid(touch_SSID_valid),
        .touch_index(touch_SSID),
        .plru_out(next_plru)
    );

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            plru <= '0;
        end
        else begin
            plru <= next_plru;
        end
    end

endmodule