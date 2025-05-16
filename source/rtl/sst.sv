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

    // PLRU Arrays:
    // logic                               plru5, next_plru5;  // index bit 5
    // logic [1:0]                         plru4, next_plru4;  // index bit 4
    // logic [1:0][1:0]                    plru3, next_plru3;  // index bit 3
    // logic [1:0][1:0][1:0]               plru2, next_plru2;  // index bit 2
    // logic [1:0][1:0][1:0][1:0]          plru1, next_plru1;  // index bit 1
    // logic [1:0][1:0][1:0][1:0][1:0]     plru0, next_plru0;  // index bit 0
    
    logic [0:0]     plru5;  // index bit 5
    logic [1:0]     plru4;  // index bit 4
    logic [3:0]     plru3;  // index bit 3
    logic [7:0]     plru2;  // index bit 2
    logic [15:0]    plru1;  // index bit 1
    logic [31:0]    plru0;  // index bit 0

    // ----------------------------------------------------------------
    // Logic: 

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            plru5 <= '0;
            plru4 <= '0;
            plru3 <= '0;
            plru2 <= '0;
            plru1 <= '0;
            plru0 <= '0;
        end
        else begin

            // update following new SSID
            if (new_SSID_valid) begin
                plru5 <= ~plru5;
                plru4[new_SSID[5]] <= ~plru4[new_SSID[5]];
                plru3[new_SSID[5:4]] <= ~plru3[new_SSID[5:4]];
                plru2[new_SSID[5:3]] <= ~plru2[new_SSID[5:3]];
                plru1[new_SSID[5:2]] <= ~plru1[new_SSID[5:2]];
                plru0[new_SSID[5:1]] <= ~plru0[new_SSID[5:1]];
            end

            // update following touch
            else if (touch_SSID_valid) begin
                plru5 <= ~touch_SSID[5];
                plru4[touch_SSID[5]] <= ~touch_SSID[4];
                plru3[touch_SSID[5:4]] <= ~touch_SSID[3];                
                plru2[touch_SSID[5:3]] <= ~touch_SSID[2];
                plru1[touch_SSID[5:2]] <= ~touch_SSID[1];
                plru0[touch_SSID[5:1]] <= ~touch_SSID[0];
            end
        end
    end

    // advertise current plru
    // assign new_SSID[5] = plru5;
    // assign new_SSID[4] = plru4[new_SSID[5]];
    // assign new_SSID[3] = plru3[new_SSID[5]][new_SSID[4]];
    // assign new_SSID[2] = plru2[new_SSID[5]][new_SSID[4]][new_SSID[3]];
    // assign new_SSID[1] = plru1[new_SSID[5]][new_SSID[4]][new_SSID[3]][new_SSID[2]];
    // assign new_SSID[0] = plru0[new_SSID[5]][new_SSID[4]][new_SSID[3]][new_SSID[2]][new_SSID[1]];

    assign new_SSID[5] = plru5;
    assign new_SSID[4] = plru4[new_SSID[5]];
    assign new_SSID[3] = plru3[new_SSID[5:4]];
    assign new_SSID[2] = plru2[new_SSID[5:3]];
    assign new_SSID[1] = plru1[new_SSID[5:2]];
    assign new_SSID[0] = plru0[new_SSID[5:1]];

endmodule