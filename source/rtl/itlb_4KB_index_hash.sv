/*
    Filename: itlb_4KB_index_hash.sv
    Author: zlagpacan
    Description: RTL for ITLB 4KB Page Array Index Hash Function
    Spec: LOROF/spec/design/itlb_4KB_index_hash.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module itlb_4KB_index_hash (
    input logic [ASID_WIDTH-1:0] ASID,
    input logic [VPN_WIDTH-1:0] VPN,
    output logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0] index
);
    // // lowest VPN ^ next lowest VPN ^ lowest ASID ^ next lowest ASID
    // always_comb begin
    //     index = VPN[ITLB_4KBPAGE_INDEX_WIDTH-1:0];
    //     index ^= VPN[ITLB_4KBPAGE_INDEX_WIDTH*2-1:ITLB_4KBPAGE_INDEX_WIDTH];
    //     index ^= ASID[ITLB_4KBPAGE_INDEX_WIDTH-1:0];
    //     index ^= ASID[ITLB_4KBPAGE_INDEX_WIDTH*2-1:ITLB_4KBPAGE_INDEX_WIDTH];
    // end

    // lowest VPN ^ next lowest VPN
        // can't mix up ASID's to different index's due to Global mapping
    always_comb begin
        index = VPN[ITLB_4KBPAGE_INDEX_WIDTH-1:0];
        index ^= VPN[ITLB_4KBPAGE_INDEX_WIDTH*2-1:ITLB_4KBPAGE_INDEX_WIDTH];
    end

endmodule