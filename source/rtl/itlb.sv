/*
    Filename: itlb.sv
    Author: zlagpacan
    Description: RTL for L1 Instruction TLB. Blocking, 2-way associative 4KB page array, direct-mapped 2MB page array, configurable set counts
    Spec: LOROF/spec/design/itlb.md
*/

`include "system_types_pkg.vh"
import system_types_pkg::*;

module itlb #(
    parameter ITLB_4KBPAGE_NUM_SETS = 16,
    parameter ITLB_4KBPAGE_INDEX_WIDTH = $clog2(ITLB_4KBPAGE_NUM_SETS),
    parameter ITLB_4KBPAGE_TAG_WIDTH = 16,

    parameter ITLB_2MBPAGE_NUM_SETS = 4,
    parameter ITLB_2MBPAGE_INDEX_WIDTH = $clog2(ITLB_2MBPAGE_NUM_SETS),
    parameter ITLB_2MBPAGE_TAG_WIDTH = 9
) (
    // seq
    input logic CLK,
    input logic nRST,

    // core req
    input logic                     core_req_valid,
    input logic [1:0]               core_req_exec_mode,
    input logic                     core_req_virtual_mode,
    input logic [ASID_WIDTH-1:0]    core_req_ASID,
    input logic [VPN_WIDTH-1:0]     core_req_VPN,

    // core resp
    output logic                    core_resp_valid,
    output logic [PPN_WIDTH-1:0]    core_resp_PPN,
    output logic                    core_resp_page_fault,
    output logic                    core_resp_access_fault,

    // req to L2 TLB


    // resp from L2 TLB


    // l2 evict to L2 TLB
    
);

endmodule