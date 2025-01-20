/*
    Filename: btb.sv
    Author: zlagpacan
    Description: RTL for Branch Target Buffer
    Spec: LOROF/spec/design/btb.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage
    input logic         valid_REQ,
    input logic [29:0]  PC30_REQ,
    input logic [29:0]  

    // RESP stage
    output logic    pred_info_RESP,
    output logic    tag_RESP,
    output logic    target_RESP,

    // write req
    input logic                                             write_valid,
    input logic [LOG_BTB_ENTRIES-LOG_BTB_BANK_COUNT-2-1:0]  write_index,
    input logic [LOG_BTB_BANK_COUNT-1:0]                    write_bank,
    input logic [1:0]                                       write_offset,
    input logic [BTB_PRED_INFO_WIDTH-1:0]                   write_pred_info,
    input logic [BTB_TAG_WIDTH-1:0]                         write_tag,
    input logic [BTB_TARGET_WIDTH-1:0]                      write_target_width
);

    // ----------------------------------------------------------------
    // Signals:

    // REQ Stage:
    logic           bank_REQ;
    logic [1:0]     offset_REQ;

    // RESP Stage:
    logic           bank_RESP;
    logic [1:0]     offset_RESP;

endmodule