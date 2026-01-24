/*
    Filename: btb.sv
    Author: zlagpacan
    Description: RTL for Branch Target (and Branch Prediction Info) Buffer
    Spec: LOROF/spec/design/btb.md
*/

`include "corep.vh"

module btb (

    // seq
    input logic CLK,
    input logic nRST,

    // arch state
    input corep::ASID_t arch_ASID,
    
    // read req in
    input logic                                                 read_req_valid,
    input corep::PC38_t                                         read_req_pc38,

    // read resp out
    output corep::BTB_entry_t [corep::FETCH_LANES-1:0]      resp_resp_entry_by_lane,
    output logic [corep::FETCH_LANES-1:0]                   read_resp_hit_by_lane,
    output corep::BTB_way_idx_t [corep::FETCH_LANES-1:0]    read_resp_hit_way_by_lane,

    // update in
    input logic                 update_valid,
    input corep::PC38_t         update_pc38,
    input corep::BTB_entry_t    update_entry,
    input logic                 update_hit,
    input corep::BTB_way_idx_t  update_hit_way
);

    // ----------------------------------------------------------------
    // Signals:

    // bram IO
    logic               bram_read_next_valid;
    corep::BTB_idx_t    bram_read_next_index;
    corep::BTB_set_t    bram_read_set;

    logic [$bits(corep::BTB_set_t)/8-1:0]   bram_write_byten;
    corep::BTB_idx_t                        bram_write_index;
    corep::BTB_set_t                        bram_write_set;

    // plru array
        // index w/ {BTB index, fetch lane}
    corep::BTB_plru_t [BTB_SETS*FETCH_LANES-1:0] plru_array;

    logic                                       plru_array_update_valid;
    logic [$clog2(BTB_SETS*FETCH_LANES)-1:0]    plru_array_update_index;
    corep::BTB_plru_t                           plru_array_update_plru;

    // ----------------------------------------------------------------
    // Logic:

    // bram
    bram_1rport_1wport #(
        .INNER_WIDTH($bits(bram_read_set)),
        .OUTER_WIDTH(BTB_SETS)
    ) BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(bram_read_next_valid),
        .rindex(bram_read_next_index),
        .rdata(bram_read_set),
        .wen_byte(bram_write_byten),
        .windex(bram_write_index),
        .wdata(bram_write_set)
    );

endmodule