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
    output corep::BTB_entry_t [corep::FETCH_WIDTH_2B-1:0]       resp_resp_btb_entry_by_lane,
    output logic [corep::FETCH_WIDTH_2B-1:0]                    read_resp_hit_by_lane,
    output corep::BTB_plru_idx_t [corep::FETCH_WIDTH_2B-1:0]    read_resp_plru_index_by_lane,

    // update in
    input logic                     update_valid,
    input corep::PC38_t             update_pc38,
    input corep::BTB_entry_t        update_btb_entry,
    input corep::BTB_plru_idx_t     update_plru_index
);

    // ----------------------------------------------------------------
    // Signals:

    

    // ----------------------------------------------------------------
    // Logic: 

endmodule