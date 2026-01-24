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
    input corep::ASID_t arch_asid,
    
    // read req stage
    input logic                                             read_req_valid,
    input corep::fetch_idx_t                                read_req_fetch_index,

    // read resp stage
    input corep::PC38_t                                     read_resp_pc38,

    output corep::BTB_info_t [corep::FETCH_LANES-1:0]       resp_resp_btb_info_by_lane,
    output logic [corep::FETCH_LANES-1:0]                   read_resp_hit_by_lane,
    output corep::BTB_way_idx_t [corep::FETCH_LANES-1:0]    read_resp_hit_way_by_lane,

    // update
    input logic                 update_valid,
    input corep::PC38_t         update_pc38,
    input corep::BTB_info_t     update_entry,
    input logic                 update_hit,
    input corep::BTB_way_idx_t  update_hit_way
);

    // ----------------------------------------------------------------
    // Functions:

    function corep::BTB_idx_t index_hash(corep::PC38_t pc38, corep::ASID_t asid);
        // low fetch index ^ low asid
        index_hash = corep::fetch_idx_bits(pc38);
        index_hash ^= asid;
    endfunction

    function corep::BTB_tag_t tag_hash(corep::PC38_t pc38, corep::ASID_t asid);
        // low pc38 above btb index ^ low asid
        tag_hash = pc38[37 : corep::LOG_BTB_SETS+corep::LOG_FETCH_LANES];
        tag_hash ^= asid;
    endfunction

    // ----------------------------------------------------------------
    // Signals:

    // bram IO
    logic               bram_read_next_valid;
    corep::BTB_idx_t    bram_read_next_index;
    corep::BTB_set_t    bram_read_set;

    logic [corep::FETCH_LANES-1:0][corep::BTB_ASSOC-1:0][$bits(corep::BTB_entry_t)/8-1:0]   bram_write_byten;
    corep::BTB_idx_t                                                                        bram_write_index;
    corep::BTB_set_t                                                                        bram_write_set;

    // plru array
        // index w/ {BTB index, fetch lane}
    corep::BTB_plru_t   plru_array  [corep::BTB_SETS-1:0][corep::FETCH_LANES-1:0];

    logic                   plru_array_update_valid;
    corep::BTB_idx_t        plru_array_update_index;
    corep::fetch_lane_t     plru_array_update_lane;
    corep::BTB_plru_t       plru_array_update_plru;

    // ----------------------------------------------------------------
    // Logic:

    // read next logic
    always_comb begin
        bram_read_next_valid = read_req_valid;
        bram_read_next_index = index_hash(read_req_fetch_index, arch_asid);
    end

    // hit logic
    always_comb begin

        // check hit by lane, by way
        for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin

            // default output way 0
            resp_resp_btb_info_by_lane[lane] = bram_read_set[lane][0].info;
            read_resp_hit_by_lane[lane] = 1'b0;
            read_resp_hit_way_by_lane[lane] = 0;

            // prioritize first way -> check in reverse order
            for (int way = corep::BTB_ASSOC-1; way >= 0; way--) begin

                // hit defined as non-zero action and tag match
                if (
                    |bram_read_set[lane][way].info.action
                    & (bram_read_set[lane][way].tag == tag_hash(read_resp_pc38, arch_asid))
                ) begin
                    resp_resp_btb_info_by_lane[lane] = bram_read_set[lane][way].info;
                    read_resp_hit_by_lane[lane] = 1'b1;
                    read_resp_hit_way_by_lane[lane] = way;
                end
            end
        end
    end

    // write logic
    always_comb begin

    end

    // bram
    bram_1rport_1wport #(
        .INNER_WIDTH($bits(bram_read_set)),
        .OUTER_WIDTH(corep::BTB_SETS)
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