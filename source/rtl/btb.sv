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
    
    // read req stage
    input logic                     read_req_valid,
    input corep::fetch_idx_t        read_req_fetch_idx,
    input corep::asid_t             read_req_asid,

    // read resp stage
    input corep::pc38_t             read_resp_pc38,

    output logic                    read_resp_hit,
    output corep::btb_way_t         read_resp_hit_way,
    output corep::fetch_lane_t      read_resp_hit_lane,
    output logic                    read_resp_double_hit,
    output corep::btb_info_t        read_resp_btb_info,

    // update
    input logic                 update_valid,
    input corep::pc38_t         update_pc38,
    input corep::asid_t         update_asid,
    input corep::btb_info_t     update_btb_info,
    input logic                 update_hit,
    input corep::btb_way_t      update_hit_way
);

    // ----------------------------------------------------------------
    // Functions:

    function corep::btb_idx_t index_hash(corep::fetch_idx_t fetch_idx, corep::asid_t asid);
        // low fetch index ^ low asid
        index_hash = fetch_idx;
        index_hash ^= asid;
    endfunction

    function corep::btb_tag_t tag_hash(corep::pc38_t pc38, corep::asid_t asid);
        // low pc38 above btb index ^ low asid
        tag_hash = pc38[37 : corep::LOG_BTB_SETS+corep::LOG_FETCH_LANES];
        tag_hash ^= asid;
    endfunction

    // ----------------------------------------------------------------
    // Signals:

    // btb array bram IO
        // index w/ BTB index
    logic               btb_array_bram_read_next_valid;
    corep::btb_idx_t    btb_array_bram_read_next_index;
    corep::btb_set_t    btb_array_bram_read_set;

    logic [1:0][$bits(corep::btb_entry_t)/8-1:0]    btb_array_bram_write_byten; // hardwired corep::BTB_ASSOC = 2
    corep::btb_idx_t                                btb_array_bram_write_index;
    corep::btb_set_t                                btb_array_bram_write_set;

    // plru array distram IO
        // index w/ {BTB index, fetch lane}
    logic [corep::LOG_BTB_SETS-1:0]     plru_array_distram_read_index;
    corep::btb_plru_t                   plru_array_distram_read_data;

    logic                               plru_array_distram_write_valid;
    logic [corep::LOG_BTB_SETS-1:0]     plru_array_distram_write_index;
    corep::btb_plru_t                   plru_array_distram_write_data;

    // read resp
    corep::asid_t       read_resp_asid;
    logic               read_resp_hit_way0;
    logic               read_resp_hit_way1;

    // update indexing
    corep::btb_idx_t    update_index;
    corep::btb_way_t    update_selected_way;

    // plru updater
    corep::btb_plru_t   plru_updater_plru_in;
    logic               plru_updater_new_valid;
    corep::btb_way_t    plru_updater_new_index;
    logic               plru_updater_touch_valid;
    corep::btb_way_t    plru_updater_touch_index;
    corep::btb_plru_t   plru_updater_plru_out;

    // ----------------------------------------------------------------
    // Logic:

    // read next logic
    always_comb begin
        btb_array_bram_read_next_valid = read_req_valid;
        btb_array_bram_read_next_index = index_hash(read_req_fetch_idx, read_req_asid);
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            read_resp_asid <= 0;
        end
        else if (read_req_valid) begin
            read_resp_asid <= read_req_asid;
        end
    end

    // hit logic
    always_comb begin

        // check hit by way
            // hardwired corep::BTB_ASSOC = 2
            // non-zero action + tag match + lane at or beyond fetch lane
        read_resp_hit_way0 =
            |btb_array_bram_read_set[0].info.action
            & (btb_array_bram_read_set[0].tag == tag_hash(read_resp_pc38, read_resp_asid))
            & (btb_array_bram_read_set[0].lane >= read_resp_pc38.lane)
        ;
        read_resp_hit_way1 =
            |btb_array_bram_read_set[1].info.action
            & (btb_array_bram_read_set[1].tag == tag_hash(read_resp_pc38, read_resp_asid))
            & (btb_array_bram_read_set[1].lane >= read_resp_pc38.lane)
        ;
        read_resp_hit = read_resp_hit_way0 | read_resp_hit_way1;
        read_resp_double_hit = read_resp_hit_way0 & read_resp_hit_way1;

        // both ways hit
        if (read_resp_hit_way0 & read_resp_hit_way1) begin

            // give lower lane hit way, prioritizing way 1 on tie
            if (btb_array_bram_read_set[1].lane <= btb_array_bram_read_set[0].lane) begin
                read_resp_hit_way = 1;
                read_resp_btb_info = btb_array_bram_read_set[1].info;
                read_resp_hit_lane = btb_array_bram_read_set[1].lane;
            end
            else begin
                read_resp_hit_way = 0;
                read_resp_btb_info = btb_array_bram_read_set[0].info;
                read_resp_hit_lane = btb_array_bram_read_set[0].lane;
            end
        end

        // way 1 hit
        else if (read_resp_hit_way1) begin
            read_resp_hit_way = 1;
            read_resp_btb_info = btb_array_bram_read_set[1].info;
            read_resp_hit_lane = btb_array_bram_read_set[1].lane;
        end

        // otherwise, default way 0 data
        else begin
            read_resp_hit_way = 0;
            read_resp_btb_info = btb_array_bram_read_set[0].info;
            read_resp_hit_lane = btb_array_bram_read_set[0].lane;
        end
    end

    // write logic
    always_comb begin
        update_index = index_hash(update_pc38.idx, update_asid);
        if (update_hit) begin
            update_selected_way = update_hit_way;
        end
        else begin
            update_selected_way = plru_updater_new_index;
        end

        plru_updater_plru_in = plru_array_distram_read_data;
        plru_updater_new_valid = update_valid & ~update_hit;
        plru_updater_touch_valid = update_valid & update_hit;
        plru_updater_touch_index = update_hit_way;

        btb_array_bram_write_byten = '0;
        if (update_valid) begin
            btb_array_bram_write_byten[update_selected_way] = '1;
        end
        btb_array_bram_write_index = update_index;
        for (int way = 0; way < corep::BTB_ASSOC; way++) begin
            btb_array_bram_write_set[way].info = update_btb_info;
            btb_array_bram_write_set[way].tag = tag_hash(update_pc38, update_asid);
            btb_array_bram_write_set[way].lane = update_pc38.lane;
        end
    end

    // plru updater
    plru_updater #(
        .NUM_ENTRIES(corep::BTB_ASSOC) // hardwired corep::BTB_ASSOC = 2
    ) PLRU_UPDATER (
        .plru_in(plru_updater_plru_in),
        .new_valid(plru_updater_new_valid),
        .new_index(plru_updater_new_index),
        .touch_valid(plru_updater_touch_valid),
        .touch_index(plru_updater_touch_index),
        .plru_out(plru_updater_plru_out)
    );

    // plru array distram
    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::btb_plru_t)),
        .OUTER_WIDTH(corep::BTB_SETS)
    ) PLRU_ARRAY_DISTRAM (
        .CLK(CLK),
        .rindex(plru_array_distram_read_index),
        .rdata(plru_array_distram_read_data),
        .wen(plru_array_distram_write_valid),
        .windex(plru_array_distram_write_index),
        .wdata(plru_array_distram_write_data)
    );
    always_comb begin
        plru_array_distram_read_index = update_index;

        plru_array_distram_write_valid = update_valid;
        plru_array_distram_write_index = update_index;
        plru_array_distram_write_data = plru_updater_plru_out;
    end

    // btb array bram
    bram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::btb_set_t)),
        .OUTER_WIDTH(corep::BTB_SETS)
    ) BTB_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(btb_array_bram_read_next_valid),
        .rindex(btb_array_bram_read_next_index),
        .rdata(btb_array_bram_read_set),
        .wen_byte(btb_array_bram_write_byten),
        .windex(btb_array_bram_write_index),
        .wdata(btb_array_bram_write_set)
    );

endmodule