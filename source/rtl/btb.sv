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

    // read resp0 stage
    input logic                     read_resp0_valid,
    input corep::pc38_t             read_resp0_pc38,

    // read resp1 stage
    output logic                    read_resp1_hit,
    output logic                    read_resp1_double_hit,
    output corep::btb_way_t         read_resp1_hit_way,

    output corep::fetch_lane_t      read_resp1_hit_lane_way0,
    output corep::fetch_lane_t      read_resp1_hit_lane_way1,
    output corep::btb_info_t        read_resp1_btb_info_way0,
    output corep::btb_info_t        read_resp1_btb_info_way1,

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
    logic                       btb_info_lane_array_bram_read0_next_valid;
    corep::btb_idx_t            btb_info_lane_array_bram_read0_next_index;
    logic                       btb_info_lane_array_bram_read1_next_valid;
    corep::btb_info_lane_set_t  btb_info_lane_array_bram_read1_set;

    logic [1:0][$bits(corep::btb_info_lane_set_t)/8-1:0]    btb_info_lane_array_bram_write_byten; // hardwired corep::BTB_ASSOC = 2
    corep::btb_idx_t                                        btb_info_lane_array_bram_write_index;
    corep::btb_info_lane_set_t                              btb_info_lane_array_bram_write_set;
    
    logic                   btb_tag_array_bram_read_next_valid;
    corep::btb_idx_t        btb_tag_array_bram_read_next_index;
    corep::btb_tag_set_t    btb_tag_array_bram_read_set;

    logic [1:0][$bits(corep::btb_tag_set_t)/8-1:0]  btb_tag_array_bram_write_byten; // hardwired corep::BTB_ASSOC = 2
    corep::btb_idx_t                                btb_tag_array_bram_write_index;
    corep::btb_tag_set_t                            btb_tag_array_bram_write_set;

    // plru array distram IO
        // index w/ {BTB index, fetch lane}
    logic [corep::LOG_BTB_SETS-1:0]     plru_array_distram_read_index;
    corep::btb_plru_t                   plru_array_distram_read_data;

    logic                               plru_array_distram_write_valid;
    logic [corep::LOG_BTB_SETS-1:0]     plru_array_distram_write_index;
    corep::btb_plru_t                   plru_array_distram_write_data;

    // read resp0
    corep::asid_t   read_resp0_asid;
    logic           read_resp0_tag_hit_way0;
    logic           read_resp0_tag_hit_way1;

    // read resp1
    logic           read_resp1_tag_hit_way0;
    logic           read_resp1_tag_hit_way1;

    logic           read_resp1_hit_way0;
    logic           read_resp1_hit_way1;

    corep::fetch_lane_t read_resp1_lane;

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
        btb_info_lane_array_bram_read0_next_valid = read_req_valid;
        btb_info_lane_array_bram_read0_next_index = index_hash(read_req_fetch_idx, read_req_asid);
        btb_info_lane_array_bram_read1_next_valid = read_resp0_valid;

        btb_tag_array_bram_read_next_valid = read_req_valid;
        btb_tag_array_bram_read_next_index = index_hash(read_req_fetch_idx, read_req_asid);
    end

    // resp0 logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            read_resp0_asid <= 0;
        end
        else begin
            if (read_req_valid) begin
                read_resp0_asid <= read_req_asid;
            end
        end
    end
    always_comb begin
        read_resp0_tag_hit_way0 = (btb_tag_array_bram_read_set[0] == tag_hash(read_resp0_pc38, read_resp0_asid));
        read_resp0_tag_hit_way1 = (btb_tag_array_bram_read_set[1] == tag_hash(read_resp0_pc38, read_resp0_asid));
    end

    // resp1 logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            read_resp1_tag_hit_way0 <= 0;
            read_resp1_tag_hit_way1 <= 0;
            read_resp1_lane <= 0;
        end
        else begin
            if (read_resp0_valid) begin
                read_resp1_tag_hit_way0 <= read_resp0_tag_hit_way0;
                read_resp1_tag_hit_way1 <= read_resp0_tag_hit_way1;
                read_resp1_lane <= read_resp0_pc38.lane;
            end
        end
    end
    always_comb begin

        // check hit by way
            // hardwired corep::BTB_ASSOC = 2
            // non-zero action + tag match + lane at or beyond fetch lane
        read_resp1_hit_way0 =
            |btb_info_lane_array_bram_read1_set[0].info.action
            & read_resp1_tag_hit_way0
            & (btb_info_lane_array_bram_read1_set[0].lane >= read_resp1_lane)
        ;
        read_resp1_hit_way1 =
            |btb_info_lane_array_bram_read1_set[1].info.action
            & read_resp1_tag_hit_way1
            & (btb_info_lane_array_bram_read1_set[1].lane >= read_resp1_lane)
        ;
        read_resp1_hit = read_resp1_hit_way0 | read_resp1_hit_way1;
        read_resp1_double_hit = read_resp1_hit_way0 & read_resp1_hit_way1;

        read_resp1_btb_info_way0 = btb_info_lane_array_bram_read1_set[0].info;
        read_resp1_hit_lane_way0 = btb_info_lane_array_bram_read1_set[0].lane;

        read_resp1_btb_info_way1 = btb_info_lane_array_bram_read1_set[1].info;
        read_resp1_hit_lane_way1 = btb_info_lane_array_bram_read1_set[1].lane;

        // both ways hit
        if (read_resp1_hit_way0 & read_resp1_hit_way1) begin

            // give lower lane hit way, prioritizing way 1 on tie
            if (btb_info_lane_array_bram_read1_set[1].lane <= btb_info_lane_array_bram_read1_set[0].lane) begin
                read_resp1_hit_way = 1;
            end
            else begin
                read_resp1_hit_way = 0;
            end
        end

        // way 1 hit
        else if (read_resp1_hit_way1) begin
            read_resp1_hit_way = 1;
        end

        // otherwise, default way 0 data
        else begin
            read_resp1_hit_way = 0;
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

        btb_info_lane_array_bram_write_byten = '0;
        btb_tag_array_bram_write_byten = '0;
        if (update_valid) begin
            btb_info_lane_array_bram_write_byten[update_selected_way] = '1;
            btb_tag_array_bram_write_byten[update_selected_way] = '1;
        end
        btb_info_lane_array_bram_write_index = update_index;
        btb_tag_array_bram_write_index = update_index;
        for (int way = 0; way < corep::BTB_ASSOC; way++) begin
            btb_info_lane_array_bram_write_set[way].info = update_btb_info;
            btb_info_lane_array_bram_write_set[way].lane = update_pc38.lane;
            btb_tag_array_bram_write_set[way] = tag_hash(update_pc38, update_asid);
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

    // btb info lane array 1xdelay bram
    bram_1xdelay_1rport_1wport #(
        .INNER_WIDTH($bits(corep::btb_info_lane_set_t)),
        .OUTER_WIDTH(corep::BTB_SETS)
    ) BTB_INFO_LANE_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren0(btb_info_lane_array_bram_read0_next_valid),
        .ren1(btb_info_lane_array_bram_read1_next_valid),
        .rindex(btb_info_lane_array_bram_read0_next_index),
        .rdata(btb_info_lane_array_bram_read1_set),
        .wen_byte(btb_info_lane_array_bram_write_byten),
        .windex(btb_info_lane_array_bram_write_index),
        .wdata(btb_info_lane_array_bram_write_set)
    );

    // btb tag array bram
    bram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::btb_tag_set_t)),
        .OUTER_WIDTH(corep::BTB_SETS)
    ) BTB_TAG_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(btb_tag_array_bram_read_next_valid),
        .rindex(btb_tag_array_bram_read_next_index),
        .rdata(btb_tag_array_bram_read_set),
        .wen_byte(btb_tag_array_bram_write_byten),
        .windex(btb_tag_array_bram_write_index),
        .wdata(btb_tag_array_bram_write_set)
    );

endmodule