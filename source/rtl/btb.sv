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
    input corep::BTB_info_t     update_btb_info,
    input logic                 update_hit,
    input corep::BTB_way_idx_t  update_hit_way
);

    // ----------------------------------------------------------------
    // Functions:

    function corep::BTB_idx_t index_hash(corep::PC38_t pc38, corep::ASID_t asid);
        // low fetch index ^ low asid
        index_hash = pc38[37 : corep::LOG_FETCH_LANES];
        index_hash ^= asid;
    endfunction

    function corep::BTB_tag_t tag_hash(corep::PC38_t pc38, corep::ASID_t asid);
        // low pc38 above btb index ^ low asid
        tag_hash = pc38[37 : corep::LOG_BTB_SETS+corep::LOG_FETCH_LANES];
        tag_hash ^= asid;
    endfunction

    // ----------------------------------------------------------------
    // Signals:

    // btb array bram IO
        // index w/ BTB index
    logic               btb_array_bram_read_next_valid;
    corep::BTB_idx_t    btb_array_bram_read_next_index;
    corep::BTB_set_t    btb_array_bram_read_set;

    logic [corep::FETCH_LANES-1:0][corep::BTB_ASSOC-1:0][$bits(corep::BTB_entry_t)/8-1:0]   btb_array_bram_write_byten;
    corep::BTB_idx_t                                                                        btb_array_bram_write_index;
    corep::BTB_set_t                                                                        btb_array_bram_write_set;

    // plru array distram IO
        // index w/ {BTB index, fetch lane}
    logic [corep::LOG_BTB_SETS+corep::LOG_FETCH_LANES-1:0]  plru_array_distram_read_index;
    corep::BTB_plru_t                                       plru_array_distram_read_data;

    logic                                                   plru_array_distram_write_valid;
    logic [corep::LOG_BTB_SETS+corep::LOG_FETCH_LANES-1:0]  plru_array_distram_write_index;
    corep::BTB_plru_t                                       plru_array_distram_write_data;

    // update indexing
    corep::BTB_idx_t        update_index;
    corep::fetch_lane_t     update_lane;
    corep::BTB_way_idx_t    update_selected_way;

    // plru updater
    corep::BTB_plru_t       plru_updater_plru_in;
    logic                   plru_updater_new_valid;
    corep::BTB_way_idx_t    plru_updater_new_way;
    logic                   plru_updater_touch_valid;
    corep::BTB_way_idx_t    plru_updater_touch_way;
    corep::BTB_plru_t       plru_updater_plru_out;

    // ----------------------------------------------------------------
    // Logic:

    // read next logic
    always_comb begin
        btb_array_bram_read_next_valid = read_req_valid;
        btb_array_bram_read_next_index = index_hash({read_req_fetch_index, {corep::LOG_FETCH_LANES{1'b0}}}, arch_asid);
    end

    // hit logic
    always_comb begin

        // check hit by lane, by way
        for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin

            // default output way 0
            resp_resp_btb_info_by_lane[lane] = btb_array_bram_read_set[lane][0].info;
            read_resp_hit_by_lane[lane] = 1'b0;
            read_resp_hit_way_by_lane[lane] = 0;

            // prioritize first way -> check in reverse order
            for (int way = corep::BTB_ASSOC-1; way >= 0; way--) begin

                // hit defined as non-zero action and tag match
                if (
                    |btb_array_bram_read_set[lane][way].info.action
                    & (btb_array_bram_read_set[lane][way].tag == tag_hash(read_resp_pc38, arch_asid))
                ) begin
                    resp_resp_btb_info_by_lane[lane] = btb_array_bram_read_set[lane][way].info;
                    read_resp_hit_by_lane[lane] = 1'b1;
                    read_resp_hit_way_by_lane[lane] = way;
                end
            end
        end
    end

    // write logic
    always_comb begin
        update_index = index_hash(update_pc38, arch_asid);
        update_lane = corep::fetch_lane_bits(update_pc38);
        if (update_hit) begin
            update_selected_way = update_hit_way;
        end
        else begin
            update_selected_way = plru_updater_new_way;
        end

        plru_updater_plru_in = plru_array_distram_read_data;
        plru_updater_new_valid = update_valid & ~update_hit;
        plru_updater_touch_valid = update_valid & update_hit;
        plru_updater_touch_way = update_hit_way;

        btb_array_bram_write_byten = '0;
        if (update_valid) begin
            btb_array_bram_write_byten[update_lane][update_selected_way] = '1;
        end
        btb_array_bram_write_index = update_index;
        for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin
            for (int way = 0; way < corep::BTB_ASSOC; way++) begin
                btb_array_bram_write_set[lane][way].info = update_btb_info;
                btb_array_bram_write_set[lane][way].tag = tag_hash(update_pc38, arch_asid);
            end
        end
    end

    // plru updater
    plru_updater #(
        .NUM_ENTRIES(corep::BTB_ASSOC)
    ) PLRU_UPDATER (
        .plru_in(plru_updater_plru_in),
        .new_valid(plru_updater_new_valid),
        .new_way(plru_updater_new_way),
        .touch_valid(plru_updater_touch_valid),
        .touch_way(plru_updater_touch_way),
        .plru_out(plru_updater_plru_out)
    );

    // plru array distram
    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::BTB_plru_t)),
        .OUTER_WIDTH(corep::BTB_SETS * corep::FETCH_LANES)
    ) PLRU_ARRAY_DISTRAM (
        .CLK(CLK),
        .rindex(plru_array_distram_read_index),
        .rdata(plru_array_distram_read_data),
        .wen(plru_array_distram_write_valid),
        .windex(plru_array_distram_write_index),
        .wdata(plru_array_distram_write_data)
    );
    always_comb begin
        plru_array_distram_read_index = {update_index, update_lane};

        plru_array_distram_write_valid = update_valid;
        plru_array_distram_write_index = {update_index, update_lane};
        plru_array_distram_write_data = plru_updater_plru_out;
    end

    // btb array bram
    bram_1rport_1wport #(
        .INNER_WIDTH($bits(btb_array_bram_read_set)),
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