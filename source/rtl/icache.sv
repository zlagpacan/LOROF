/*
    Filename: icache.sv
    Author: zlagpacan
    Description: RTL for L1 Instruction Cache. Blocking, configurable associativity, set count, and block size
    Spec: LOROF/spec/design/icache.md
*/

`include "system_types.vh"

module icache #(
    parameter int unsigned ICACHE_SIZE = 2**13, // 8KB, 4KB page per way
    parameter int unsigned ICACHE_BLOCK_SIZE = system_types::L1_BLOCK_SIZE, // 32B
    parameter int unsigned ICACHE_ASSOC = 2, // 2x
    parameter int unsigned LOG_ICACHE_ASSOC = $clog2(ICACHE_ASSOC), // 1b
    parameter int unsigned ICACHE_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE), // 5b
    parameter int unsigned ICACHE_NUM_SETS = ICACHE_SIZE / ICACHE_ASSOC / ICACHE_BLOCK_SIZE, // 128x
    parameter int unsigned ICACHE_INDEX_WIDTH = $clog2(ICACHE_NUM_SETS), // 7b
    parameter int unsigned ICACHE_TAG_WIDTH = system_types::PA_WIDTH - ICACHE_INDEX_WIDTH - ICACHE_BLOCK_OFFSET_WIDTH, // 34b - 7b - 5b = 22b

    parameter int unsigned ICACHE_FETCH_WIDTH = 16, // 16B
    parameter int unsigned ICACHE_FETCH_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE / ICACHE_FETCH_WIDTH) // 1b
) (
    // seq
    input logic CLK,
    input logic nRST,

    // req from core
    input logic                                         core_req_valid,
    input logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]   core_req_block_offset,
    input logic [ICACHE_INDEX_WIDTH-1:0]                core_req_index,

    // resp to core
    output logic [ICACHE_ASSOC-1:0]                                  core_resp_valid_by_way,
    output logic [ICACHE_ASSOC-1:0][ICACHE_TAG_WIDTH-1:0]            core_resp_tag_by_way,
    output logic [ICACHE_ASSOC-1:0][ICACHE_FETCH_WIDTH-1:0][7:0]     core_resp_instr_16B_by_way,

    // resp feedback from core
    input logic                         core_resp_hit_valid,
    input logic [LOG_ICACHE_ASSOC-1:0]  core_resp_hit_way,
    input logic                         core_resp_miss_valid,
    input logic [ICACHE_TAG_WIDTH-1:0]  core_resp_miss_tag,

    // req to L2
    output logic                                            l2_req_valid,
    output logic [system_types::L1_BLOCK_ADDR_WIDTH-1:0]    l2_req_PA29,
    input logic                                             l2_req_ready,

    // resp from L2
    input logic                                             l2_resp_valid,
    input logic [system_types::L1_BLOCK_ADDR_WIDTH-1:0]     l2_resp_PA29,
    input logic [system_types::L1_BLOCK_SIZE_BITS-1:0]      l2_resp_data256,

    // L2 snoop inv
    input logic                                             l2_snoop_inv_valid,
    input logic [system_types::L1_BLOCK_ADDR_WIDTH-1:0]     l2_snoop_inv_PA29
);

    // direct lower bit index hashing
        // phyiscally tagged so no need to XOR w/ ASID

    // interfaces
        // req from core
            // unstoppable

        // resp to core
            // can be delayed by delaying valid
            
        // resp feedback from core
            // comb response to resp to core

        // req to L2
            // ready-valid

        // resp from L2
            // unstoppable

        // L2 snoop inv
            // unstoppable
            // prioritize over L2 miss coming in, which can be saved in miss reg

    // ----------------------------------------------------------------
    // Signals:

    // tag array:
        // BRAM

    typedef struct packed {
        logic                                           valid;
        logic [((8-((ICACHE_TAG_WIDTH+1)%8))%8)-1:0]    byte_align_bits;
        logic [ICACHE_TAG_WIDTH-1:0]                    tag;
    } tag_entry_t;

    logic                                                   tag_array_read_next_valid;
    logic [ICACHE_INDEX_WIDTH-1:0]                          tag_array_read_next_index;
    tag_entry_t [ICACHE_ASSOC-1:0]                          tag_array_read_set;

    logic [ICACHE_ASSOC-1:0][($bits(tag_entry_t)/8)-1:0]    tag_array_write_valid_mask;
    logic [ICACHE_INDEX_WIDTH-1:0]                          tag_array_write_index;
    tag_entry_t [ICACHE_ASSOC-1:0]                          tag_array_write_set;

    // PLRU array:
        // reg
    
    logic [ICACHE_NUM_SETS-1:0][ICACHE_ASSOC-2:0] plru_array;

    // data array:
        // BRAM

    logic                                                           data_array_read_next_valid;
    logic [ICACHE_INDEX_WIDTH+ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]  data_array_read_next_index;
    logic [ICACHE_ASSOC-1:0][ICACHE_FETCH_WIDTH*8-1:0]              data_array_read_set;

    logic [ICACHE_ASSOC-1:0][ICACHE_FETCH_WIDTH-1:0]                data_array_write_valid_mask;
    logic [ICACHE_INDEX_WIDTH+ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]  data_array_write_index;
    logic [ICACHE_ASSOC-1:0][ICACHE_FETCH_WIDTH*8-1:0]              data_array_write_set;

    // read port usage:
        // core req
            // tag + data
        // l2 snoop inv
            // tag

    // write port usage:
        // miss resp
            // tag + data
        // l2 snoop inv
            // tag

    logic                                           snoop_inv_next_reading;
    logic                                           snoop_inv_writing;
    logic [system_types::L1_BLOCK_ADDR_WIDTH-1:0]   snoop_inv_saved_PA29;

    logic snoop_inv_writing_delay_cycle;

    logic                           l2_snoop_hit;
    logic [LOG_ICACHE_ASSOC-1:0]    l2_snoop_hit_way;

    logic                                           core_resp_valid;
    logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]     core_resp_block_offset;
    logic [ICACHE_INDEX_WIDTH-1:0]                  core_resp_index;

    logic                                                                       miss_reg_valid, next_miss_reg_valid;
    logic                                                                       miss_reg_requested, next_miss_reg_requested;
    logic [ICACHE_INDEX_WIDTH-1:0]                                              miss_reg_missing_index, next_miss_reg_missing_index;
    logic [ICACHE_TAG_WIDTH-1:0]                                                miss_reg_missing_tag, next_miss_reg_missing_tag;
    logic [LOG_ICACHE_ASSOC-1:0]                                                miss_reg_old_lru_way, next_miss_reg_old_lru_way;
    logic                                                                       miss_reg_data_valid, next_miss_reg_data_valid;
    logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]                                 miss_reg_data_blkoff, next_miss_reg_data_blkoff;
    logic [2**ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0][ICACHE_FETCH_WIDTH*8-1:0]    miss_reg_data_buffer, next_miss_reg_data_buffer;
    logic                                                                       miss_reg_delay_cycle, next_miss_reg_delay_cycle;

    logic miss_index_matching_core;
    logic miss_index_and_tag_matching_core;

    // PLRU updater
    logic [ICACHE_ASSOC-2:0]        plru_updater_plru_in;
    logic                           plru_updater_new_valid;
    logic [LOG_ICACHE_ASSOC-1:0]    plru_updater_new_index;
    logic                           plru_updater_touch_valid;
    logic [LOG_ICACHE_ASSOC-1:0]    plru_updater_touch_index;
    logic [ICACHE_ASSOC-2:0]        plru_updater_plru_out;

    // empty way PE
    logic [ICACHE_ASSOC-1:0]        empty_way_pe_req_vec;
    logic                           empty_way_pe_req_present;
    logic [LOG_ICACHE_ASSOC-1:0]    empty_way_pe_ack_index;

    // ----------------------------------------------------------------
    // Logic:

    // read port logic
    always_comb begin
        tag_array_read_next_valid = core_req_valid | snoop_inv_next_reading;
        if (snoop_inv_next_reading) begin
            tag_array_read_next_index = l2_snoop_inv_PA29[ICACHE_INDEX_WIDTH-1:0];
        end
        else begin
            tag_array_read_next_index = core_req_index;
        end

        data_array_read_next_valid = core_req_valid;
        data_array_read_next_index = {core_req_index, core_req_block_offset};
    end

    // write port logic
    always_comb begin
        l2_snoop_hit = 1'b0;
        l2_snoop_hit_way = 0;

        tag_array_write_valid_mask = '0;
        if (snoop_inv_writing) begin
            tag_array_write_index = snoop_inv_saved_PA29[ICACHE_INDEX_WIDTH-1:0];

            for (int way = 0; way < ICACHE_ASSOC; way++) begin
                if (tag_array_read_set[way].tag == snoop_inv_saved_PA29[ICACHE_TAG_WIDTH+ICACHE_INDEX_WIDTH-1:ICACHE_INDEX_WIDTH]) begin
                    tag_array_write_valid_mask[way] = '1;
                    l2_snoop_hit = 1'b1;
                    l2_snoop_hit_way = way;
                end
                tag_array_write_set[way].valid = 1'b0;
            end
        end
        else begin
            tag_array_write_index = miss_reg_missing_index;

            if (miss_reg_valid & miss_reg_data_valid) begin
                tag_array_write_valid_mask[miss_reg_old_lru_way] = '1;
            end

            for (int way = 0; way < ICACHE_ASSOC; way++) begin
                tag_array_write_set[way].valid = (miss_reg_data_blkoff == '1);
            end
        end

        for (int way = 0; way < ICACHE_ASSOC; way++) begin
            tag_array_write_set[way].byte_align_bits = '0;
            tag_array_write_set[way].tag = miss_reg_missing_tag;
                // duplicate for all ways, write valid mask will make so only write to one
                // for snooping, don't care what tag is written
        end

        data_array_write_valid_mask = '0;
        if (miss_reg_valid & miss_reg_data_valid & ~snoop_inv_writing) begin
            data_array_write_valid_mask[miss_reg_old_lru_way] = '1;
        end
        data_array_write_index = {miss_reg_missing_index, miss_reg_data_blkoff};

        for (int way = 0; way < ICACHE_ASSOC; way++) begin
            data_array_write_set[way] = miss_reg_data_buffer[miss_reg_data_blkoff];
            // duplicate for all ways, write valid mask will make so only write to one
        end
    end

    // Way PLRU + PE
    plru_updater #(
        .NUM_ENTRIES(ICACHE_ASSOC)
    ) WAY_PLRU (
        .plru_in(plru_updater_plru_in),
        .new_valid(plru_updater_new_valid),
        .new_index(plru_updater_new_index),
        .touch_valid(plru_updater_touch_valid),
        .touch_index(plru_updater_touch_index),
        .plru_out(plru_updater_plru_out)
    );
    pe_lsb #(
        .WIDTH(ICACHE_ASSOC),
        .USE_INDEX(1)
    ) WAY_PE (
        .req_vec(empty_way_pe_req_vec),
        .ack_index(empty_way_pe_ack_index)
    );

    // miss logic
    always_comb begin

        // defaults
        next_miss_reg_valid = miss_reg_valid;
        next_miss_reg_requested = miss_reg_requested;
        next_miss_reg_missing_index = miss_reg_missing_index;
        next_miss_reg_missing_tag = miss_reg_missing_tag;
        next_miss_reg_old_lru_way = miss_reg_old_lru_way;
        next_miss_reg_data_valid = miss_reg_data_valid;
        next_miss_reg_data_blkoff = miss_reg_data_blkoff;
        next_miss_reg_data_buffer = miss_reg_data_buffer;
        next_miss_reg_delay_cycle = 1'b0;

        l2_req_valid = miss_reg_valid & ~miss_reg_requested;
        l2_req_PA29 = {miss_reg_missing_tag, miss_reg_missing_index};

        miss_index_matching_core = 
            core_resp_valid
            & miss_reg_valid
            & (core_resp_index == miss_reg_missing_index);

        miss_index_and_tag_matching_core =
            miss_index_matching_core
            & (core_resp_miss_tag == miss_reg_missing_tag);

        plru_updater_plru_in = plru_array[core_resp_index];
        plru_updater_new_valid = 1'b0;
        plru_updater_touch_valid = core_resp_hit_valid;
        plru_updater_touch_index = core_resp_hit_way;

        for (int way = 0; way < ICACHE_ASSOC; way++) begin
            empty_way_pe_req_vec[way] = ~tag_array_read_set[way].valid;
        end
        empty_way_pe_req_present = |empty_way_pe_req_vec;

        // check for l2 snoop of miss reg
        if (
            l2_snoop_inv_valid
            & (l2_snoop_inv_PA29[ICACHE_INDEX_WIDTH-1:0] == miss_reg_missing_index)
            & (l2_snoop_inv_PA29[ICACHE_TAG_WIDTH+ICACHE_INDEX_WIDTH-1:ICACHE_INDEX_WIDTH] == miss_reg_missing_tag)
        ) begin
            // clear miss reg
                // could resp to core and be fine, but definitely don't want to fill cache if got inv'd
            next_miss_reg_valid = 1'b0;
        end
        // check for miss with data being filled this and next cycle
        else if (
            miss_reg_valid
            & miss_reg_data_valid
            & ~snoop_inv_writing
            & (miss_reg_data_blkoff != '1)
        ) begin
            next_miss_reg_data_blkoff = miss_reg_data_blkoff + 1;
        end
        // check for new miss
        else if (
            core_resp_miss_valid
            & (~miss_reg_valid | ~miss_index_and_tag_matching_core)
            & ~snoop_inv_writing
            & ~snoop_inv_writing_delay_cycle
        ) begin
            next_miss_reg_valid = 1'b1;
            next_miss_reg_requested = 1'b0;
            next_miss_reg_missing_index = core_resp_index;
            next_miss_reg_missing_tag = core_resp_miss_tag;
            if (empty_way_pe_req_present) begin
                next_miss_reg_old_lru_way = empty_way_pe_ack_index;
            end
            else begin
                next_miss_reg_old_lru_way = plru_updater_new_index;
            end
            next_miss_reg_data_valid = 1'b0;
            next_miss_reg_data_blkoff = 0;
            next_miss_reg_delay_cycle = 1'b0;

            plru_updater_new_valid = 1'b1;
        end
        // check for miss with last data fill
        else if (
            miss_reg_valid
            & miss_reg_data_valid
            & ~snoop_inv_writing
            & (miss_reg_data_blkoff == '1)
        ) begin
            next_miss_reg_data_valid = 1'b0;
            next_miss_reg_delay_cycle = 1'b1;
        end
        // check for miss with delay cycle
        else if (miss_reg_valid & miss_reg_delay_cycle) begin
            next_miss_reg_valid = 1'b0;
        end
        // check waiting for l2
        else if (miss_reg_valid) begin
            // l2 resp arrived
            if (
                l2_resp_valid
                & (l2_resp_PA29[ICACHE_INDEX_WIDTH-1:0] == miss_reg_missing_index)
                & (l2_resp_PA29[ICACHE_TAG_WIDTH+ICACHE_INDEX_WIDTH-1:ICACHE_INDEX_WIDTH] == miss_reg_missing_tag)
            ) begin
                next_miss_reg_requested = 1'b1;
                    // possible for old l2 resp to come in for this new miss
                        // check l2 req ready after this case for same reason
                        // don't reset data blkoff for same reason
                next_miss_reg_data_valid = 1'b1;
                next_miss_reg_data_buffer = l2_resp_data256;
            end
            // finish l2 req
            else if (~miss_reg_requested) begin
                if (l2_req_ready) begin
                    next_miss_reg_requested = 1'b1;
                end
            end
        end
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            miss_reg_valid <= 1'b0;
            miss_reg_requested <= 1'b0;
            miss_reg_missing_index <= 0;
            miss_reg_missing_tag <= 0;
            miss_reg_old_lru_way <= 0;
            miss_reg_data_valid <= 1'b0;
            miss_reg_data_blkoff <= 0;
            miss_reg_data_buffer <= '0;
            miss_reg_delay_cycle <= 1'b0;
        end
        else begin
            miss_reg_valid <= next_miss_reg_valid;
            miss_reg_requested <= next_miss_reg_requested;
            miss_reg_missing_index <= next_miss_reg_missing_index;
            miss_reg_missing_tag <= next_miss_reg_missing_tag;
            miss_reg_old_lru_way <= next_miss_reg_old_lru_way;
            miss_reg_data_valid <= next_miss_reg_data_valid;
            miss_reg_data_blkoff <= next_miss_reg_data_blkoff;
            miss_reg_data_buffer <= next_miss_reg_data_buffer;
            miss_reg_delay_cycle <= next_miss_reg_delay_cycle;
        end
    end

    // snoop inv logic
    always_comb begin
        snoop_inv_next_reading = l2_snoop_inv_valid;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            core_resp_valid <= 1'b0;
            core_resp_block_offset <= 0;
            core_resp_index <= 0;

            snoop_inv_writing <= 1'b0;
            snoop_inv_writing_delay_cycle <= 1'b0;
        end
        else begin
            core_resp_valid <= core_req_valid;
            core_resp_block_offset <= core_req_block_offset;
            core_resp_index <= core_req_index;

            snoop_inv_writing <= snoop_inv_next_reading;
            snoop_inv_writing_delay_cycle <= snoop_inv_writing;
        end
    end

    // resp to core:
    always_comb begin

        // defaults
        for (int way = 0; way < ICACHE_ASSOC; way++) begin
            core_resp_valid_by_way[way] = tag_array_read_set[way].valid & ~snoop_inv_writing;
            core_resp_tag_by_way[way] = tag_array_read_set[way].tag;
            core_resp_instr_16B_by_way[way] = data_array_read_set[way];
        end

        // miss return bypass (only index has to match, bring in new tags based on miss reg)
        if (miss_index_matching_core & (miss_reg_data_valid | miss_reg_delay_cycle)) begin
            core_resp_valid_by_way[miss_reg_old_lru_way] = 1'b1;
            core_resp_tag_by_way[miss_reg_old_lru_way] = miss_reg_missing_tag;
                // keep this arranged as when would enter cache so that lru gets set correctly
            core_resp_instr_16B_by_way[miss_reg_old_lru_way] = miss_reg_data_buffer[core_resp_block_offset];
        end
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            snoop_inv_saved_PA29 <= '0;
        end
        else begin
            snoop_inv_saved_PA29 <= l2_snoop_inv_PA29;
        end
    end

    // ----------------------------------------------------------------
    // Arrays:

    bram_1rport_1wport #(
        .INNER_WIDTH($bits(tag_entry_t) * ICACHE_ASSOC),
        .OUTER_WIDTH(ICACHE_NUM_SETS)
    ) TAG_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(tag_array_read_next_valid),
        .rindex(tag_array_read_next_index),
        .rdata(tag_array_read_set),
        .wen_byte(tag_array_write_valid_mask),
        .windex(tag_array_write_index),
        .wdata(tag_array_write_set)
    );
    
    bram_1rport_1wport #(
        .INNER_WIDTH(ICACHE_FETCH_WIDTH * 8 * ICACHE_ASSOC),
        .OUTER_WIDTH(ICACHE_NUM_SETS * 2**ICACHE_FETCH_BLOCK_OFFSET_WIDTH)
    ) DATA_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(data_array_read_next_valid),
        .rindex(data_array_read_next_index),
        .rdata(data_array_read_set),
        .wen_byte(data_array_write_valid_mask),
        .windex(data_array_write_index),
        .wdata(data_array_write_set)
    );

    always_ff @ (posedge CLK, negedge nRST) begin : PLRU_ARRAY_REG
        if (~nRST) begin
            plru_array <= '0;
        end
        else begin
            // on core hit, updater PLRU
            if (core_resp_hit_valid) begin
                plru_array[core_resp_index] <= plru_updater_plru_out;
            end
        end
    end

endmodule