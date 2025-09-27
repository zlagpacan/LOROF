/*
    Filename: core.sv
    Author: zlagpacan
    Description: RTL for Instruction Cache. Blocking, 2-way associative, configurable set count and block size
    Spec: LOROF/spec/design/core.md
*/

`include "system_types_pkg.vh"
import system_types_pkg::*;

module icache #(
    parameter ICACHE_NUM_SETS = 2**7, // 128x
    parameter ICACHE_INDEX_WIDTH = $clog2(ICACHE_NUM_SETS), // 7b

    parameter ICACHE_BLOCK_SIZE = 32, // 32B
    parameter ICACHE_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE); // 5b

    parameter ICACHE_TAG_WIDTH = 22, // 22b

    parameter ICACHE_FETCH_WIDTH = 16, // 16B
    parameter ICACHE_FETCH_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE / ICACHE_FETCH_WIDTH), // 1b
) (
    // seq
    input logic CLK,
    input logic nRST,

    // req from core
    input logic                                         core_req_valid,
    input logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]   core_req_block_offset,
    input logic [ICACHE_INDEX_WIDTH-1:0]                core_req_index,

    // resp to core
    output logic [1:0]                                  core_resp_valid_by_way,
    output logic [1:0][ICACHE_TAG_WIDTH-1:0]            core_resp_tag_by_way,
    output logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0]     core_resp_instr_16B_by_way,

    // resp feedback from core
    input logic                                         core_resp_hit_valid,
    input logic                                         core_resp_hit_way,
    input logic                                         core_resp_miss_valid,
    input logic [ICACHE_TAG_WIDTH-1:0]                  core_resp_miss_tag,

    // req to L2
    output logic                            l2_req_valid,
    output logic [L1_BLOCK_ADDR_WIDTH-1:0]  l2_req_PA29,
    input logic                             l2_req_ready,

    // resp from L2
    input logic                             l2_resp_valid,
    input logic [L1_BLOCK_ADDR_WIDTH-1:0]   l2_resp_PA29,
    input logic [L1_BLOCK_SIZE_BITS-1:0]    l2_resp_data256,

    // L2 snoop inv
    input logic                             l2_snoop_inv_valid,
    input logic [L1_BLOCK_ADDR_WIDTH-1:0]   l2_snoop_inv_PA29
);

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
        logic [1:0]                         valid_by_way;
        logic [1:0][ICACHE_TAG_WIDTH-1:0]   tag_by_way;
    } tag_entry_t;

    logic                           tag_array_read_next_valid;
    logic [ICACHE_INDEX_WIDTH-1:0]  tag_array_read_next_index;
    tag_entry_t                     tag_array_read_entry;

    logic                           tag_array_write_valid;
    logic [ICACHE_INDEX_WIDTH-1:0]  tag_array_write_index;
    tag_entry_t                     tag_array_write_entry;

    // LRU array:
        // reg
    
    logic [ICACHE_NUM_SETS-1:0] lru_array, next_lru_array;
        // remember to set lru on inv

    // data array:
        // BRAM

    logic                                                           data_array_read_next_valid;
    logic [ICACHE_INDEX_WIDTH+ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]  data_array_read_next_index;
    logic [ICACHE_FETCH_WIDTH*8-1:0]                                data_array_read_entry;

    logic                                                           data_array_write_valid;
    logic [ICACHE_INDEX_WIDTH+ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]  data_array_write_index;
    logic [ICACHE_FETCH_WIDTH*8-1:0]                                data_array_write_entry;

    // read port usage:
        // core req
            // tag + data
        // l2 snoop inv
            // tag

    logic snoop_inv_next_reading;

    // write port usage:
        // miss resp
            // tag + data
        // l2 snoop inv
            // tag
            
    logic snoop_inv_writing;

    logic                                           core_resp_valid;
    logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]     core_resp_block_offset;
    logic [ICACHE_INDEX_WIDTH-1:0]                  core_resp_index;

    logic                                       miss_reg_valid, next_miss_reg_valid;
    logic                                       miss_reg_requested, next_miss_reg_requested;
    logic [L1_BLOCK_ADDR_WIDTH-1:0]             miss_reg_PA29, next_miss_reg_PA29;
    logic                                       miss_reg_lru_way, next_miss_reg_lru_way;
    logic                                       miss_reg_data_valid, next_miss_reg_data_valid;
    logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH]     miss_reg_data_blkoff, next_miss_reg_data_blkoff;
    logic [L1_BLOCK_SIZE_BITS-1:0]              miss_reg_data_buffer, next_miss_reg_data_buffer;

    // ----------------------------------------------------------------
    // Logic:

    // read port logic
    always_comb begin
        
    end

    // write port logic
    always_comb begin

    end

    // miss logic
    always_comb begin
        
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            
        end
        else begin

        end
    end

    // snoop inv logic
    always_comb begin
        snoop_inv_next_reading = l2_snoop_inv_valid;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            snoop_inv_writing <= 1'b0;
        end
        else begin
            snoop_inv_writing <= snoop_inv_next_reading;
        end
    end

    // ----------------------------------------------------------------
    // Arrays:

    bram_1rport_1wport #(
        .INNER_WIDTH((($bits(tag_entry_t)-1)/8 + 1) * 8),
        .OUTER_WIDTH(ICACHE_NUM_SETS)
    ) TAG_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(tag_array_read_next_valid),
        .rindex(tag_array_read_next_index),
        .rdata(tag_array_read_entry),
        .wen_byte({(($bits(tag_entry_t)-1)/8 + 1){tag_array_write_valid}}),
        .windex(tag_array_write_index),
        .wdata(tag_array_write_entry)        
    );
    
    bram_1rport_1wport #(
        .INNER_WIDTH(ICACHE_FETCH_WIDTH * 8),
        .OUTER_WIDTH(ICACHE_NUM_SETS * 2**ICACHE_FETCH_BLOCK_OFFSET_WIDTH)
    ) DATA_ARRAY_BRAM (
        .CLK(CLK),
        .nRST(nRST),
        .ren(data_array_read_next_valid),
        .rindex(data_array_read_next_index),
        .rdata(data_array_read_entry),
        .wen_byte({(ICACHE_FETCH_WIDTH){data_array_write_valid}}),
        .windex(data_array_write_index),
        .wdata(data_array_write_entry)
    );

    always_ff @ (posedge CLK, negedge nRST) begin : LRU_ARRAY_REG
        if (~nRST) begin
            lru_array <= '0;
        end
        else begin
            lru_array <= next_lru_array;
        end
    end

endmodule