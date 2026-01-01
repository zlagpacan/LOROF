/*
    Filename: icache_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around icache module. 
    Spec: LOROF/spec/design/icache.md
*/

`timescale 1ns/100ps

`include "system_types_pkg.vh"
import system_types_pkg::*;

module icache_wrapper #(
	parameter ICACHE_SIZE = 2**13, // 8KB, 4KB page per way,
	parameter ICACHE_BLOCK_SIZE = L1_BLOCK_SIZE, // 32B,
	parameter ICACHE_ASSOC = 2, // 2x,
	parameter LOG_ICACHE_ASSOC = $clog2(ICACHE_ASSOC), // 1b,
	parameter ICACHE_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE), // 5b,
	parameter ICACHE_NUM_SETS = ICACHE_SIZE / ICACHE_ASSOC / ICACHE_BLOCK_SIZE, // 128x,
	parameter ICACHE_INDEX_WIDTH = $clog2(ICACHE_NUM_SETS), // 7b,
	parameter ICACHE_TAG_WIDTH = PA_WIDTH - ICACHE_INDEX_WIDTH - ICACHE_BLOCK_OFFSET_WIDTH, // 34b - 7b - 5b = 22b,
	parameter ICACHE_FETCH_WIDTH = 16, // 16B,
	parameter ICACHE_FETCH_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE / ICACHE_FETCH_WIDTH) // 1b
) (

    // seq
    input logic CLK,
    input logic nRST,

    // req from core
	input logic next_core_req_valid,
	input logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] next_core_req_block_offset,
	input logic [ICACHE_INDEX_WIDTH-1:0] next_core_req_index,

    // resp to core
	output logic [ICACHE_ASSOC-1:0] last_core_resp_valid_by_way,
	output logic [ICACHE_ASSOC-1:0][ICACHE_TAG_WIDTH-1:0] last_core_resp_tag_by_way,
	output logic [ICACHE_ASSOC-1:0][ICACHE_FETCH_WIDTH-1:0][7:0] last_core_resp_instr_16B_by_way,

    // resp feedback from core
	input logic next_core_resp_hit_valid,
	input logic [LOG_ICACHE_ASSOC-1:0] next_core_resp_hit_way,
	input logic next_core_resp_miss_valid,
	input logic [ICACHE_TAG_WIDTH-1:0] next_core_resp_miss_tag,

    // req to L2
	output logic last_l2_req_valid,
	output logic [L1_BLOCK_ADDR_WIDTH-1:0] last_l2_req_PA29,
	input logic next_l2_req_ready,

    // resp from L2
	input logic next_l2_resp_valid,
	input logic [L1_BLOCK_ADDR_WIDTH-1:0] next_l2_resp_PA29,
	input logic [L1_BLOCK_SIZE_BITS-1:0] next_l2_resp_data256,

    // L2 snoop inv
	input logic next_l2_snoop_inv_valid,
	input logic [L1_BLOCK_ADDR_WIDTH-1:0] next_l2_snoop_inv_PA29
);

    // ----------------------------------------------------------------
    // Direct Module Connections:

    // req from core
	logic core_req_valid;
	logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0] core_req_block_offset;
	logic [ICACHE_INDEX_WIDTH-1:0] core_req_index;

    // resp to core
	logic [ICACHE_ASSOC-1:0] core_resp_valid_by_way;
	logic [ICACHE_ASSOC-1:0][ICACHE_TAG_WIDTH-1:0] core_resp_tag_by_way;
	logic [ICACHE_ASSOC-1:0][ICACHE_FETCH_WIDTH-1:0][7:0] core_resp_instr_16B_by_way;

    // resp feedback from core
	logic core_resp_hit_valid;
	logic [LOG_ICACHE_ASSOC-1:0] core_resp_hit_way;
	logic core_resp_miss_valid;
	logic [ICACHE_TAG_WIDTH-1:0] core_resp_miss_tag;

    // req to L2
	logic l2_req_valid;
	logic [L1_BLOCK_ADDR_WIDTH-1:0] l2_req_PA29;
	logic l2_req_ready;

    // resp from L2
	logic l2_resp_valid;
	logic [L1_BLOCK_ADDR_WIDTH-1:0] l2_resp_PA29;
	logic [L1_BLOCK_SIZE_BITS-1:0] l2_resp_data256;

    // L2 snoop inv
	logic l2_snoop_inv_valid;
	logic [L1_BLOCK_ADDR_WIDTH-1:0] l2_snoop_inv_PA29;

    // ----------------------------------------------------------------
    // Module Instantiation:

	icache #(
		.ICACHE_SIZE(ICACHE_SIZE),
		.ICACHE_BLOCK_SIZE(ICACHE_BLOCK_SIZE),
		.ICACHE_ASSOC(ICACHE_ASSOC),
		.LOG_ICACHE_ASSOC(LOG_ICACHE_ASSOC),
		.ICACHE_BLOCK_OFFSET_WIDTH(ICACHE_BLOCK_OFFSET_WIDTH),
		.ICACHE_NUM_SETS(ICACHE_NUM_SETS),
		.ICACHE_INDEX_WIDTH(ICACHE_INDEX_WIDTH),
		.ICACHE_TAG_WIDTH(ICACHE_TAG_WIDTH),
		.ICACHE_FETCH_WIDTH(ICACHE_FETCH_WIDTH),
		.ICACHE_FETCH_BLOCK_OFFSET_WIDTH(ICACHE_FETCH_BLOCK_OFFSET_WIDTH)
	) WRAPPED_MODULE (.*);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

		    // req from core
			core_req_valid <= '0;
			core_req_block_offset <= '0;
			core_req_index <= '0;

		    // resp to core
			last_core_resp_valid_by_way <= '0;
			last_core_resp_tag_by_way <= '0;
			last_core_resp_instr_16B_by_way <= '0;

		    // resp feedback from core
			core_resp_hit_valid <= '0;
			core_resp_hit_way <= '0;
			core_resp_miss_valid <= '0;
			core_resp_miss_tag <= '0;

		    // req to L2
			last_l2_req_valid <= '0;
			last_l2_req_PA29 <= '0;
			l2_req_ready <= '0;

		    // resp from L2
			l2_resp_valid <= '0;
			l2_resp_PA29 <= '0;
			l2_resp_data256 <= '0;

		    // L2 snoop inv
			l2_snoop_inv_valid <= '0;
			l2_snoop_inv_PA29 <= '0;
        end
        else begin

		    // req from core
			core_req_valid <= next_core_req_valid;
			core_req_block_offset <= next_core_req_block_offset;
			core_req_index <= next_core_req_index;

		    // resp to core
			last_core_resp_valid_by_way <= core_resp_valid_by_way;
			last_core_resp_tag_by_way <= core_resp_tag_by_way;
			last_core_resp_instr_16B_by_way <= core_resp_instr_16B_by_way;

		    // resp feedback from core
			core_resp_hit_valid <= next_core_resp_hit_valid;
			core_resp_hit_way <= next_core_resp_hit_way;
			core_resp_miss_valid <= next_core_resp_miss_valid;
			core_resp_miss_tag <= next_core_resp_miss_tag;

		    // req to L2
			last_l2_req_valid <= l2_req_valid;
			last_l2_req_PA29 <= l2_req_PA29;
			l2_req_ready <= next_l2_req_ready;

		    // resp from L2
			l2_resp_valid <= next_l2_resp_valid;
			l2_resp_PA29 <= next_l2_resp_PA29;
			l2_resp_data256 <= next_l2_resp_data256;

		    // L2 snoop inv
			l2_snoop_inv_valid <= next_l2_snoop_inv_valid;
			l2_snoop_inv_PA29 <= next_l2_snoop_inv_PA29;
        end
    end

endmodule