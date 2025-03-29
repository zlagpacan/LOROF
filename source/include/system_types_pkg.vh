/*
    Filename: system_types_pkg.vh
    Author: zlagpacan
    Description: Package Header File for System-Level Types
*/

`ifndef SYSTEM_TYPES_VH
`define SYSTEM_TYPES_VH

package system_types_pkg;

    // ----------------------------------------------------------------
    // General:

    parameter VA_WIDTH = 32;
    parameter PA_WIDTH = 34;

    parameter PAGE_OFFSET_WIDTH = 12;
    parameter VPN_WIDTH = 20;
    parameter PPN_WIDTH = 22;

    // ----------------------------------------------------------------
    // Caches:

    // icache
        // sizing
    parameter ICACHE_SIZE = 2**13; // 8 KB
    parameter ICACHE_BLOCK_SIZE = 32;
    parameter ICACHE_ASSOC = 2;
        // address bit partitioning
            // 16B*2-way fetch width
            // {tag, index[], blkoff[0]}[]
    parameter ICACHE_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE);
    parameter ICACHE_NUM_SETS = ICACHE_SIZE / ICACHE_ASSOC / ICACHE_BLOCK_SIZE;
    parameter ICACHE_INDEX_WIDTH = $clog2(ICACHE_NUM_SETS);
    parameter ICACHE_TAG_WIDTH = PA_WIDTH - ICACHE_INDEX_WIDTH - ICACHE_BLOCK_OFFSET_WIDTH;
        // fetch side interface
    parameter ICACHE_FETCH_WIDTH = 16;
    parameter ICACHE_FETCH_BLOCK_OFFSET_WIDTH = 1;

    // dcache_write_buffer

    // dcache_amo_unit

    // dcache

    // l2_cache

    // conflict_table

    // bus_amo_unit

    // bus

    // l3_cache

    // mem_controller_write_buffer

    // mem_controller

    // ----------------------------------------------------------------
    // TLB's:

    // itlb

    // dtlb

    // pt_walker

endpackage

`endif // SYSTEM_TYPES_VH