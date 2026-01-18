/*
    Filename: sysp.vh
    Author: zlagpacan
    Description: Package Header File for System-Level Types
*/

`ifndef SYSP_VH
`define SYSP_VH

package sysp;

    // ----------------------------------------------------------------
    // Virtual Memory:

    parameter int unsigned VA_WIDTH = 32;
    parameter int unsigned VPN_WIDTH = 20;
    parameter int unsigned VPN1_WIDTH = 10;
    parameter int unsigned VPN0_WIDTH = 10;

    parameter int unsigned PA_WIDTH = 34;
    parameter int unsigned PPN_WIDTH = 22;
    parameter int unsigned PPN1_WIDTH = 12;
    parameter int unsigned PPN0_WIDTH = 10;

    parameter int unsigned PO_WIDTH = 12;

    parameter int unsigned ASID_WIDTH = 16;

    // Sv32 Page Table Entry:
        // {PPN1[11:0], PPN0[9:0], RSW[1:0], D, A, G, U, X, W, R, V}
    typedef struct packed {
        logic [11:0]    PPN1;
        logic [9:0]     PPN0;
        logic [1:0]     RSW; // reserved
        logic           D; // Dirty
        logic           A; // Accessed
        logic           G; // Global
        logic           U; // User
        logic           X; // eXecutable
        logic           W; // Writeable
        logic           R; // Readable
        logic           V; // Valid
    } pte_t;

    // ----------------------------------------------------------------
    // Memory System Components:

    // coherence granularity 
    parameter int unsigned COH_BLOCK_SIZE = 64; // 64B
    parameter int unsigned COH_BLOCK_SIZE_BITS = COH_BLOCK_SIZE * 8; // 512b
        // AKA data512
    parameter int unsigned COH_BLOCK_OFFSET = $clog2(COH_BLOCK_SIZE); // 6b
    parameter int unsigned COH_BLOCK_ADDR_WIDTH = PA_WIDTH - COH_BLOCK_OFFSET; // 34b - 6b = 28b
        // AKA PA28

    // L1 granularity
    parameter int unsigned L1_BLOCK_SIZE = 32; // 32B
    parameter int unsigned L1_BLOCK_SIZE_BITS = L1_BLOCK_SIZE * 8; // 256b
        // AKA data256
    parameter int unsigned L1_BLOCK_OFFSET = $clog2(L1_BLOCK_SIZE); // 5b
    parameter int unsigned L1_BLOCK_ADDR_WIDTH = PA_WIDTH - L1_BLOCK_OFFSET; // 34b - 5b = 29b
        // AKA PA29

    // icache
        // sizing
    parameter int unsigned ICACHE_SIZE = 2**13; // 8KB, 4KB page per way
    parameter int unsigned ICACHE_BLOCK_SIZE = L1_BLOCK_SIZE; // 32B
    parameter int unsigned ICACHE_ASSOC = 2; // 2x
    parameter int unsigned LOG_ICACHE_ASSOC = $clog2(ICACHE_ASSOC); // 1b
        // PA bit partitioning
            // 16B*2-way fetch width
            // {tag[21:0], index[6:0], block_offset[0], fetch_offset[3:0]}
    parameter int unsigned ICACHE_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE); // 5b
    parameter int unsigned ICACHE_NUM_SETS = ICACHE_SIZE / ICACHE_ASSOC / ICACHE_BLOCK_SIZE; // 128x
    parameter int unsigned ICACHE_INDEX_WIDTH = $clog2(ICACHE_NUM_SETS); // 7b
    parameter int unsigned ICACHE_TAG_WIDTH = PA_WIDTH - ICACHE_INDEX_WIDTH - ICACHE_BLOCK_OFFSET_WIDTH; // 34b - 7b - 5b = 22b
        // fetch side interface
    parameter int unsigned ICACHE_FETCH_WIDTH = 16; // 16B
    parameter int unsigned ICACHE_FETCH_BLOCK_OFFSET_WIDTH = $clog2(ICACHE_BLOCK_SIZE / ICACHE_FETCH_WIDTH); // 1b

    // itlb
    // 4KB page array:
    parameter int unsigned ITLB_4KBPAGE_ENTRIES = 16; // 16-entry
        // 1x TLB entry per TLB block
    parameter int unsigned ITLB_4KBPAGE_ASSOC = 4; // 4x
    parameter int unsigned LOG_ITLB_4KBPAGE_ASSOC = $clog2(ITLB_4KBPAGE_ASSOC); // 2b
        // VA bit partitioning
            // {tag[17:0], index[1:0], PO[11:0]}
    parameter int unsigned ITLB_4KBPAGE_NUM_SETS = ITLB_4KBPAGE_ENTRIES / ITLB_4KBPAGE_ASSOC; // 4x
    parameter int unsigned ITLB_4KBPAGE_INDEX_WIDTH = $clog2(ITLB_4KBPAGE_NUM_SETS); // 2b
    parameter int unsigned ITLB_4KBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4KBPAGE_INDEX_WIDTH - PO_WIDTH; // 18b
    // 4MB page array:
    parameter int unsigned ITLB_4MBPAGE_ENTRIES = 4; // 4-entry
        // 1x TLB entry per TLB block
    parameter int unsigned ITLB_4MBPAGE_ASSOC = 2; // 2x
    parameter int unsigned LOG_ITLB_4MBPAGE_ASSOC = $clog2(ITLB_4MBPAGE_ASSOC); // 1b
        // VA bit partitioning
            // {tag[8:0], index[0], VPN0[9:0], PO[11:0]}
    parameter int unsigned ITLB_4MBPAGE_NUM_SETS = ITLB_4MBPAGE_ENTRIES / ITLB_4MBPAGE_ASSOC; // 2x
    parameter int unsigned ITLB_4MBPAGE_INDEX_WIDTH = $clog2(ITLB_4MBPAGE_NUM_SETS); // 1b
    parameter int unsigned ITLB_4MBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4MBPAGE_INDEX_WIDTH - VPN0_WIDTH - PO_WIDTH; // 9b
    // L2 TLB req tags
    parameter int unsigned ITLB_L2_TLB_REQ_TAG_COUNT = 4;
    parameter int unsigned ITLB_L2_TLB_REQ_TAG_WIDTH = $clog2(ITLB_L2_TLB_REQ_TAG_COUNT);

    // dcache_write_buffer

    // dcache_amo_unit

    // dcache
    parameter int unsigned DCACHE_SIZE = 2**13; // 8 KB
    parameter int unsigned DCACHE_BLOCK_SIZE = L1_BLOCK_SIZE; // 32B
    parameter int unsigned DCACHE_ASSOC = 2; // 2x
    // hardcoded 2 banks, partitioned based on lowest index bit
    parameter int unsigned DCACHE_BLOCK_OFFSET_WIDTH = $clog2(DCACHE_BLOCK_SIZE);
    parameter int unsigned DCACHE_NUM_SETS = DCACHE_SIZE / DCACHE_ASSOC / DCACHE_BLOCK_SIZE;
    parameter int unsigned DCACHE_NUM_SETS_PER_BANK = DCACHE_NUM_SETS / 2;
    parameter int unsigned DCACHE_INDEX_WIDTH = $clog2(DCACHE_NUM_SETS_PER_BANK);
    parameter int unsigned DCACHE_TAG_WIDTH = PA_WIDTH - DCACHE_INDEX_WIDTH - 1 - DCACHE_BLOCK_OFFSET_WIDTH;
    parameter int unsigned DCACHE_BANK_BIT = DCACHE_BLOCK_OFFSET_WIDTH;
    parameter int unsigned DCACHE_WORD_ADDR_BANK_BIT = DCACHE_BLOCK_OFFSET_WIDTH - 2;
    // data array access
        // grab index from index bits + upper block offset bits
    parameter int unsigned DCACHE_DATA_WORD_WIDTH = 4;
    parameter int unsigned LOG_DCACHE_DATA_WORD_WIDTH = $clog2(DCACHE_DATA_WORD_WIDTH);
    parameter int unsigned DCACHE_DATA_WORD_INDEX_WIDTH = DCACHE_INDEX_WIDTH + DCACHE_BLOCK_OFFSET_WIDTH - LOG_DCACHE_DATA_WORD_WIDTH;
    parameter int unsigned DCACHE_DATA_NUM_ROWS_PER_BANK = 2**DCACHE_DATA_WORD_INDEX_WIDTH;

    // dtlb

    // l2_cache

    // l2_tlb

    // conflict_table

    // bus_amo_unit

    // bus

    // l3_cache

    // mem_controller_write_buffer

    // mem_controller

endpackage

`endif // SYSP_VH