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

    parameter int unsigned VA_WIDTH = 39;
    parameter int unsigned VPN_WIDTH = 27;
    parameter int unsigned VPN2_WIDTH = 9;
    parameter int unsigned VPN1_WIDTH = 9;
    parameter int unsigned VPN0_WIDTH = 9;

    typedef logic [VA_WIDTH-1:0]    va39_t;
    typedef logic [VPN_WIDTH-1:0]   vpn_t;
    typedef logic [VPN2_WIDTH-1:0]  vpn2_t;
    typedef logic [VPN1_WIDTH-1:0]  vpn1_t;
    typedef logic [VPN0_WIDTH-1:0]  vpn0_t;

    parameter int unsigned PA_WIDTH = 39;
    parameter int unsigned PPN_WIDTH = 27;
    parameter int unsigned PPN2_WIDTH = 9;
    parameter int unsigned PPN1_WIDTH = 9;
    parameter int unsigned PPN0_WIDTH = 9;

    typedef logic [PA_WIDTH-1:0]    pa39_t;
    typedef logic [PPN_WIDTH-1:0]   ppn_t;
    typedef logic [PPN2_WIDTH-1:0]  ppn2_t;
    typedef logic [PPN1_WIDTH-1:0]  ppn1_t;
    typedef logic [PPN0_WIDTH-1:0]  ppn0_t;

    parameter int unsigned BIG_PA_WIDTH = 56;
    parameter int unsigned BIG_PPN_WIDTH = 44;
    parameter int unsigned BIG_PPN2_WIDTH = 26;

    typedef logic [BIG_PA_WIDTH-1:0]    big_pa56_t;
    typedef logic [BIG_PPN_WIDTH-1:0]   big_ppn_t;
    typedef logic [BIG_PPN2_WIDTH-1:0]  big_ppn2_t;

    parameter int unsigned PO_WIDTH = 12;

    typedef logic [PO_WIDTH-1:0] po_t;

    // ASID: also in corep.vh
    parameter int unsigned ASID_WIDTH = 16;
    typedef logic [ASID_WIDTH-1:0] asid_t;

    // Sv39 Page Table Entry:
        // {N, PBMT[1:0], Reserved[6:0], PPN2[25:0], PPN1[8:0], PPN0[8:0], RSW[1:0], D, A, G, U, X, W, R, V}
    typedef struct packed {
        logic           n;          // unsupported
        logic [1:0]     pbmt;       // unsupported
        logic [6:0]     reserved;
        big_ppn2_t      big_ppn2;
        ppn1_t          ppn1;
        ppn0_t          ppn0;
        logic [1:0]     rsw;        // Reserved
        logic           d;          // Dirty
        logic           a;          // Accessed
        logic           g;          // Global
        logic           u;          // User
        logic           x;          // eXecutable
        logic           w;          // Writeable
        logic           r;          // Readable
        logic           v;          // Valid
    } big_pte_t;

    typedef struct packed {
        ppn2_t  ppn2;
        ppn1_t  ppn1;
        ppn0_t  ppn0;
        logic   d;      // Dirty
        logic   a;      // Accessed
        logic   g;      // Global
        logic   u;      // User
        logic   x;      // eXecutable
        logic   w;      // Writeable
        logic   r;      // Readable
        logic   v;      // Valid
    } pte_t;

    function pte_t make_small_pte (big_pte_t big_pte);
        make_small_pte.ppn2     = big_pte.big_ppn2[PPN2_WIDTH-1:0];
        make_small_pte.ppn1     = big_pte.ppn1;
        make_small_pte.ppn0     = big_pte.ppn0;
        make_small_pte.d        = big_pte.d;
        make_small_pte.a        = big_pte.a;
        make_small_pte.g        = big_pte.g;
        make_small_pte.u        = big_pte.u;
        make_small_pte.x        = big_pte.x;
        make_small_pte.w        = big_pte.w;
        make_small_pte.r        = big_pte.r;
        make_small_pte.v        = big_pte.v;
    endfunction

    function big_pte_t make_big_pte (pte_t pte);
        make_big_pte.n          = 1'b0;
        make_big_pte.pbmt       = 2'b00;
        make_big_pte.reserved   = 7'b0000000;
        make_big_pte.big_ppn2   = {17'h0, pte.ppn2}; // zero-extend pa39 to pa56
        make_big_pte.ppn1       = pte.ppn1;
        make_big_pte.ppn0       = pte.ppn0;
        make_big_pte.rsw        = 2'b00;
        make_big_pte.d          = pte.d;
        make_big_pte.a          = pte.a;
        make_big_pte.g          = pte.g;
        make_big_pte.u          = pte.u;
        make_big_pte.x          = pte.x;
        make_big_pte.w          = pte.w;
        make_big_pte.r          = pte.r;
        make_big_pte.v          = pte.v;
    endfunction

    // ----------------------------------------------------------------
    // Memory System Components:

    // coherence granularity 
    parameter int unsigned COH_BLOCK_SIZE = 64; // 64B
    parameter int unsigned COH_BLOCK_SIZE_BITS = COH_BLOCK_SIZE * 8; // 512b

    typedef logic [COH_BLOCK_SIZE-1:0][7:0] coh_block_data_t;

    parameter int unsigned COH_BLOCK_OFFSET = $clog2(COH_BLOCK_SIZE); // 6b
    parameter int unsigned COH_BLOCK_ADDR_WIDTH = PA_WIDTH - COH_BLOCK_OFFSET; // 39b - 6b = 33b

    typedef logic [COH_BLOCK_ADDR_WIDTH-1:0] coh_pa33_t;

    function coh_pa33_t coh_pa33_bits (pa39_t pa39);
        coh_pa33_bits = pa39[PA_WIDTH-1:COH_BLOCK_OFFSET];
    endfunction

    // L1 granularity
    parameter int unsigned L1_BLOCK_SIZE = 32; // 32B
    parameter int unsigned L1_BLOCK_SIZE_BITS = L1_BLOCK_SIZE * 8; // 256b

    typedef logic [L1_BLOCK_SIZE-1:0][7:0] l1_block_data_t;

    parameter int unsigned L1_BLOCK_OFFSET = $clog2(L1_BLOCK_SIZE); // 5b
    parameter int unsigned L1_BLOCK_ADDR_WIDTH = PA_WIDTH - L1_BLOCK_OFFSET; // 39b - 5b = 34b

    typedef logic [L1_BLOCK_ADDR_WIDTH-1:0] l1_pa34_t;

    function l1_pa34_t l1_pa34_bits (pa39_t pa39);
        l1_pa34_bits = pa39[PA_WIDTH-1:L1_BLOCK_OFFSET];
    endfunction

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
    parameter int unsigned ICACHE_IDX_WIDTH = $clog2(ICACHE_NUM_SETS); // 7b
    parameter int unsigned ICACHE_TAG_WIDTH = PA_WIDTH - ICACHE_IDX_WIDTH - ICACHE_BLOCK_OFFSET_WIDTH; // 34b - 7b - 5b = 22b
        // fetch side interface
            // take from corep

    typedef logic [LOG_ICACHE_ASSOC-1:0]    icache_way_t;
    typedef logic [ICACHE_IDX_WIDTH-1:0]    icache_idx_t;
    typedef logic [ICACHE_TAG_WIDTH-1:0]    icache_tag_t;


    // itlb
        // TODO: fix for RV64GC
    // 4KB page array:
    parameter int unsigned ITLB_4KBPAGE_ENTRIES = 16; // 16-entry
        // 1x TLB entry per TLB block
    parameter int unsigned ITLB_4KBPAGE_ASSOC = 4; // 4x
    parameter int unsigned LOG_ITLB_4KBPAGE_ASSOC = $clog2(ITLB_4KBPAGE_ASSOC); // 2b
        // VA bit partitioning
            // {tag[17:0], index[1:0], PO[11:0]}
    parameter int unsigned ITLB_4KBPAGE_NUM_SETS = ITLB_4KBPAGE_ENTRIES / ITLB_4KBPAGE_ASSOC; // 4x
    parameter int unsigned ITLB_4KBPAGE_IDX_WIDTH = $clog2(ITLB_4KBPAGE_NUM_SETS); // 2b
    parameter int unsigned ITLB_4KBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4KBPAGE_IDX_WIDTH - PO_WIDTH; // 18b
    // 4MB page array:
    parameter int unsigned ITLB_4MBPAGE_ENTRIES = 4; // 4-entry
        // 1x TLB entry per TLB block
    parameter int unsigned ITLB_4MBPAGE_ASSOC = 2; // 2x
    parameter int unsigned LOG_ITLB_4MBPAGE_ASSOC = $clog2(ITLB_4MBPAGE_ASSOC); // 1b
        // VA bit partitioning
            // {tag[8:0], index[0], VPN0[9:0], PO[11:0]}
    parameter int unsigned ITLB_4MBPAGE_NUM_SETS = ITLB_4MBPAGE_ENTRIES / ITLB_4MBPAGE_ASSOC; // 2x
    parameter int unsigned ITLB_4MBPAGE_IDX_WIDTH = $clog2(ITLB_4MBPAGE_NUM_SETS); // 1b
    parameter int unsigned ITLB_4MBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4MBPAGE_IDX_WIDTH - VPN0_WIDTH - PO_WIDTH; // 9b
    // L2 TLB req tags
    parameter int unsigned ITLB_L2_TLB_REQ_TAG_COUNT = 4;
    parameter int unsigned ITLB_L2_TLB_REQ_TAG_WIDTH = $clog2(ITLB_L2_TLB_REQ_TAG_COUNT);

    // dcache_write_buffer

    // dcache_amo_unit

    // dcache
        // TODO: fix for RV64GC
    parameter int unsigned DCACHE_SIZE = 2**13; // 8 KB
    parameter int unsigned DCACHE_BLOCK_SIZE = L1_BLOCK_SIZE; // 32B
    parameter int unsigned DCACHE_ASSOC = 2; // 2x
    // hardcoded 2 banks, partitioned based on lowest index bit
    parameter int unsigned DCACHE_BLOCK_OFFSET_WIDTH = $clog2(DCACHE_BLOCK_SIZE);
    parameter int unsigned DCACHE_NUM_SETS = DCACHE_SIZE / DCACHE_ASSOC / DCACHE_BLOCK_SIZE;
    parameter int unsigned DCACHE_NUM_SETS_PER_BANK = DCACHE_NUM_SETS / 2;
    parameter int unsigned DCACHE_IDX_WIDTH = $clog2(DCACHE_NUM_SETS_PER_BANK);
    parameter int unsigned DCACHE_TAG_WIDTH = PA_WIDTH - DCACHE_IDX_WIDTH - 1 - DCACHE_BLOCK_OFFSET_WIDTH;
    parameter int unsigned DCACHE_BANK_BIT = DCACHE_BLOCK_OFFSET_WIDTH;
    parameter int unsigned DCACHE_WORD_ADDR_BANK_BIT = DCACHE_BLOCK_OFFSET_WIDTH - 2;
    // data array access
        // grab index from index bits + upper block offset bits
    parameter int unsigned DCACHE_DATA_WORD_WIDTH = 4;
    parameter int unsigned LOG_DCACHE_DATA_WORD_WIDTH = $clog2(DCACHE_DATA_WORD_WIDTH);
    parameter int unsigned DCACHE_DATA_WORD_IDX_WIDTH = DCACHE_IDX_WIDTH + DCACHE_BLOCK_OFFSET_WIDTH - LOG_DCACHE_DATA_WORD_WIDTH;
    parameter int unsigned DCACHE_DATA_NUM_ROWS_PER_BANK = 2**DCACHE_DATA_WORD_IDX_WIDTH;

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