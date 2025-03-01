`ifndef CORE_TYPES_VH
`define CORE_TYPES_VH

package core_types_pkg;

    // ----------------------------------------------------------------
    // General:

    parameter XLEN = 32;
    parameter ASID_WIDTH = 9;

    // ----------------------------------------------------------------
    // Central: 

    // PRF
    parameter PR_COUNT = 128;
    parameter LOG_PR_COUNT = $clog2(PR_COUNT);
    parameter PRF_BANK_COUNT = 4;
    parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT);
    parameter PRF_RR_COUNT = 11;
    parameter PRF_WR_COUNT = 7;

    // ROB
    parameter ROB_ENTRIES = 128;
    parameter LOG_ROB_ENTRIES = $clog2(ROB_ENTRIES);

    // ----------------------------------------------------------------
    // IQ's:
    
    parameter ALU_REG_MDU_IQ_ENTRIES = 8;
    parameter ALU_IMM_LDU_IQ_ENTRIES = 8;
    parameter STAMOU_IQ_ENTRIES = 16;
    parameter BRU_IQ_ENTRIES = 4;
    parameter SYS_IQ_ENTRIES = 4;

    // ----------------------------------------------------------------
    // Fetch Predictors:

    parameter FETCH_WIDTH_B = 16;
    parameter FETCH_WIDTH_2B = 8;

    // BTB:
    parameter BTB_NWAY_ENTRIES = 2048;
    parameter LOG_BTB_NWAY_ENTRIES = $clog2(BTB_NWAY_ENTRIES);
    parameter BTB_ENTRY_ASSOC = 2;
    parameter LOG_BTB_ENTRY_ASSOC = $clog2(BTB_ENTRY_ASSOC);
    parameter BTB_NWAY_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter LOG_BTB_NWAY_ENTRIES_PER_BLOCK = $clog2(BTB_NWAY_ENTRIES_PER_BLOCK);
    parameter BTB_SETS = BTB_NWAY_ENTRIES / BTB_NWAY_ENTRIES_PER_BLOCK;
    parameter BTB_INDEX_WIDTH = $clog2(BTB_SETS);
    // BTB per way
    parameter BTB_PRED_INFO_WIDTH = 8;
    parameter BTB_TAG_WIDTH = 6;
    parameter BTB_TARGET_WIDTH = 10;
    // BTB shared over ways
    parameter BTB_LRU_INFO_WIDTH = 1;

    parameter SIMPLE_BRANCH_INIT_ACCURACY = 9;
    parameter SIMPLE_BRANCH_ACCURACY_THRESHOLD = 7;
    parameter SIMPLE_BRANCH_INACCURACY_PENALTY = 7;

    // LHT:
        // using PC ^ ASID
    parameter LH_LENGTH = 8;
    parameter LHT_ENTRIES = 256;
    parameter LOG_LHT_ENTRIES = $clog2(LHT_ENTRIES);
    parameter LHT_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter LOG_LHT_ENTRIES_PER_BLOCK = $clog2(LHT_ENTRIES_PER_BLOCK);
    parameter LHT_SETS = LHT_ENTRIES / LHT_ENTRIES_PER_BLOCK;
    parameter LHT_INDEX_WIDTH = $clog2(LHT_SETS);

    // LBPT:
        // using PC ^ LH ^ ASID
        // implied width of 2 for 2bc per entry
    parameter LBPT_ENTRIES = 2**(LH_LENGTH); // want LH_LENGTH
    parameter LBPT_ENTRIES_PER_BLOCK = 4; // 4 * 2b = 1B
    parameter LOG_LBPT_ENTRIES_PER_BLOCK = $clog2(LBPT_ENTRIES_PER_BLOCK);
    parameter LBPT_SETS = LBPT_ENTRIES / LBPT_ENTRIES_PER_BLOCK;
    parameter LBPT_INDEX_WIDTH = $clog2(LBPT_SETS);

    // GBPT:
        // using PC ^ GHR ^ ASID
        // implied width of 2 for 2bc per entry
    parameter GH_LENGTH = 12;
    parameter GBPT_ENTRIES = 2**(GH_LENGTH); // want GH_LENGTH
    parameter GBPT_ENTRIES_PER_BLOCK = 4; // 4 * 2b = 1B
    parameter LOG_GBPT_ENTRIES_PER_BLOCK = $clog2(GBPT_ENTRIES_PER_BLOCK);
    parameter GBPT_SETS = GBPT_ENTRIES / GBPT_ENTRIES_PER_BLOCK;
    parameter GBPT_INDEX_WIDTH = $clog2(GBPT_SETS);

    // RAS:
    parameter RAS_ENTRIES = 8;
    parameter RAS_INDEX_WIDTH = $clog2(RAS_ENTRIES);
    parameter RAS_TARGET_WIDTH = 32 - 1;

    // UPCT:
    parameter UPCT_ENTRIES = 8; // table not designed to be parameterizable due to PLRU. constant 8
    parameter LOG_UPCT_ENTRIES = $clog2(UPCT_ENTRIES);
    parameter UPPER_PC_WIDTH = 32 - BTB_TARGET_WIDTH - 1;

    // MDPT:
    parameter MDPT_ENTRIES = 2**12;
    parameter MDPT_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B; // 8 * 2b = 2B
    parameter LOG_MDPT_ENTRIES_PER_BLOCK = $clog2(MDPT_ENTRIES_PER_BLOCK);
    parameter MDPT_SETS = MDPT_ENTRIES / MDPT_ENTRIES_PER_BLOCK;
    parameter MDPT_INDEX_WIDTH = $clog2(MDPT_SETS);

    // ----------------------------------------------------------------
    // Frontend:

    // ISTREAM:
    parameter ISTREAM_SETS = 8;
    parameter ISTREAM_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter ISTREAM_INDEX_WIDTH = $clog2(ISTREAM_BLOCKS);

endpackage

`endif // CORE_TYPES_VH