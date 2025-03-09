`ifndef CORE_TYPES_VH
`define CORE_TYPES_VH

package core_types_pkg;

    // ----------------------------------------------------------------
    // General:

    parameter XLEN = 32;
    parameter AR_COUNT = 32;
    parameter ASID_WIDTH = 9;
    parameter INIT_PC = 32'h80000000;

    // ----------------------------------------------------------------
    // Central:

    // prf
    parameter PR_COUNT = 128;
    parameter LOG_PR_COUNT = $clog2(PR_COUNT);
    parameter PRF_BANK_COUNT = 4;
    parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT);
    parameter PRF_RR_COUNT = 11;
    parameter PRF_WR_COUNT = 7;

    // rob
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

    // btb:
    parameter BTB_NWAY_ENTRIES = 2048;
    parameter LOG_BTB_NWAY_ENTRIES = $clog2(BTB_NWAY_ENTRIES);
    parameter BTB_ENTRY_ASSOC = 2;
    parameter LOG_BTB_ENTRY_ASSOC = $clog2(BTB_ENTRY_ASSOC);
    parameter BTB_NWAY_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter LOG_BTB_NWAY_ENTRIES_PER_BLOCK = $clog2(BTB_NWAY_ENTRIES_PER_BLOCK);
    parameter BTB_SETS = BTB_NWAY_ENTRIES / BTB_NWAY_ENTRIES_PER_BLOCK;
    parameter BTB_INDEX_WIDTH = $clog2(BTB_SETS);
    // btb per way
    parameter BTB_PRED_INFO_WIDTH = 8;
    parameter BTB_TAG_WIDTH = 6;
    parameter BTB_TARGET_WIDTH = 10;
    // btb shared over ways
    parameter BTB_LRU_INFO_WIDTH = 1;

    parameter SIMPLE_BRANCH_INIT_ACCURACY = 9;
    parameter SIMPLE_BRANCH_ACCURACY_THRESHOLD = 7;
    parameter SIMPLE_BRANCH_INACCURACY_PENALTY = 7;

    // lht:
        // using PC ^ ASID
    parameter LH_LENGTH = 8;
    parameter LHT_ENTRIES = 256;
    parameter LOG_LHT_ENTRIES = $clog2(LHT_ENTRIES);
    parameter LHT_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter LOG_LHT_ENTRIES_PER_BLOCK = $clog2(LHT_ENTRIES_PER_BLOCK);
    parameter LHT_SETS = LHT_ENTRIES / LHT_ENTRIES_PER_BLOCK;
    parameter LHT_INDEX_WIDTH = $clog2(LHT_SETS);

    // lbpt:
        // using PC ^ LH ^ ASID
        // implied width of 2 for 2bc per entry
    parameter LBPT_ENTRIES = 2**(LH_LENGTH); // want LH_LENGTH
    parameter LBPT_ENTRIES_PER_BLOCK = 4; // 4 * 2b = 1B
    parameter LOG_LBPT_ENTRIES_PER_BLOCK = $clog2(LBPT_ENTRIES_PER_BLOCK);
    parameter LBPT_SETS = LBPT_ENTRIES / LBPT_ENTRIES_PER_BLOCK;
    parameter LBPT_INDEX_WIDTH = $clog2(LBPT_SETS);

    // gbpt:
        // using PC ^ GHR ^ ASID
        // implied width of 2 for 2bc per entry
    parameter GH_LENGTH = 12;
    parameter GBPT_ENTRIES = 2**(GH_LENGTH); // want GH_LENGTH
    parameter GBPT_ENTRIES_PER_BLOCK = 4; // 4 * 2b = 1B
    parameter LOG_GBPT_ENTRIES_PER_BLOCK = $clog2(GBPT_ENTRIES_PER_BLOCK);
    parameter GBPT_SETS = GBPT_ENTRIES / GBPT_ENTRIES_PER_BLOCK;
    parameter GBPT_INDEX_WIDTH = $clog2(GBPT_SETS);

    // ras:
    parameter RAS_ENTRIES = 8;
    parameter RAS_INDEX_WIDTH = $clog2(RAS_ENTRIES);
    parameter RAS_TARGET_WIDTH = 32 - 1;

    // upct:
    parameter UPCT_ENTRIES = 8; // table not designed to be parameterizable due to PLRU. constant 8
    parameter LOG_UPCT_ENTRIES = $clog2(UPCT_ENTRIES);
    parameter UPPER_PC_WIDTH = 32 - BTB_TARGET_WIDTH - 1;

    // mdpt:
    parameter MDPT_INFO_WIDTH = 8;
    parameter MDPT_ENTRIES = 2**10;
    parameter MDPT_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B; // 8 * 2b = 2B
    parameter LOG_MDPT_ENTRIES_PER_BLOCK = $clog2(MDPT_ENTRIES_PER_BLOCK);
    parameter MDPT_SETS = MDPT_ENTRIES / MDPT_ENTRIES_PER_BLOCK;
    parameter MDPT_INDEX_WIDTH = $clog2(MDPT_SETS);

    // ----------------------------------------------------------------
    // Frontend:

    // istream:
    parameter ISTREAM_SETS = 8;
    parameter ISTREAM_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter ISTREAM_INDEX_WIDTH = $clog2(ISTREAM_SETS);

    // free_list:
    parameter FREE_LIST_BANK_COUNT = PRF_BANK_COUNT;
    parameter LOG_FREE_LIST_BANK_COUNT = $clog2(FREE_LIST_BANK_COUNT);
    parameter FREE_LIST_LENGTH_PER_BANK = PR_COUNT / FREE_LIST_BANK_COUNT;
    parameter LOG_FREE_LIST_LENGTH_PER_BANK = $clog2(FREE_LIST_LENGTH_PER_BANK);

    parameter FREE_LIST_SHIFT_REG_ENTRIES = 12;

    parameter FREE_LIST_LOWER_THRESHOLD = 8;
    parameter FREE_LIST_UPPER_THRESHOLD = 24;

    // ----------------------------------------------------------------
    // LSQ:

    // ldu
    parameter LDU_Q_ENTRIES = 32;

    // stamou
    parameter STAMOU_Q_ENTRIES = 24;

endpackage

`endif // CORE_TYPES_VH
