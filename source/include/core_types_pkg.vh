`ifndef CORE_TYPES_VH
`define CORE_TYPES_VH

package core_types_pkg;

    // general
    parameter XLEN = 32;
    parameter ASID_WIDTH = 9;

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

    // IQ's:
    
    // Shared IQ's
    parameter ALU_REG_MDU_IQ_ENTRIES = 8;
    parameter ALU_IMM_LDU_IQ_ENTRIES = 8;
    parameter STAMOU_IQ_ENTRIES = 16;
    parameter BRU_IQ_ENTRIES = 6;
    parameter SYS_IQ_ENTRIES = 4;

    // Branch Prediction:

    // BTB
    parameter BTB_NWAY_ENTRIES = 2048;
    parameter LOG_BTB_NWAY_ENTRIES = $clog2(BTB_NWAY_ENTRIES);
    parameter BTB_ENTRY_ASSOC = 2;
    parameter LOG_BTB_ENTRY_ASSOC = $clog2(BTB_ENTRY_ASSOC);
    parameter BTB_NWAY_ENTRIES_PER_BLOCK = 8;
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

    parameter UPPER_PC_TABLE_ENTRIES = 8;
    parameter UPPER_PC_WIDTH = 32 - BTB_TARGET_WIDTH - 1;

    parameter LH_LENGTH = 8;
    parameter LHT_ENTRIES = 16; // using PC ^ ASID
    parameter LOG_LHT_ENTRIES = $clog2(LHT_ENTRIES);
    parameter LBPT_ENTRIES = 2**(LH_LENGTH); // using PC ^ LH ^ ASID
    parameter LOG_LBPT_ENTRIES = $clog2(LBPT_ENTRIES);

    parameter GH_LENGTH = 12;
    parameter GBPT_ENTRIES = 2**(GH_LENGTH); // using PC ^ GHR ^ ASID
    parameter LOG_GBPT_ENTRIES = $clog2(GBPT_ENTRIES);

    parameter RAS_DEPTH = 8;
    parameter RAS_TARGET_WIDTH = BTB_TARGET_WIDTH;

endpackage

`endif // CORE_TYPES_VH