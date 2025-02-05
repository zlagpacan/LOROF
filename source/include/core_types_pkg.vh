`ifndef CORE_TYPES_VH
`define CORE_TYPES_VH

package core_types_pkg;

    // general
    parameter XLEN = 32;

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

    // IQ's
    
    // Shared IQ's
    parameter ALU_REG_MD_IQ_ENTRIES = 8;
    parameter ALU_IMM_LD_IQ_ENTRIES = 16;
    parameter ST_AMO_IQ_ENTRIES = 16;
    parameter BRU_IQ_ENTRIES = 6;
    parameter SYS_IQ_ENTRIES = 4;

    // Branch Prediction
    parameter BTB_ENTRIES = 512;
    parameter LOG_BTB_ENTRIES = $clog2(BTB_ENTRIES);
    parameter BTB_ENTRIES_PER_BLOCK = 4;
    parameter LOG_BTB_ENTRIES_PER_BLOCK = 2;
    parameter BTB_BANK_COUNT = 2;
    parameter LOG_BTB_BANK_COUNT = 1;
    parameter BTB_BLOCKS_PER_BANK = BTB_ENTRIES / BTB_ENTRIES_PER_BLOCK / BTB_BANK_COUNT;
    parameter BTB_INDEX_WIDTH = $clog2(BTB_BLOCKS_PER_BANK);

    parameter BTB_PRED_INFO_WIDTH = 8;
    parameter BTB_TAG_WIDTH = 4;
    parameter BTB_TARGET_WIDTH = 12;
        // likely want sum of these or sum of desired subsets to be power of 2

    parameter UPPER_PC_TABLE_ENTRIES = 4;
    parameter UPPER_PC_WIDTH = 30 - BTB_TARGET_WIDTH;

    parameter LH_LENGTH = 8;
    parameter LHT_ENTRIES = 16;
    parameter LOG_LHT_ENTRIES = $clog2(LHT_ENTRIES); 
    parameter LBPT_ENTRIES = 2**(LH_LENGTH); // using PC ^ LH
    parameter LOG_LBPT_ENTRIES = $clog2(LBPT_ENTRIES);

    parameter GH_LENGTH = 12;
    parameter GBPT_ENTRIES = 2**(GH_LENGTH); // using PC ^ GHR
    parameter LOG_GBPT_ENTRIES = $clog2(GBPT_ENTRIES);

    parameter RAS_DEPTH = 8;
    parameter RAS_TARGET_WIDTH = BTB_TARGET_WIDTH;

endpackage

`endif // CORE_TYPES_VH