/*
    Filename: core_types_pkg.vh
    Author: zlagpacan
    Description: Package Header File for CPU Core Types
*/

`ifndef CORE_TYPES_VH
`define CORE_TYPES_VH

package core_types_pkg;

    // ----------------------------------------------------------------
    // General:

    parameter XLEN = 32;
    parameter AR_COUNT = 32;
    parameter LOG_AR_COUNT = 5;
    parameter ASID_WIDTH = 9;

    // ----------------------------------------------------------------
    // Environment:

    parameter U_MODE = 2'b00;
    parameter S_MODE = 2'b01;
    parameter M_MODE = 2'b11;

    parameter INIT_PC = 32'h0;
    parameter INIT_ASID = 9'h0;
    parameter INIT_EXEC_MODE = M_MODE;
    parameter INIT_VIRTUAL_MODE = 1'b0;
    parameter INIT_MXR = 1'b0;
    parameter INIT_SUM = 1'b0;
	parameter INIT_TRAP_SFENCE = 1'b0;
	parameter INIT_TRAP_WFI = 1'b0;
	parameter INIT_TRAP_SRET = 1'b0;

    // parameter INIT_WAIT_FOR_RESTART_STATE = 1'b0;
        // depends on core

    // ----------------------------------------------------------------
    // Central:

    // prf
    parameter PR_COUNT = 128;
    parameter LOG_PR_COUNT = $clog2(PR_COUNT);
    parameter PRF_BANK_COUNT = 4;
    parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT);
    parameter PRF_RR_COUNT = 9;
        // ALU Reg-Reg / MDU A
        // ALU Reg-Reg / MDU B
        // ALU Reg-Imm A
        // BRU A
        // BRU B
        // LDU A
        // STAMOFU A
        // STAMOFU B
        // SYSU A
    parameter PRF_WR_COUNT = 8;
        // ALU Reg-Reg
        // MDU
        // ALU Reg-Imm
        // BRU
        // LDU bank 0
        // LDU bank 1
        // STAMOFU
        // SYSU

    // rob
    parameter ROB_ENTRIES = 128;
    parameter LOG_ROB_ENTRIES = $clog2(ROB_ENTRIES);

    parameter ROB_MISPRED_Q_ENTRIES = 2;
    parameter ROB_PR_FREE_Q_ENTRIES = 2;

    // ----------------------------------------------------------------
    // DQ's and IQ's:

    parameter ALU_REG_MDU_DQ_ENTRIES = 4;
    parameter ALU_REG_MDU_IQ_ENTRIES = 12;

    parameter ALU_IMM_DQ_ENTRIES = 4;
    parameter ALU_IMM_IQ_ENTRIES = 12;

    parameter BRU_DQ_ENTRIES = 4;
    parameter BRU_IQ_ENTRIES = 4;
    
    parameter LDU_DQ_ENTRIES = 4;
    parameter LDU_IQ_ENTRIES = 8;

    parameter STAMOFU_DQ_ENTRIES = 4;
    parameter STAMOFU_IQ_ENTRIES = 8;

    parameter SYSU_DQ_ENTRIES = 4;

    // ----------------------------------------------------------------
    // Fetch Predictors:

    parameter FETCH_WIDTH_B = 16;
    parameter FETCH_WIDTH_2B = 8;

    // btb:
    parameter BTB_NWAY_ENTRIES = 512;
    parameter LOG_BTB_NWAY_ENTRIES = $clog2(BTB_NWAY_ENTRIES);
    parameter BTB_ENTRY_ASSOC = 2;
    parameter LOG_BTB_ENTRY_ASSOC = $clog2(BTB_ENTRY_ASSOC);
    parameter BTB_NWAY_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter LOG_BTB_NWAY_ENTRIES_PER_BLOCK = $clog2(BTB_NWAY_ENTRIES_PER_BLOCK);
    parameter BTB_SETS = BTB_NWAY_ENTRIES / BTB_NWAY_ENTRIES_PER_BLOCK;
    parameter BTB_INDEX_WIDTH = $clog2(BTB_SETS);
    // btb per way
    parameter BTB_PRED_INFO_WIDTH = 8;
    parameter BTB_TAG_WIDTH = 5;
    parameter BTB_TARGET_WIDTH = 11;
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
    parameter MDPT_ENTRIES = 2**12;
    parameter MDPT_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
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

    // map_table
    parameter MAP_TABLE_READ_PORT_COUNT = 12;
    parameter MAP_TABLE_WRITE_PORT_COUNT = 4;

    // checkpoint array:
    parameter CHECKPOINT_COUNT = 8;
    parameter CHECKPOINT_INDEX_WIDTH = $clog2(CHECKPOINT_COUNT);
    parameter CHECKPOINT_THRESHOLD = 3;

    // ----------------------------------------------------------------
    // LSQ:

    // ldu
    parameter LDU_CQ_ENTRIES = 40;
    parameter LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES);
    parameter LDU_MQ_ENTRIES = 4;
    parameter LOG_LDU_MQ_ENTRIES = $clog2(LDU_MQ_ENTRIES);

    // stamofu
    parameter STAMOFU_CQ_ENTRIES = 24;
    parameter LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES);
    parameter STAMOFU_AQ_ENTRIES = 4;
    parameter STAMOFU_MQ_ENTRIES = 4;
    parameter LOG_STAMOFU_MQ_ENTRIES = $clog2(STAMOFU_MQ_ENTRIES);
    parameter STAMOFU_LQ_ENTRIES = 4;

    // sst
    parameter STORE_SET_COUNT = 64; // hardwired in sst
    parameter SSID_WIDTH = $clog2(STORE_SET_COUNT); // hardwired in sst

    // ssu
    parameter SSU_INNER_BUFFER_ENTRIES = 2;
    parameter SSU_FUNNEL_BUFFER_ENTRIES = 2;

    // ----------------------------------------------------------------
    // SYSU:

endpackage

`endif // CORE_TYPES_VH
