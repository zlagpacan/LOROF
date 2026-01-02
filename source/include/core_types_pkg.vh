/*
    Filename: core_types_pkg.vh
    Author: zlagpacan
    Description: Package Header File for CPU Core Types
*/

`ifndef CORE_TYPES_PKG_VH
`define CORE_TYPES_PKG_VH

package core_types_pkg;

    // ----------------------------------------------------------------
    // General:

    parameter int unsigned XLEN = 32;
    parameter int unsigned AR_COUNT = 32;
    parameter int unsigned LOG_AR_COUNT = 5;
    parameter int unsigned ASID_WIDTH = 9;

    // ----------------------------------------------------------------
    // Environment:

    parameter logic [1:0] U_MODE = 2'b00;
    parameter logic [1:0] S_MODE = 2'b01;
    parameter logic [1:0] M_MODE = 2'b11;

    parameter logic [31:0] INIT_PC = 32'h0;
    parameter logic [8:0] INIT_ASID = 9'h0;
    parameter logic [1:0] INIT_EXEC_MODE = M_MODE;
    parameter logic INIT_VIRTUAL_MODE = 1'b0;
    parameter logic INIT_MXR = 1'b0;
    parameter logic INIT_SUM = 1'b0;
	parameter logic INIT_TRAP_SFENCE = 1'b0;
	parameter logic INIT_TRAP_WFI = 1'b0;
	parameter logic INIT_TRAP_SRET = 1'b0;

    // parameter INIT_WAIT_FOR_RESTART_STATE = 1'b0;
        // depends on core

    // ----------------------------------------------------------------
    // Central:

    // prf and reg read/write
    parameter int unsigned PR_COUNT = 128;
    parameter int unsigned LOG_PR_COUNT = $clog2(PR_COUNT);
    parameter int unsigned PRF_BANK_COUNT = 4;
    parameter int unsigned LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT);

    parameter int unsigned IS_OC_BUFFER_SIZE = 2;
    parameter int unsigned FAST_FORWARD_PIPE_COUNT = 4;
        // LDU bank 0
        // LDU bank 1
        // ALU reg-reg
        // ALU reg-imm
    parameter int unsigned LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT);

    parameter int unsigned PRF_RR_COUNT = 9;
        // LDU A
        // ALU Reg-Reg / MDU A
        // ALU Reg-Reg / MDU B
        // ALU Reg-Imm A
        // BRU A
        // BRU B
        // STAMOFU A
        // STAMOFU B
        // SYSU A
    parameter int unsigned PRF_RR_INPUT_BUFFER_SIZE = IS_OC_BUFFER_SIZE;
    parameter int unsigned OC_ENTRIES = IS_OC_BUFFER_SIZE + 1;
    
    parameter int unsigned PRF_WR_COUNT = 8;
        // WR_BUF
        // LDU bank 0
        // LDU bank 1
        // ALU Reg-Reg
        // MDU
        // ALU Reg-Imm
        // BRU
        // SYSU
    parameter int unsigned PRF_WR_INPUT_BUFFER_SIZE = 2;

    // rob
    parameter int unsigned ROB_ENTRIES = 128;
    parameter int unsigned LOG_ROB_ENTRIES = $clog2(ROB_ENTRIES);

    parameter int unsigned ROB_MISPRED_Q_ENTRIES = 2;
    parameter int unsigned ROB_PR_FREE_Q_ENTRIES = 2;

    // ----------------------------------------------------------------
    // DQ's and IQ's:

    parameter int unsigned ALU_REG_MDU_DQ_ENTRIES = 4;
    parameter int unsigned ALU_REG_MDU_IQ_ENTRIES = 12;

    parameter int unsigned ALU_IMM_DQ_ENTRIES = 4;
    parameter int unsigned ALU_IMM_IQ_ENTRIES = 12;

    parameter int unsigned BRU_DQ_ENTRIES = 4;
    parameter int unsigned BRU_IQ_ENTRIES = 4;

    parameter int unsigned LDU_DQ_ENTRIES = 4;
    parameter int unsigned LDU_IQ_ENTRIES = 8;

    parameter int unsigned STAMOFU_DQ_ENTRIES = 4;
    parameter int unsigned STAMOFU_IQ_ENTRIES = 8;

    parameter int unsigned SYSU_DQ_ENTRIES = 4;

    // ----------------------------------------------------------------
    // Fetch Predictors:

    parameter int unsigned FETCH_WIDTH_B = 16;
    parameter int unsigned FETCH_WIDTH_2B = 8;

    // btb:
    parameter int unsigned BTB_NWAY_ENTRIES = 512;
    parameter int unsigned LOG_BTB_NWAY_ENTRIES = $clog2(BTB_NWAY_ENTRIES);
    parameter int unsigned BTB_ENTRY_ASSOC = 2;
    parameter int unsigned LOG_BTB_ENTRY_ASSOC = $clog2(BTB_ENTRY_ASSOC);
    parameter int unsigned BTB_NWAY_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter int unsigned LOG_BTB_NWAY_ENTRIES_PER_BLOCK = $clog2(BTB_NWAY_ENTRIES_PER_BLOCK);
    parameter int unsigned BTB_SETS = BTB_NWAY_ENTRIES / BTB_NWAY_ENTRIES_PER_BLOCK;
    parameter int unsigned BTB_INDEX_WIDTH = $clog2(BTB_SETS);
    // btb per way
    parameter int unsigned BTB_PRED_INFO_WIDTH = 8;
    parameter int unsigned BTB_TAG_WIDTH = 5;
    parameter int unsigned BTB_TARGET_WIDTH = 11;
    // btb shared over ways
    parameter int unsigned BTB_LRU_INFO_WIDTH = 1;

    parameter int unsigned SIMPLE_BRANCH_INIT_ACCURACY = 9;
    parameter int unsigned SIMPLE_BRANCH_ACCURACY_THRESHOLD = 7;
    parameter int unsigned SIMPLE_BRANCH_INACCURACY_PENALTY = 7;

    // lht:
        // using PC ^ ASID
    parameter int unsigned LH_LENGTH = 8;
    parameter int unsigned LHT_ENTRIES = 256;
    parameter int unsigned LOG_LHT_ENTRIES = $clog2(LHT_ENTRIES);
    parameter int unsigned LHT_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter int unsigned LOG_LHT_ENTRIES_PER_BLOCK = $clog2(LHT_ENTRIES_PER_BLOCK);
    parameter int unsigned LHT_SETS = LHT_ENTRIES / LHT_ENTRIES_PER_BLOCK;
    parameter int unsigned LHT_INDEX_WIDTH = $clog2(LHT_SETS);

    // lbpt:
        // using PC ^ LH ^ ASID
        // implied width of 2 for 2bc per entry
    parameter int unsigned LBPT_ENTRIES = 2**(LH_LENGTH); // want LH_LENGTH
    parameter int unsigned LBPT_ENTRIES_PER_BLOCK = 4; // 4 * 2b = 1B
    parameter int unsigned LOG_LBPT_ENTRIES_PER_BLOCK = $clog2(LBPT_ENTRIES_PER_BLOCK);
    parameter int unsigned LBPT_SETS = LBPT_ENTRIES / LBPT_ENTRIES_PER_BLOCK;
    parameter int unsigned LBPT_INDEX_WIDTH = $clog2(LBPT_SETS);

    // gbpt:
        // using PC ^ GHR ^ ASID
        // implied width of 2 for 2bc per entry
    parameter int unsigned GH_LENGTH = 12;
    parameter int unsigned GBPT_ENTRIES = 2**(GH_LENGTH); // want GH_LENGTH
    parameter int unsigned GBPT_ENTRIES_PER_BLOCK = 4; // 4 * 2b = 1B
    parameter int unsigned LOG_GBPT_ENTRIES_PER_BLOCK = $clog2(GBPT_ENTRIES_PER_BLOCK);
    parameter int unsigned GBPT_SETS = GBPT_ENTRIES / GBPT_ENTRIES_PER_BLOCK;
    parameter int unsigned GBPT_INDEX_WIDTH = $clog2(GBPT_SETS);

    // ras:
    parameter int unsigned RAS_ENTRIES = 8;
    parameter int unsigned RAS_INDEX_WIDTH = $clog2(RAS_ENTRIES);
    parameter int unsigned RAS_TARGET_WIDTH = 32 - 1;

    // upct:
    parameter int unsigned UPCT_ENTRIES = 8;
    parameter int unsigned LOG_UPCT_ENTRIES = $clog2(UPCT_ENTRIES);
    parameter int unsigned UPPER_PC_WIDTH = 32 - BTB_TARGET_WIDTH - 1;

    // mdpt:
    parameter int unsigned MDPT_INFO_WIDTH = 8;
    parameter int unsigned MDPT_ENTRIES = 2**12;
    parameter int unsigned MDPT_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter int unsigned LOG_MDPT_ENTRIES_PER_BLOCK = $clog2(MDPT_ENTRIES_PER_BLOCK);
    parameter int unsigned MDPT_SETS = MDPT_ENTRIES / MDPT_ENTRIES_PER_BLOCK;
    parameter int unsigned MDPT_INDEX_WIDTH = $clog2(MDPT_SETS);

    // ----------------------------------------------------------------
    // Frontend:

    // istream:
    parameter int unsigned ISTREAM_SETS = 8;
    parameter int unsigned ISTREAM_ENTRIES_PER_BLOCK = FETCH_WIDTH_2B;
    parameter int unsigned ISTREAM_INDEX_WIDTH = $clog2(ISTREAM_SETS);

    // free_list:
    parameter int unsigned FREE_LIST_BANK_COUNT = PRF_BANK_COUNT;
    parameter int unsigned LOG_FREE_LIST_BANK_COUNT = $clog2(FREE_LIST_BANK_COUNT);
    parameter int unsigned FREE_LIST_LENGTH_PER_BANK = PR_COUNT / FREE_LIST_BANK_COUNT;
    parameter int unsigned LOG_FREE_LIST_LENGTH_PER_BANK = $clog2(FREE_LIST_LENGTH_PER_BANK);

    parameter int unsigned FREE_LIST_SHIFT_REG_ENTRIES = 12;

    parameter int unsigned FREE_LIST_LOWER_THRESHOLD = 8;
    parameter int unsigned FREE_LIST_UPPER_THRESHOLD = 24;

    // map_table
    parameter int unsigned MAP_TABLE_READ_PORT_COUNT = 12;
    parameter int unsigned MAP_TABLE_WRITE_PORT_COUNT = 4;

    // checkpoint array:
    parameter int unsigned CHECKPOINT_COUNT = 8;
    parameter int unsigned CHECKPOINT_INDEX_WIDTH = $clog2(CHECKPOINT_COUNT);
    parameter int unsigned CHECKPOINT_THRESHOLD = 3;

    // ----------------------------------------------------------------
    // MDU:

    parameter int unsigned MDU_RESULT_CACHE_ENTRIES = 4;
    parameter int unsigned LOG_MDU_RESULT_CACHE_ENTRIES = $clog2(MDU_RESULT_CACHE_ENTRIES);

    // ----------------------------------------------------------------
    // LSQ:

    // ldu
    parameter int unsigned LDU_CQ_ENTRIES = 40;
    parameter int unsigned LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES);
    parameter int unsigned LDU_MQ_ENTRIES = 4;
    parameter int unsigned LOG_LDU_MQ_ENTRIES = $clog2(LDU_MQ_ENTRIES);

    // stamofu
    parameter int unsigned STAMOFU_CQ_ENTRIES = 24;
    parameter int unsigned LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES);
    parameter int unsigned STAMOFU_AQ_ENTRIES = 4;
    parameter int unsigned STAMOFU_MQ_ENTRIES = 4;
    parameter int unsigned LOG_STAMOFU_MQ_ENTRIES = $clog2(STAMOFU_MQ_ENTRIES);
    parameter int unsigned STAMOFU_LQ_ENTRIES_PER_BANK = 2;

    // sst
    parameter int unsigned STORE_SET_COUNT = 64; // hardwired in sst
    parameter int unsigned SSID_WIDTH = $clog2(STORE_SET_COUNT); // hardwired in sst

    // ssu
    parameter int unsigned SSU_INPUT_BUFFER_ENTRIES = 2;
    parameter int unsigned SSU_FUNNEL_BUFFER_ENTRIES = 2;

    // ----------------------------------------------------------------
    // SYSU:

endpackage

`endif // CORE_TYPES_PKG_VH
