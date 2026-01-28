/*
    Filename: corep.vh
    Author: zlagpacan
    Description: Package Header File for CPU Core Types
*/

`ifndef COREP_VH
`define COREP_VH

package corep;

    // ----------------------------------------------------------------
    // General:

    parameter int unsigned XLEN = 64;

    typedef logic [XLEN-1:0] XLEN_t;

    parameter int unsigned AR5_COUNT = 32; // {x0:x31}, {f0:f31}
    parameter int unsigned LOG_AR5_COUNT = 5;
    parameter int unsigned AR6_COUNT = 64; // {x0:x31} U {f0:f31}
    parameter int unsigned LOG_AR6_COUNT = 6;

    typedef logic [LOG_AR5_COUNT-1:0] AR5_t;
    
    typedef struct packed {
        logic   is_fp;
        AR5_t   ar5;
    } AR6_t;

    parameter int unsigned ASID_WIDTH = 16;

    typedef logic [ASID_WIDTH-1:0] ASID_t;

    // ----------------------------------------------------------------
    // Environment:

    typedef logic [1:0] EXEC_MODE_t;

    parameter EXEC_MODE_t EXEC_MODE_U = 2'b00;
    parameter EXEC_MODE_t EXEC_MODE_S = 2'b01;
    parameter EXEC_MODE_t EXEC_MODE_M = 2'b11;

    typedef logic [37:0] PC38_t;

    parameter PC38_t INIT_PC38 = 38'h0;
    parameter ASID_t INIT_ASID = 16'h0;
    parameter EXEC_MODE_t INIT_EXEC_MODE = EXEC_MODE_M;
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

    typedef logic [LOG_PR_COUNT-1:0]                        PR_t;
    typedef logic [LOG_PRF_BANK_COUNT-1:0]                  PR_bank_t;
    typedef logic [LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     upper_PR_t;

    function upper_PR_t upper_PR_bits (PR_t PR);
        return PR[LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT];
    endfunction

    function PR_bank_t PR_bank_bits (PR_t PR);
        return PR[LOG_PRF_BANK_COUNT-1:0];
    endfunction

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

    typedef logic [LOG_ROB_ENTRIES-1:0] ROB_idx_t;

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

    parameter int unsigned FPU_DQ_ENTRIES = 4;
    parameter int unsigned FPU_IQ_ENTRIES = 8;

    parameter int unsigned LDU_DQ_ENTRIES = 4;
    parameter int unsigned LDU_IQ_ENTRIES = 8;

    parameter int unsigned STAMOFU_DQ_ENTRIES = 4;
    parameter int unsigned STAMOFU_IQ_ENTRIES = 8;

    parameter int unsigned SYSU_DQ_ENTRIES = 4;

    // ----------------------------------------------------------------
    // Fetch Predictors:

    // PC38 possibilities:
        // last_pc38
        // last_pc38 + 8
        // {last_pc38[37:12], big_target[11:0]}
        // {upc.upper[25:0], small_target[8:0], upc.lane[2:0]}
        // ras ret pc38
        // ibtb pc38

    // 2-bit saturating counter:
    typedef logic [1:0] TBC_t;

    // fetch access:
    parameter int unsigned FETCH_WIDTH_B = 16;
    parameter int unsigned FETCH_LANES = 8;
    parameter int unsigned LOG_FETCH_LANES = $clog2(FETCH_LANES);

    typedef logic [LOG_FETCH_LANES-1:0] fetch_lane_t;
    typedef logic [38-LOG_FETCH_LANES-1:0] fetch_idx_t;

    function fetch_lane_t fetch_lane_bits(PC38_t PC38);
        return PC38[LOG_FETCH_LANES-1:0];
    endfunction

    function fetch_idx_t fetch_idx_bits(PC38_t PC38);
        return PC38[37:LOG_FETCH_LANES];
    endfunction 

    // btb entry:
        // {action, use_upct, big_target, tag}
        // 8-wide / 8x fetch lane access into associative tagged entries
    parameter int unsigned BTB_ACTION_WIDTH = 3;
    parameter int unsigned BTB_BIG_TARGET_WIDTH = 12;
    parameter int unsigned BTB_SMALL_TARGET_WIDTH = 9;
    parameter int unsigned LOG_UPCT_ENTRIES = BTB_BIG_TARGET_WIDTH - BTB_SMALL_TARGET_WIDTH;
    parameter int unsigned BTB_TAG_WIDTH = 8;
    parameter int unsigned BTB_ASSOC = 2;

    typedef logic [BTB_ACTION_WIDTH-1:0]        BTB_action_t;
    typedef logic [BTB_SMALL_TARGET_WIDTH-1:0]  BTB_small_target_t;
    typedef logic [LOG_UPCT_ENTRIES-1:0]        UPCT_idx_t;
    typedef logic [BTB_TAG_WIDTH-1:0]           BTB_tag_t;

    typedef struct packed {
        UPCT_idx_t          upct_idx;
        BTB_small_target_t  small_target;
    } BTB_big_target_t;
    
    typedef struct packed {
        BTB_action_t        action;
        logic               use_upct;
        BTB_big_target_t    big_target;
    } BTB_info_t;

    typedef struct packed {
        BTB_info_t  info;
        BTB_tag_t   tag;
    } BTB_entry_t;

    typedef BTB_entry_t [FETCH_LANES-1:0][BTB_ASSOC-1:0] BTB_set_t;

    parameter BTB_action_t BTB_ACTION_NONE          = 3'b000;
    parameter BTB_action_t BTB_ACTION_BRANCH        = 3'b001;
    parameter BTB_action_t BTB_ACTION_JUMP          = 3'b010;
    parameter BTB_action_t BTB_ACTION_JUMP_L        = 3'b011;
    parameter BTB_action_t BTB_ACTION_RET           = 3'b100;
    parameter BTB_action_t BTB_ACTION_RET_L         = 3'b101;
    parameter BTB_action_t BTB_ACTION_INDIRECT      = 3'b110;
    parameter BTB_action_t BTB_ACTION_INDIRECT_L    = 3'b111;

    // btb:
        // 8-wide access into associative tagged entries
        // index: PC, ASID
        // tag: PC, ASID
    parameter int unsigned BTB_ENTRIES = 1024;
    parameter int unsigned BTB_SETS = BTB_ENTRIES / BTB_ASSOC / FETCH_LANES; // 1024 / 2 / 8 = 64
    parameter int unsigned LOG_BTB_SETS = $clog2(BTB_SETS);
    
    typedef logic [LOG_BTB_SETS-1:0]        BTB_idx_t;
    typedef logic [BTB_ASSOC-2:0]           BTB_plru_t;
    typedef logic [$clog2(BTB_ASSOC)-1:0]   BTB_way_idx_t;

    // gbpt entry:
        // 2BC
        // 8-wide access into direct-mapped, untagged entries
    typedef TBC_t                           GBPT_entry_t;
    typedef GBPT_entry_t [FETCH_LANES-1:0]  GBPT_set_t;

    // gbpt:
        // 8-wide access into direct-mapped, untagged entries
        // index: PC, GHR, ASID
    parameter int unsigned GH_LENGTH = 9;
    parameter int unsigned GBPT_SETS = 2**GH_LENGTH;
    parameter int unsigned GBPT_ENTRIES = GBPT_SETS * FETCH_LANES;

    typedef logic [GH_LENGTH-1:0]   GH_t;
    typedef GH_t                    GBPT_idx_t;

    // ras:
        // 1-wide stack
    parameter int unsigned RAS_ENTRIES = 16;
    parameter int unsigned LOG_RAS_ENTRIES = $clog2(RAS_ENTRIES);

    typedef logic [LOG_RAS_ENTRIES-1:0]     RAS_idx_t;
    typedef logic [LOG_RAS_ENTRIES+1-1:0]   RAS_count_t;

    // upct:
        // PLRU-allocated array
    // LOG_UPCT_ENTRIES defined ^
    // UPCT_idx_t defined ^
    parameter int unsigned UPCT_ENTRIES = 2**LOG_UPCT_ENTRIES;

    typedef logic [38-BTB_SMALL_TARGET_WIDTH-1:0] UPC_t;
        // PC38 = {upc.upper[27:0], small_target[8:0]}

    // ibtb entry:
        // {use_upct, big_target}
        // 1-wide access into direct-mapped, untagged entries
    typedef struct packed {
        logic               use_upct;
        BTB_big_target_t    big_target;
    } IBTB_info_t;

    typedef IBTB_info_t IBTB_entry_t;

    // ibtb:
        // 1-wide access into direct-mapped, untagged entries
        // index: PC, GHR, ASID
    parameter int unsigned IBTB_ENTRIES = 32;
    parameter int unsigned IBTB_GH_WIDTH = $clog2(IBTB_ENTRIES);
    parameter int unsigned LOG_IBTB_ENTRIES = $clog2(IBTB_ENTRIES);

    typedef logic [IBTB_GH_WIDTH-1:0]   IBTB_GH_t;
    typedef IBTB_GH_t                   IBTB_idx_t;

    // sst:
        // sst params needed for mdpt entry
    parameter int unsigned STORE_SET_COUNT = 64;
    parameter int unsigned SSID_WIDTH = $clog2(STORE_SET_COUNT); // 6

    typedef logic [SSID_WIDTH-1:0] SSID_t;

    // mdpt entry:
        // 2BC + SSID
    typedef struct packed {
        TBC_t   tbc;    // 2b
        SSID_t  ssid;   // 6b
    } MDP_t;            // 8b = 1B

    typedef MDP_t                           MDPT_entry_t;
    typedef MDPT_entry_t [FETCH_LANES-1:0]  MDPT_set_t;

    // mdpt:
        // 8-wide access into direct-mapped, untagged entries
        // index: PC, ASID
    parameter int unsigned MDPT_ENTRIES = 1024;
    parameter int unsigned MDPT_SETS = MDPT_ENTRIES / FETCH_LANES;
    parameter int unsigned LOG_MDPT_SETS = $clog2(MDPT_SETS);

    typedef logic [LOG_MDPT_SETS-1:0] MDPT_idx_t;

    // ----------------------------------------------------------------
    // Frontend:

    // ibuffer:
    parameter int unsigned IBUFFER_SETS = 8;
    parameter int unsigned LOG_IBUFFER_SETS = $clog2(IBUFFER_SETS);

    typedef logic [LOG_IBUFFER_SETS-1:0] IBUFFER_idx_t;

    // free_list:
    parameter int unsigned FREE_LIST_BANK_COUNT = PRF_BANK_COUNT;
    parameter int unsigned LOG_FREE_LIST_BANK_COUNT = $clog2(FREE_LIST_BANK_COUNT);
    parameter int unsigned FREE_LIST_LENGTH_PER_BANK = PR_COUNT / FREE_LIST_BANK_COUNT;
    parameter int unsigned LOG_FREE_LIST_LENGTH_PER_BANK = $clog2(FREE_LIST_LENGTH_PER_BANK);

    parameter int unsigned FREE_LIST_SHIFT_REG_ENTRIES = 12;

    parameter int unsigned FREE_LIST_LOWER_THRESHOLD = 8;
    parameter int unsigned FREE_LIST_UPPER_THRESHOLD = 24;

    // map_table
    parameter int unsigned MAP_TABLE_ARF_READ_PORT_COUNT = 12;
    parameter int unsigned MAP_TABLE_ARF_WRITE_PORT_COUNT = 4;
        // for FARF, most likely want to limit the ports and force 2-beat
            // dense FP is very uncommon
           // map_table complexity increases very quickly
    parameter int unsigned MAP_TABLE_FARF_READ_PORT_COUNT = 16;
    parameter int unsigned MAP_TABLE_FARF_WRITE_PORT_COUNT = 4;

    // checkpoint array:
    parameter int unsigned CHECKPOINT_COUNT = 8;
    parameter int unsigned LOG_CHECKPOINT_COUNT = $clog2(CHECKPOINT_COUNT);
    parameter int unsigned CHECKPOINT_THRESHOLD = 3;

    typedef logic [LOG_CHECKPOINT_COUNT-1:0] CHECKPOINT_idx_t;

    // ----------------------------------------------------------------
    // MDU:

    parameter int unsigned MDU_RESULT_CACHE_ENTRIES = 4;
    parameter int unsigned LOG_MDU_RESULT_CACHE_ENTRIES = $clog2(MDU_RESULT_CACHE_ENTRIES);

    // ----------------------------------------------------------------
    // LSQ:

    // ldu
    parameter int unsigned LDU_CQ_ENTRIES = 40;
    parameter int unsigned LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES);

    typedef logic [LOG_LDU_CQ_ENTRIES-1:0] LDU_CQ_idx_t;

    // stamofu
    parameter int unsigned STAMOFU_CQ_ENTRIES = 24;
    parameter int unsigned LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES);
    parameter int unsigned STAMOFU_AQ_ENTRIES = 4;
    parameter int unsigned LOG_STAMOFU_AQ_ENTRIES = $clog2(STAMOFU_AQ_ENTRIES);
    parameter int unsigned STAMOFU_LQ_ENTRIES_PER_BANK = 2;

    typedef logic [LOG_STAMOFU_CQ_ENTRIES-1:0] STAMOFU_CQ_idx_t;
    typedef logic [LOG_STAMOFU_AQ_ENTRIES-1:0] STAMOFU_AQ_idx_t;

    // ssu
    parameter int unsigned SSU_INPUT_BUFFER_ENTRIES = 2;
    parameter int unsigned SSU_FUNNEL_BUFFER_ENTRIES = 2;

    // ----------------------------------------------------------------
    // SYSU:



    // ----------------------------------------------------------------
    // FPU:
        // get from fpnew_pkg

    

endpackage

`endif // COREP_VH
