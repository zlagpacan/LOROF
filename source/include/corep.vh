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

    typedef logic [XLEN-1:0] xlen_t;

    parameter int unsigned AR5_COUNT = 32; // {x0:x31}, {f0:f31}
    parameter int unsigned LOG_AR5_COUNT = 5;
    parameter int unsigned AR6_COUNT = 64; // {x0:x31} U {f0:f31}
    parameter int unsigned LOG_AR6_COUNT = 6;

    typedef logic [LOG_AR5_COUNT-1:0] ar5_t;
    
    typedef struct packed {
        logic   is_fp;
        ar5_t   ar5;
    } ar6_t;

    parameter int unsigned ASID_WIDTH = 16;

    typedef logic [ASID_WIDTH-1:0] asid_t;

    // ----------------------------------------------------------------
    // Environment:

    typedef logic [1:0] exec_mode_t;

    parameter exec_mode_t EXEC_MODE_U = 2'b00;
    parameter exec_mode_t EXEC_MODE_S = 2'b01;
    parameter exec_mode_t EXEC_MODE_M = 2'b11;

    typedef logic [37:0] pc38_t;
        // legal 64b fetch addr: {{25{pc38[37]}}, pc38[37:0], 1'b0}
    typedef logic [34:0] pc35_t;
        // legal 64b fetch addr: {{25{pc35[34]}}, pc35[34:0], 3'b000, 1'b0}

    parameter pc38_t INIT_PC38 = 38'h0;
    parameter asid_t INIT_ASID = 16'h0;
    parameter exec_mode_t INIT_EXEC_MODE = EXEC_MODE_M;
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

    typedef logic [LOG_PR_COUNT-1:0]                        pr_t;
    typedef logic [LOG_PRF_BANK_COUNT-1:0]                  pr_bank_t;
    typedef logic [LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     upper_pr_t;

    function upper_pr_t upper_pr_bits (pr_t pr);
        return pr[LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT];
    endfunction

    function pr_bank_t pr_bank_bits (pr_t pr);
        return pr[LOG_PRF_BANK_COUNT-1:0];
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

    typedef logic [LOG_ROB_ENTRIES-1:0] rob_idx_t;

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
    // Fetch Unit:

    // pc38 possibilities:
        // last_pc38
            // stall or btb double hit
        // last_pc38 + 8
            // default
        // {last_pc38[37:15], btb big_target[14:0]}
            // fast redirect
        // {upc[25:0], btb small_target[11:0]}
            // fast redirect
        // ret_pc38
            // fast redirect
        // {last_pc38[37:15], ibtb big_target[14:0]}
            // slow redirect
        // {upc[25:0], ibtb small_target[11:0]}
            // slow redirect
        // restart_pc38
            // restart

    // fetch access:
    parameter int unsigned FETCH_WIDTH_B = 16;
    parameter int unsigned FETCH_WIDTH_2B = 8;
    parameter int unsigned FETCH_LANES = FETCH_WIDTH_2B;
    parameter int unsigned LOG_FETCH_LANES = $clog2(FETCH_LANES); // 3b

    typedef logic [15:0]                    fetch2B_t;
    typedef logic [31:0]                    fetch4B_t;
    typedef fetch2B_t [FETCH_LANES-1:0]     fetch16B_t;

    parameter int unsigned BTB_SMALL_TARGET_WIDTH = 12;

    parameter int unsigned FETCH_IDX_WIDTH = BTB_SMALL_TARGET_WIDTH - LOG_FETCH_LANES; // 9b

    typedef logic [LOG_FETCH_LANES-1:0]     fetch_lane_t;
    typedef logic [FETCH_IDX_WIDTH-1:0]     fetch_idx_t;
        // fetch_idx can be built in back-to-back cycles for fast redirect
        // limited by how far the small_target can reach
        // all predict and fetch structures must be fully indexable by the fetch_idx
            // itlb, icache indexing will be truly limited
            // fetch structures may not strictly require all valid pc bits in access index
                // structures naturally deal with aliasing
                // notably the pht, which can have bits exclusively indexed by gh

    function fetch_lane_t fetch_lane_bits(pc38_t pc38);
        return pc38[LOG_FETCH_LANES-1:0];
    endfunction

    function fetch_idx_t fetch_idx_bits(pc38_t pc38);
        return pc38[37:LOG_FETCH_LANES];
    endfunction 

    // btb entry: 40b
        // {info, tag, lane}
        // info: 19b
            // {action, use_upct, big_target}
            // action: 3b
            // use_upct: 1b
            // big_target: 15b
                // {upct_idx, small_target}
                // upct_idx: 3b
                // small_target: 12b
        // tag: 18b
        // lane: 3b
        // 1-wide access into associative tagged entries
    parameter int unsigned BTB_ACTION_WIDTH = 3;
    parameter int unsigned BTB_BIG_TARGET_WIDTH = 15;
    // parameter int unsigned BTB_SMALL_TARGET_WIDTH = 12; // defined ^ since determines fetch idx width
    parameter int unsigned LOG_UPCT_ENTRIES = BTB_BIG_TARGET_WIDTH - BTB_SMALL_TARGET_WIDTH;
    parameter int unsigned BTB_TAG_WIDTH = 18;
    parameter int unsigned BTB_ASSOC = 2; // hardcoded. have to do explicit lower hitting lane greater than input lane check

    typedef logic [BTB_ACTION_WIDTH-1:0]        btb_action_t;
    typedef logic [BTB_SMALL_TARGET_WIDTH-1:0]  btb_small_target_t;
    typedef logic [LOG_UPCT_ENTRIES-1:0]        upct_idx_t;
    typedef logic [BTB_TAG_WIDTH-1:0]           btb_tag_t;

    typedef struct packed {
        upct_idx_t          upct_idx;
        btb_small_target_t  small_target;
    } btb_big_target_t;
    
    typedef struct packed {
        btb_action_t        action;
        logic               use_upct;
        btb_big_target_t    big_target;
    } btb_info_t;

    typedef struct packed {
        btb_info_t      info;
        btb_tag_t       tag;
        fetch_lane_t    lane;
    } btb_entry_t;

    typedef btb_entry_t [BTB_ASSOC-1:0] btb_set_t;

    parameter btb_action_t BTB_ACTION_NONE          = 3'b000;
    parameter btb_action_t BTB_ACTION_BRANCH        = 3'b001;
    parameter btb_action_t BTB_ACTION_JUMP          = 3'b010;
    parameter btb_action_t BTB_ACTION_JUMP_L        = 3'b011;
    parameter btb_action_t BTB_ACTION_RET           = 3'b100;
    parameter btb_action_t BTB_ACTION_RET_L         = 3'b101;
    parameter btb_action_t BTB_ACTION_INDIRECT      = 3'b110;
    parameter btb_action_t BTB_ACTION_INDIRECT_L    = 3'b111;

    // btb:
        // 8-wide access into associative tagged entries
        // index: fetch idx, asid
        // tag: fetch idx, asid
    parameter int unsigned BTB_ENTRIES = 1024;
    parameter int unsigned BTB_SETS = BTB_ENTRIES / BTB_ASSOC;
    parameter int unsigned LOG_BTB_SETS = $clog2(BTB_SETS);
    
    typedef logic [LOG_BTB_SETS-1:0]        btb_idx_t;
    typedef logic [BTB_ASSOC-2:0]           btb_plru_t;
    typedef logic [$clog2(BTB_ASSOC)-1:0]   btb_way_t;

    // 2-bit saturating counter:
    typedef logic [1:0] tbc_t;

    // pht entry:
        // 2BC
        // 8-wide access into direct-mapped, untagged entries
    typedef tbc_t                           pht_entry_t;
    typedef pht_entry_t [FETCH_LANES-1:0]   pht_set_t;

    // pht:
        // 8-wide access into direct-mapped, untagged entries
        // index: fetch idx, ghr, backward asid
        // lane: redirect lane, ghr
    parameter int unsigned GH_LENGTH = 13;
    parameter int unsigned PHT_ENTRIES = 2**GH_LENGTH;
    parameter int unsigned PHT_SETS = PHT_ENTRIES / FETCH_LANES;
    parameter int unsigned LOG_PHT_SETS = $clog2(PHT_SETS);

    typedef logic [GH_LENGTH-1:0]       gh_t;
    typedef logic [LOG_PHT_SETS-1:0]    pht_idx_t;

    // ras:
        // 1-wide stack
        // index: internal sp
    parameter int unsigned RAS_ENTRIES = 16;
    parameter int unsigned LOG_RAS_ENTRIES = $clog2(RAS_ENTRIES);

    typedef logic [LOG_RAS_ENTRIES-1:0]     ras_idx_t;
    typedef logic [LOG_RAS_ENTRIES+1-1:0]   ras_cnt_t;

    // upct:
        // PLRU-allocated associative array
        // index: upct_idx
    // LOG_UPCT_ENTRIES defined ^
    // upct_idx_t defined ^
    parameter int unsigned UPCT_ENTRIES = 2**LOG_UPCT_ENTRIES;

    typedef logic [38-BTB_SMALL_TARGET_WIDTH-1:0] upc_t;
        // PC38 = {upc[25:0], small_target[11:0]}

    // ibtb entry: 16b
        // {use_upct, big_target}
        // use_upct: 1b
        // big_target: 15b
            // {upct_idx, small_target}
            // upct_idx: 3b
            // small_target: 12b
        // 1-wide access into direct-mapped, untagged entries
    typedef struct packed {
        logic               use_upct;
        btb_big_target_t    big_target;
    } ibtb_info_t;

    typedef ibtb_info_t ibtb_entry_t;

    // ibtb:
        // 1-wide access into direct-mapped, untagged entries
        // index: pc38, ghr, asid
    parameter int unsigned IBTB_ENTRIES = 32;
    parameter int unsigned IBTB_GH_WIDTH = $clog2(IBTB_ENTRIES);
    parameter int unsigned LOG_IBTB_ENTRIES = $clog2(IBTB_ENTRIES);

    typedef logic [IBTB_GH_WIDTH-1:0]   ibtb_gh_t;
    typedef ibtb_gh_t                   ibtb_idx_t;

    // sst:
        // sst params needed for mdpt entry
    parameter int unsigned STORE_SET_COUNT = 64;
    parameter int unsigned SSID_WIDTH = $clog2(STORE_SET_COUNT); // 6

    typedef logic [SSID_WIDTH-1:0] ssid_t;

    // mdpt entry: 8b
        // {tbc, ssid}
        // tbc: 2b
        // ssid: 6b
    typedef struct packed {
        tbc_t   tbc;    // 2b
        ssid_t  ssid;   // 6b
    } mdp_t;            // 8b = 1B

    typedef mdp_t                           mdpt_entry_t;
    typedef mdpt_entry_t [FETCH_LANES-1:0]  mdpt_set_t;

    // mdpt:
        // 8-wide access into direct-mapped, untagged entries
        // index: fetch idx, asid
    parameter int unsigned MDPT_ENTRIES = 1024;
    parameter int unsigned MDPT_SETS = MDPT_ENTRIES / FETCH_LANES;
    parameter int unsigned LOG_MDPT_SETS = $clog2(MDPT_SETS);

    typedef logic [LOG_MDPT_SETS-1:0] mdpt_idx_t;

    // bcb entry:
        // {gh, ras_idx, ras_cnt}
    typedef struct packed {
        gh_t        gh;
        ras_idx_t   ras_idx;
        ras_cnt_t   ras_cnt;
        logic       btb_hit;
        btb_way_t   btb_hit_way;
    } bcb_info_t;

    typedef bcb_info_t bcb_entry_t;

    // bcb:
        // 1-wide access
        // index: bcb_idx
    parameter int unsigned BCB_ENTRIES = 16;
    parameter int unsigned LOG_BCB_ENTRIES = $clog2(BCB_ENTRIES);

    typedef logic [LOG_BCB_ENTRIES-1:0] bcb_idx_t;

    // ibuffer:
    parameter int unsigned IBUFFER_ENTRIES = 8;
    parameter int unsigned LOG_IBUFFER_ENTRIES = $clog2(IBUFFER_ENTRIES);

    typedef logic [LOG_IBUFFER_ENTRIES-1:0] ibuffer_idx_t;
    
    parameter int unsigned FMID_COUNT = 16;
    parameter int unsigned LOG_FMID_COUNT = $clog2(FMID_COUNT);

    typedef logic [LOG_FMID_COUNT-1:0] fmid_t;

    // ibuffer entries:
        // all in one place so can easily modify
    typedef struct packed {
        logic [FETCH_LANES-1:0]         valid_by_lane;
        logic [FETCH_LANES-1:0]         btb_hit_by_lane;
        logic [FETCH_LANES-1:0]         redirect_taken_by_lane;
        bcb_idx_t                       bcb_idx;
        pc35_t                          src_pc35;
        pc38_t                          tgt_pc38;
        logic                           page_fault;
        logic                           access_fault;
        mdp_t [FETCH_LANES-1:0]         mdp_by_lane;
    } ibuffer_enq_info_t;

    typedef struct packed {
        logic       valid;
        logic       btb_hit;
        logic       redirect_taken;
        logic       mid_instr_redirect;
        bcb_idx_t   bcb_idx;
        pc38_t      src_pc38;
        pc38_t      tgt_pc38;
        logic       page_fault;
        logic       access_fault;
        mdp_t       mdp;
        fetch4B_t   fetch4B;
    } ibuffer_deq_entry_t;

    // ----------------------------------------------------------------
    // Decode Unit:

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
    parameter int unsigned MTCB_ENTRIES = 8;
    parameter int unsigned LOG_MTCB_ENTRIES = $clog2(MTCB_ENTRIES);

    typedef logic [LOG_MTCB_ENTRIES-1:0] mtcb_idx_t;

    // ----------------------------------------------------------------
    // MDU:

    parameter int unsigned MDU_RESULT_CACHE_ENTRIES = 4;
    parameter int unsigned LOG_MDU_RESULT_CACHE_ENTRIES = $clog2(MDU_RESULT_CACHE_ENTRIES);

    // ----------------------------------------------------------------
    // LSQ:

    // ldu
    parameter int unsigned LDU_CQ_ENTRIES = 40;
    parameter int unsigned LOG_LDU_CQ_ENTRIES = $clog2(LDU_CQ_ENTRIES);

    typedef logic [LOG_LDU_CQ_ENTRIES-1:0] ldu_cq_idx_t;

    // stamofu
    parameter int unsigned STAMOFU_CQ_ENTRIES = 24;
    parameter int unsigned LOG_STAMOFU_CQ_ENTRIES = $clog2(STAMOFU_CQ_ENTRIES);
    parameter int unsigned STAMOFU_AQ_ENTRIES = 4;
    parameter int unsigned LOG_STAMOFU_AQ_ENTRIES = $clog2(STAMOFU_AQ_ENTRIES);
    parameter int unsigned STAMOFU_LQ_ENTRIES_PER_BANK = 2;

    typedef logic [LOG_STAMOFU_CQ_ENTRIES-1:0] stamofu_cq_idx_t;
    typedef logic [LOG_STAMOFU_AQ_ENTRIES-1:0] stamofu_aq_idx_t;

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
