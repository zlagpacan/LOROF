/*
    Filename: itlb.sv
    Author: zlagpacan
    Description: RTL for L1 Instruction TLB. Blocking, 4KB page array, 4MB page array, configurable associativity and set count
    Spec: LOROF/spec/design/itlb.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module itlb #(
    // 4KB page array
    parameter ITLB_4KBPAGE_ENTRIES = 16, // 16-entry
    parameter ITLB_4KBPAGE_ASSOC = 4, // 4x
    parameter LOG_ITLB_4KBPAGE_ASSOC = $clog2(ITLB_4KBPAGE_ASSOC), // 2b
    parameter ITLB_4KBPAGE_NUM_SETS = ITLB_4KBPAGE_ENTRIES / ITLB_4KBPAGE_ASSOC, // 4x
    parameter ITLB_4KBPAGE_INDEX_WIDTH = $clog2(ITLB_4KBPAGE_NUM_SETS), // 2b
    parameter ITLB_4KBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4KBPAGE_INDEX_WIDTH - PO_WIDTH, // 18b

    // 4MB page array
    parameter ITLB_4MBPAGE_ENTRIES = 4, // 4-entry
    parameter ITLB_4MBPAGE_ASSOC = 2, // 2x
    parameter LOG_ITLB_4MBPAGE_ASSOC = $clog2(ITLB_4MBPAGE_ASSOC), // 1b
    parameter ITLB_4MBPAGE_NUM_SETS = ITLB_4MBPAGE_ENTRIES / ITLB_4MBPAGE_ASSOC, // 2x
    parameter ITLB_4MBPAGE_INDEX_WIDTH = $clog2(ITLB_4MBPAGE_NUM_SETS), // 1b
    parameter ITLB_4MBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4MBPAGE_INDEX_WIDTH - VPN0_WIDTH - PO_WIDTH, // 9b

    // L2 TLB req tags
    parameter ITLB_L2_TLB_REQ_TAG_COUNT = 4,
    parameter ITLB_L2_TLB_REQ_TAG_WIDTH = $clog2(ITLB_L2_TLB_REQ_TAG_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // core req
    input logic                     core_req_valid,
    input logic [1:0]               core_req_exec_mode,
    input logic                     core_req_virtual_mode,
    input logic [ASID_WIDTH-1:0]    core_req_ASID,
    input logic [VPN_WIDTH-1:0]     core_req_VPN,

    // core resp
    output logic                    core_resp_valid,
    output logic [PPN_WIDTH-1:0]    core_resp_PPN,
    output logic                    core_resp_page_fault,
    output logic                    core_resp_access_fault,

    // req to L2 TLB
    output logic                                    l2_tlb_req_valid,
    output logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0]    l2_tlb_req_tag,
    output logic [ASID_WIDTH-1:0]                   l2_tlb_req_ASID,
    output logic [VPN_WIDTH-1:0]                    l2_tlb_req_VPN,

    input logic                                     l2_tlb_req_ready,

    // resp from L2 TLB
    input logic                                     l2_tlb_resp_valid,
    input logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0]     l2_tlb_resp_tag,
    input pte_t                                     l2_tlb_resp_pte,
    input logic                                     l2_tlb_resp_is_superpage,
    input logic                                     l2_tlb_resp_access_fault,

    // evict to L2 TLB
    output logic                    l2_tlb_evict_valid,
    output logic [ASID_WIDTH-1:0]   l2_tlb_evict_ASID,
    output logic [VPN_WIDTH-1:0]    l2_tlb_evict_VPN,
    output pte_t                    l2_tlb_evict_pte,
    output logic                    l2_tlb_evict_is_superpage,

    // sfence invalidation
    input logic                     sfence_inv_valid,
    input logic [ASID_WIDTH-1:0]    sfence_inv_ASID,
    input logic [VPN_WIDTH-1:0]     sfence_inv_VPN,

    // sfence invalidation backpressure
    output logic                    sfence_inv_ready
);

    // simple hit paradigm
        // hit solely based on native array hit structures
            // also single native PMA check structure (mem_map)
        // fine since uncommon case, not latency sensitive to misses

    // index hashing: lowest VPN ^ next lowest VPN ^ lowest ASID ^ next lowest ASID
        // virtually tagged and have ASID so might as well prevent VPN aliasing
        // due to PTE replacement w/ L2 TLB, have to needlessly store index bits in lower VPN in entry
        // hashing means have to check all sets on SFENCE.VMA rs1/VPN == 0 or rs2/ASID == 0 
            // uncommon case, and can share single sfence FSM functionality, so okay with this 

    // no backpressure for evict to L2 TLB
        // best effort and uncommon case so not a big deal if miss eviction
        // evicts can only come on cycles with miss resp, so L2 TLB can indirectly apply backpressure through delay of miss resp
        // this greatly simplifies miss resp state machine guaranteeing only perform eviction on cycle when it's needing, 
            // neatly requiring no entry buffering in or out

    // tagged L2 TLB req's
        // need to make sure get most recently updated version of PTE's
        // old req with same ASID+VPN could have stale PTE with old resp arriving after newer req's resp

    // ----------------------------------------------------------------
    // Signals:

    // 4KB page array:
        // reg
    
    typedef struct packed {

        // access components:
        logic                   valid;
        logic [ASID_WIDTH-1:0]  ASID;
        logic [VPN_WIDTH-1:0]   VPN;

        // PTE components:
        logic [11:0]            pte_PPN1;
        logic [9:0]             pte_PPN0;
        logic [1:0]             pte_RSW; // RSW; preserve SW value
        logic                   pte_D; // Dirty; no guarantees on value (e.g. self-modifying codes)
                                // Accessed; guaranteed 1 if in any TLB
        logic                   pte_G; // Global; also relevant for VTM to bypass ASID match
        logic                   pte_U; // User
        logic                   pte_X; // eXecutable
        logic                   pte_W; // Writeable
        logic                   pte_R; // Readable
        logic                   pte_V; // Valid

        // PMA components:
        logic                   pma_access_fault;

    } array_entry_t;

    typedef struct packed {
        array_entry_t [ITLB_4KBPAGE_ASSOC-1:0]  entry_by_way;
        logic [ITLB_4KBPAGE_ASSOC-2:0]          plru;
    } array_4KB_set_t;

    array_4KB_set_t [ITLB_4KBPAGE_NUM_SETS-1:0] array_4KB_by_set;

    logic                                   array_4KB_read_next_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    array_4KB_read_next_index;
    array_4KB_set_t                         array_4KB_read_set;

    logic                                   array_4KB_write_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    array_4KB_write_index;
    array_4KB_set_t                         array_4KB_write_set;

    // 4MB page array:
        // reg

    // same array_entry_t as 4KB page array

    typedef struct packed {
        array_entry_t [ITLB_4MBPAGE_ASSOC-1:0]  entry_by_way;
        logic [ITLB_4MBPAGE_ASSOC-2:0]          plru;
    } array_4MB_set_t;

    array_4MB_set_t [ITLB_4MBPAGE_NUM_SETS-1:0] array_4MB_by_set;

    logic                                   array_4MB_read_next_valid;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    array_4MB_read_next_index;
    array_4MB_set_t                         array_4MB_read_set;

    logic                                   array_4MB_write_valid;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    array_4MB_write_index;
    array_4MB_set_t                         array_4MB_write_set;

    // core resp
    logic                                   core_resp_stage_valid;
    logic [1:0]                             core_resp_stage_exec_mode;
    logic                                   core_resp_stage_virtual_mode;
    logic                                   core_resp_stage_hit;
    logic                                   core_resp_stage_miss;
    logic                                   core_resp_stage_l2_req_sent;
    logic [ITLB_L2_TLB_REQ_TAG_WIDTH-1:0]   core_resp_stage_l2_req_tag;

    // first stage
    logic [ASID_WIDTH-1:0]                  first_stage_ASID;
    logic [VPN_WIDTH-1:0]                   first_stage_VPN;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    first_stage_4KB_read_next_index;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    first_stage_4MB_read_next_index;

    // second stage
    logic [ASID_WIDTH-1:0]                  second_stage_ASID;
    logic [VPN_WIDTH-1:0]                   second_stage_VPN;

    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    second_stage_4KB_read_index;
    logic [ITLB_4KBPAGE_ASSOC-1:0]          second_stage_4KB_valid_by_way;
    logic [LOG_ITLB_4KBPAGE_ASSOC-1:0]      second_stage_4KB_invalid_way;
    logic [ITLB_4KBPAGE_ASSOC-1:0]          second_stage_4KB_hit_by_way;
    logic [LOG_ITLB_4KBPAGE_ASSOC-1:0]      second_stage_4KB_hitting_way;
    logic [ITLB_4KBPAGE_ASSOC-2:0]          second_stage_4KB_old_plru;
    logic [LOG_ITLB_4KBPAGE_ASSOC-1:0]      second_stage_4KB_new_way;
    logic [ITLB_4KBPAGE_ASSOC-2:0]          second_stage_4KB_new_plru;
    logic [LOG_ITLB_4KBPAGE_ASSOC-1:0]      second_stage_4KB_fill_way;

    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    second_stage_4MB_read_index;
    logic [ITLB_4MBPAGE_ASSOC-1:0]          second_stage_4MB_valid_by_way;
    logic [LOG_ITLB_4MBPAGE_ASSOC-1:0]      second_stage_4MB_invalid_way;
    logic [ITLB_4MBPAGE_ASSOC-1:0]          second_stage_4MB_hit_by_way;
    logic [LOG_ITLB_4MBPAGE_ASSOC-1:0]      second_stage_4MB_hitting_way;
    logic [ITLB_4MBPAGE_ASSOC-2:0]          second_stage_4MB_old_plru;
    logic [LOG_ITLB_4MBPAGE_ASSOC-1:0]      second_stage_4MB_new_way;
    logic [ITLB_4MBPAGE_ASSOC-2:0]          second_stage_4MB_new_plru;
    logic [LOG_ITLB_4MBPAGE_ASSOC-1:0]      second_stage_4MB_fill_way;

    // miss request
    logic tag_tracker_new_tag_ready;

    // miss return
    logic miss_return_valid;
    logic miss_return_4KB_valid;
    logic miss_return_4MB_valid;

    // sfence inv FSM
    typedef enum logic [1:0] {
        IDLE,
        INV_SINGLE_SET,
        INV_ALL_SETS
    } sfence_fsm_state_t;
    sfence_fsm_state_t sfence_fsm_state, next_sfence_fsm_state;
    
    logic [$clog2(ITLB_4KBPAGE_ENTRIES+ITLB_4MBPAGE_ENTRIES)-2:0] sfence_fsm_index, next_sfence_fsm_index;
        // want to have enough bits for index of larger array
        // 8 + 2 = 10 -> 4b - 1b = 3b for 8
        // 8 + 8 = 16 -> 4b - 1b = 3b for 8
        // 8 + 16 = 24 -> 5b - 1b = 4b for 16

    logic sfence_fsm_active;
    logic sfence_fsm_use_index;
    logic sfence_fsm_exiting;

    // mem map
    logic [PPN_WIDTH-1:0]   mem_map_PPN;
    logic                   mem_map_DRAM;
    logic                   mem_map_ROM;

    // ----------------------------------------------------------------
    // Logic:

    // read port logic:
    always_comb begin
        // new sfence inv
        if (sfence_inv_valid & sfence_inv_ready) begin
            array_4KB_read_next_valid = 1'b1;
            array_4MB_read_next_valid = 1'b1;
            first_stage_ASID = sfence_inv_ASID;
            first_stage_VPN = sfence_inv_VPN;
        end
        // new core req
        else if (
            core_req_valid
            & ~sfence_inv_valid
            & ~(sfence_fsm_active & ~sfence_fsm_exiting)
        ) begin
            array_4KB_read_next_valid = 1'b1;
            array_4MB_read_next_valid = 1'b1;
            first_stage_ASID = core_req_ASID;
            first_stage_VPN = core_req_VPN;
        end
        else begin
            array_4KB_read_next_valid = 1'b0;
            array_4MB_read_next_valid = 1'b0;
            first_stage_ASID = core_req_ASID; // don't care
            first_stage_VPN = core_req_VPN; // don't care
        end
    end
    itlb_4KB_index_hash ITLB_4KB_INDEX_HASH (
        .ASID(first_stage_ASID),
        .VPN(first_stage_VPN),
        .index(first_stage_4KB_read_next_index)
    );
    itlb_4MB_index_hash ITLB_4MB_INDEX_HASH (
        .ASID(first_stage_ASID),
        .VPN(first_stage_VPN),
        .index(first_stage_4MB_read_next_index)
    );
    always_comb begin
        if (sfence_fsm_use_index) begin
            array_4KB_read_next_index = sfence_fsm_index[ITLB_4KBPAGE_INDEX_WIDTH-1:0];
            array_4MB_read_next_index = sfence_fsm_index[ITLB_4MBPAGE_INDEX_WIDTH-1:0];
        end
        else begin
            array_4KB_read_next_index = first_stage_4KB_read_next_index;
            array_4MB_read_next_index = first_stage_4MB_read_next_index;
        end
    end

    // second stage logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            second_stage_ASID <= 0;
            second_stage_VPN <= 0;
            second_stage_4KB_read_index <= 0;
            second_stage_4MB_read_index <= 0;
        end
        else begin
            second_stage_ASID <= first_stage_ASID;
            second_stage_VPN <= first_stage_VPN;
            second_stage_4KB_read_index <= array_4KB_read_next_index;
            second_stage_4MB_read_index <= array_4MB_read_next_index;
        end
    end
    always_comb begin
        second_stage_4KB_invalid_way = 0;
        second_stage_4KB_hitting_way = 0;
        // prioritize lower way -> iterate backwards
        for (int way = ITLB_4KBPAGE_ASSOC-1; way >= 0; way--) begin
            second_stage_4KB_valid_by_way[way] = array_4KB_read_set.entry_by_way[way].valid;
            if (~second_stage_4KB_valid_by_way[way]) begin
                second_stage_4KB_invalid_way = way;
            end
            second_stage_4KB_hit_by_way[way] = 
                array_4KB_read_set.entry_by_way[way].valid
                & (
                    array_4KB_read_set.entry_by_way[way].ASID == second_stage_ASID
                    | array_4KB_read_set.entry_by_way[way].pte_G
                    | sfence_fsm_active & (second_stage_ASID == 0)
                )
                & (
                    array_4KB_read_set.entry_by_way[way].VPN == second_stage_VPN
                    | sfence_fsm_active & (second_stage_VPN == 0)
                )
            ;
            if (second_stage_4KB_hit_by_way[way]) begin
                second_stage_4KB_hitting_way = way;
            end
        end
        second_stage_4KB_old_plru = array_4KB_read_set.plru;
    end
    always_comb begin
        second_stage_4MB_invalid_way = 0;
        second_stage_4MB_hitting_way = 0;
        // prioritize lower way -> iterate backwards
        for (int way = ITLB_4MBPAGE_ASSOC-1; way >= 0; way--) begin
            second_stage_4MB_valid_by_way[way] = array_4MB_read_set.entry_by_way[way].valid;
            if (~second_stage_4MB_valid_by_way[way]) begin
                second_stage_4MB_invalid_way = way;
            end
            second_stage_4MB_hit_by_way[way] = 
                array_4MB_read_set.entry_by_way[way].valid
                & (
                    array_4MB_read_set.entry_by_way[way].ASID == second_stage_ASID
                    | array_4MB_read_set.entry_by_way[way].pte_G
                    | sfence_fsm_active & (second_stage_ASID == 0)
                )
                & (
                    array_4MB_read_set.entry_by_way[way].VPN == second_stage_VPN
                    | sfence_fsm_active & (second_stage_VPN == 0)
                )
            ;
            if (second_stage_4MB_hit_by_way[way]) begin
                second_stage_4MB_hitting_way = way;
            end
        end
        second_stage_4MB_old_plru = array_4MB_read_set.plru;
    end
    plru_updater #(
        .NUM_ENTRIES(ITLB_4KBPAGE_ASSOC)
    ) PLRU_UPDATER_4KB (
        .plru_in(second_stage_4KB_old_plru),
        .new_valid(1'b0), // only update plru on hits
        .new_index(second_stage_4KB_new_way),
        .touch_valid(core_resp_stage_valid & core_resp_stage_virtual_mode & |second_stage_4KB_hit_by_way),
        .touch_index(second_stage_4KB_hitting_way),
        .plru_out(second_stage_4KB_new_plru)
    );
    plru_updater #(
        .NUM_ENTRIES(ITLB_4MBPAGE_ASSOC)
    ) PLRU_UPDATER_4MB (
        .plru_in(second_stage_4MB_old_plru),
        .new_valid(1'b0), // only update plru on hits
        .new_index(second_stage_4MB_new_way),
        .touch_valid(core_resp_stage_valid & core_resp_stage_virtual_mode & |second_stage_4MB_hit_by_way),
        .touch_index(second_stage_4MB_hitting_way),
        .plru_out(second_stage_4MB_new_plru)
    );

    // core resp logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            core_resp_stage_valid <= 1'b0;
            core_resp_stage_exec_mode <= INIT_EXEC_MODE;
            core_resp_stage_virtual_mode <= INIT_VIRTUAL_MODE;
            core_resp_stage_l2_req_sent <= 1'b0;
            core_resp_stage_l2_req_tag <= 0;
        end
        else begin
            if (sfence_inv_valid | (sfence_fsm_active & ~sfence_fsm_exiting)) begin
                core_resp_stage_valid <= 1'b0;
                core_resp_stage_l2_req_sent <= 1'b0;
            end
            else if (core_req_valid) begin
                core_resp_stage_valid <= 1'b1;
                core_resp_stage_exec_mode <= core_req_exec_mode;
                core_resp_stage_virtual_mode <= core_req_virtual_mode;
                core_resp_stage_l2_req_sent <= 
                    (core_resp_stage_l2_req_sent | l2_tlb_req_valid & l2_tlb_req_ready)
                    & core_req_ASID == second_stage_ASID
                    & core_req_VPN == second_stage_VPN
                ;
                if (
                    l2_tlb_req_valid & l2_tlb_req_ready
                    & core_req_ASID == second_stage_ASID
                    & core_req_VPN == second_stage_VPN
                ) begin
                    core_resp_stage_l2_req_tag <= l2_tlb_req_tag;
                end
            end
            else begin
                core_resp_stage_valid <= 1'b0;
                core_resp_stage_l2_req_sent <= 1'b0;
            end
        end
    end
    always_comb begin
        core_resp_stage_hit = |second_stage_4KB_hit_by_way | |second_stage_4MB_hit_by_way;
        core_resp_stage_miss = ~core_resp_stage_hit;
    end
    always_comb begin
        core_resp_PPN = '0;
        core_resp_page_fault = 1'b0;
        core_resp_access_fault = 1'b0;
        // TLB lookup
        if (core_resp_stage_virtual_mode) begin
            core_resp_valid = core_resp_stage_valid & core_resp_stage_hit;
            // 4KB array hit
            if (|second_stage_4KB_hit_by_way) begin
                for (int way = 0; way < ITLB_4KBPAGE_ASSOC; way++) begin
                    if (second_stage_4KB_hit_by_way[way]) begin
                        // PPN components:
                            // PPN1: array entry
                            // PPN0: array entry
                        core_resp_PPN |= {
                            array_4KB_read_set.entry_by_way[way].pte_PPN1,
                            array_4KB_read_set.entry_by_way[way].pte_PPN0
                        };
                        // page fault conditions:
                            // ~V
                            // ~X
                            // X & W & ~R
                            // U_MODE & ~U
                        core_resp_page_fault |= 
                            ~array_4KB_read_set.entry_by_way[way].pte_V
                            | ~array_4KB_read_set.entry_by_way[way].pte_X
                            | (array_4KB_read_set.entry_by_way[way].pte_W & ~array_4KB_read_set.entry_by_way[way].pte_R)
                            | (core_resp_stage_exec_mode == U_MODE & array_4KB_read_set.entry_by_way[way].pte_U)
                        ;
                        // access fault conditions:
                            // no PMA access fault (in TLB entry)
                            // given access fault from l2 resp
                        core_resp_access_fault |= array_4KB_read_set.entry_by_way[way].pma_access_fault;
                    end
                end
            end
            // 4MB array hit
            else begin
                for (int way = 0; way < ITLB_4MBPAGE_ASSOC; way++) begin
                    if (second_stage_4MB_hit_by_way[way]) begin
                        // PPN components:
                            // PPN1: array entry
                            // PPN0: core req VPN0
                        core_resp_PPN |= {
                            array_4MB_read_set.entry_by_way[way].pte_PPN1,
                            core_req_VPN[VPN0_WIDTH-1:0]
                        };
                        // page fault conditions:
                            // ~V
                            // ~X
                            // X & W & ~R
                            // U_MODE & ~U
                            // PPN0 != 0
                        core_resp_page_fault |= 
                            ~array_4MB_read_set.entry_by_way[way].pte_V
                            | ~array_4MB_read_set.entry_by_way[way].pte_X
                            | (array_4MB_read_set.entry_by_way[way].pte_W & ~array_4MB_read_set.entry_by_way[way].pte_R)
                            | (core_resp_stage_exec_mode == U_MODE & array_4MB_read_set.entry_by_way[way].pte_U)
                            | array_4MB_read_set.entry_by_way[way].pte_PPN0 != 0
                        ;
                        // access fault conditions:
                            // no PMA access fault
                            // given access fault from l2 resp
                            // these conditions are condensed into array entry access fault 
                        core_resp_access_fault |= array_4MB_read_set.entry_by_way[way].pma_access_fault;
                    end
                end
            end
        end
        // baremetal
        else begin
            core_resp_valid = core_resp_stage_valid;
                // guaranteed hit for baremetal, only have to do PMA checks
            core_resp_PPN = $signed(second_stage_VPN);
                // sign extend VPN -> PPN
            core_resp_page_fault = 1'b0;
            core_resp_access_fault = ~(mem_map_DRAM | mem_map_ROM);
        end
    end

    // miss request logic
    always_comb begin
        l2_tlb_req_valid = 
            core_resp_stage_valid
            & core_resp_stage_virtual_mode
            & core_resp_stage_miss
            & ~core_resp_stage_l2_req_sent
            & tag_tracker_new_tag_ready
        ;
        l2_tlb_req_ASID = second_stage_ASID;
        l2_tlb_req_VPN = second_stage_VPN;
    end
    tag_tracker #(
        .TAG_COUNT(ITLB_L2_TLB_REQ_TAG_COUNT)
    ) L2_TLB_REQ_TAG_TRACKER (
        .CLK(CLK),
        .nRST(nRST),
        .new_tag_consume(l2_tlb_req_valid & l2_tlb_req_ready),
        .new_tag_ready(tag_tracker_new_tag_ready),
        .new_tag(l2_tlb_req_tag),
        .old_tag_done(l2_tlb_resp_valid),
        .old_tag(l2_tlb_resp_tag)
    );

    // miss return logic
    always_comb begin
        miss_return_valid = 
            core_resp_stage_valid
            & core_resp_stage_miss
                // no double filling 
            & core_resp_stage_l2_req_sent
            & l2_tlb_resp_valid
            & l2_tlb_resp_tag == core_resp_stage_l2_req_tag
        ;
        miss_return_4KB_valid = miss_return_valid & ~l2_tlb_resp_is_superpage;
        miss_return_4MB_valid = miss_return_valid & l2_tlb_resp_is_superpage;
    end

    // l2 evict logic
    always_comb begin
        // 4KB array eviction
        if (miss_return_4KB_valid) begin
            l2_tlb_evict_valid = &second_stage_4KB_valid_by_way;
            // get ASID, VPN, pte from new way
            l2_tlb_evict_ASID = array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].ASID;
            l2_tlb_evict_VPN = array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].VPN;
            l2_tlb_evict_pte = {
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_PPN1,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_PPN0,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_RSW,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_D,
                1'b1,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_G,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_U,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_X,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_W,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_R,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_V
            };
            l2_tlb_evict_is_superpage = 1'b0;
        end
        // 4MB array eviction
        else if (miss_return_4MB_valid) begin
            l2_tlb_evict_valid = &second_stage_4MB_valid_by_way;
            // get ASID, VPN, pte from new way
            l2_tlb_evict_ASID = array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].ASID;
            l2_tlb_evict_VPN = array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].VPN;
            l2_tlb_evict_pte = {
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_PPN1,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_PPN0,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_RSW,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_D,
                1'b1,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_G,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_U,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_X,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_W,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_R,
                array_4MB_read_set.entry_by_way[second_stage_4MB_new_way].pte_V
            };
            l2_tlb_evict_is_superpage = 1'b1;
        end
        else begin
            l2_tlb_evict_valid = 1'b0;
            // rest don't cares from 4KB array
            l2_tlb_evict_ASID = array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].ASID;
            l2_tlb_evict_VPN = array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].VPN;
            l2_tlb_evict_pte = {
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_PPN1,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_PPN0,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_RSW,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_D,
                1'b1,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_G,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_U,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_X,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_W,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_R,
                array_4KB_read_set.entry_by_way[second_stage_4KB_new_way].pte_V
            };
            l2_tlb_evict_is_superpage = 1'b0;
        end
    end

    // sfence fsm logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            sfence_fsm_state <= IDLE;
            sfence_fsm_index <= 0;
        end
        else begin
            sfence_fsm_state <= next_sfence_fsm_state;
            sfence_fsm_index <= next_sfence_fsm_index;
        end
    end
    always_comb begin
        case (sfence_fsm_state)

            INV_SINGLE_SET: begin
                sfence_fsm_active = 1'b1;
                sfence_fsm_use_index = 1'b0;
                sfence_fsm_exiting = 1'b1;
                next_sfence_fsm_state = IDLE;
                next_sfence_fsm_index = 0;
            end

            INV_ALL_SETS: begin
                sfence_fsm_active = 1'b1;
                if (sfence_fsm_index == '1) begin
                    sfence_fsm_use_index = 1'b0;
                    sfence_fsm_exiting = 1'b1;
                    next_sfence_fsm_state = IDLE;
                    next_sfence_fsm_index = 0;
                end
                else begin
                    sfence_fsm_use_index = 1'b1;
                    sfence_fsm_exiting = 1'b0;
                    next_sfence_fsm_state = INV_ALL_SETS;
                    next_sfence_fsm_index = sfence_fsm_index + 1;
                end
            end
            
            default: begin // IDLE
                sfence_fsm_active = 1'b0;
                sfence_fsm_exiting = 1'b0;

                // inv all sets if all VPN's
                if (sfence_inv_valid & sfence_inv_VPN == 0) begin
                    sfence_fsm_use_index = 1'b1;
                    next_sfence_fsm_state = INV_ALL_SETS;
                    next_sfence_fsm_index = sfence_fsm_index + 1;
                end
                // inv only single set if only single VPN
                else if (sfence_inv_valid) begin
                    sfence_fsm_use_index = 1'b0;
                    next_sfence_fsm_state = INV_SINGLE_SET;
                    next_sfence_fsm_index = 0;
                end
                else begin
                    sfence_fsm_use_index = 1'b0;
                    next_sfence_fsm_state = IDLE;
                    next_sfence_fsm_index = 0;
                end
            end
        endcase
    end
    always_comb begin
        sfence_inv_ready = ~(sfence_fsm_active & ~sfence_fsm_exiting);
    end

    // write port logic:
    always_comb begin
        if (&second_stage_4KB_valid_by_way) begin
            second_stage_4KB_fill_way = second_stage_4KB_new_way;
        end
        else begin
            second_stage_4KB_fill_way = second_stage_4KB_invalid_way;
        end
    end
    always_comb begin
        array_4KB_write_index = second_stage_4KB_read_index;
        array_4KB_write_set = array_4KB_read_set;

        // miss fill
        if (miss_return_4KB_valid) begin
            array_4KB_write_valid = 1'b1;

            // fill in miss way
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].valid = 1'b1;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].ASID = second_stage_ASID;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].VPN = second_stage_VPN;

            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_PPN1 = l2_tlb_resp_pte.PPN1;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_PPN0 = l2_tlb_resp_pte.PPN0;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_RSW = l2_tlb_resp_pte.RSW;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_D = l2_tlb_resp_pte.D;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_G = l2_tlb_resp_pte.G;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_U = l2_tlb_resp_pte.U;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_X = l2_tlb_resp_pte.X;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_W = l2_tlb_resp_pte.W;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_R = l2_tlb_resp_pte.R;
            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pte_V = l2_tlb_resp_pte.V;

            array_4KB_write_set.entry_by_way[second_stage_4KB_fill_way].pma_access_fault = l2_tlb_resp_access_fault | ~(mem_map_DRAM | mem_map_ROM);
        end
        // sfence inv
        else if (sfence_fsm_active) begin
            array_4KB_write_valid = 1'b1;

            // invalidate hitting ways
            for (int way = 0; way < ITLB_4KBPAGE_ASSOC; way++) begin
                if (second_stage_4KB_hit_by_way[way]) begin
                    array_4KB_write_set.entry_by_way[way].valid = 1'b0;
                end
            end
        end
        // hit plru update
        else begin
            array_4KB_write_valid = 
                core_resp_stage_valid
                & core_resp_stage_virtual_mode
                & |second_stage_4KB_hit_by_way
            ;
            array_4KB_write_set.plru = second_stage_4KB_new_plru;
        end
    end
    always_comb begin
        array_4MB_write_index = second_stage_4MB_read_index;
        array_4MB_write_set = array_4MB_read_set;

        // miss fill
        if (miss_return_4MB_valid) begin
            array_4MB_write_valid = 1'b1;

            // fill in miss way
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].valid = 1'b1;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].ASID = second_stage_ASID;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].VPN = second_stage_VPN;

            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_PPN1 = l2_tlb_resp_pte.PPN1;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_PPN0 = l2_tlb_resp_pte.PPN0;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_RSW = l2_tlb_resp_pte.RSW;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_D = l2_tlb_resp_pte.D;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_G = l2_tlb_resp_pte.G;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_U = l2_tlb_resp_pte.U;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_X = l2_tlb_resp_pte.X;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_W = l2_tlb_resp_pte.W;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_R = l2_tlb_resp_pte.R;
            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pte_V = l2_tlb_resp_pte.V;

            array_4MB_write_set.entry_by_way[second_stage_4MB_fill_way].pma_access_fault = l2_tlb_resp_access_fault | ~(mem_map_DRAM | mem_map_ROM);
        end
        // sfence inv
        else if (sfence_fsm_active) begin
            array_4MB_write_valid = 1'b1;

            // invalidate hitting ways
            for (int way = 0; way < ITLB_4MBPAGE_ASSOC; way++) begin
                if (second_stage_4MB_hit_by_way[way]) begin
                    array_4MB_write_set.entry_by_way[way].valid = 1'b0;
                end
            end
        end
        // hit plru update
        else begin
            array_4MB_write_valid = 
                core_resp_stage_valid
                & core_resp_stage_virtual_mode
                & |second_stage_4MB_hit_by_way
            ;
            array_4MB_write_set.plru = second_stage_4MB_new_plru;
        end
    end

    // mem map logic:
    always_comb begin
        if (core_resp_stage_virtual_mode) begin
            // need mem map for tlb entry fill
            mem_map_PPN = {
                l2_tlb_resp_pte.PPN1,
                l2_tlb_resp_pte.PPN0
            };
        end
        else begin
            // need mem map for baremetal access addr
            mem_map_PPN = $signed(second_stage_VPN);
        end
    end
    mem_map MEM_MAP (
        .PPN(mem_map_PPN),
        .DRAM(mem_map_DRAM),
        .ROM(mem_map_ROM)
    );

    // array logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            array_4KB_by_set <= '0;
            array_4MB_by_set <= '0;

            array_4KB_read_set <= '0;
            array_4MB_read_set <= '0; 
        end
        else begin
            // 4KB array write
            if (array_4KB_write_valid) begin
                array_4KB_by_set[array_4KB_write_index] <= array_4KB_write_set;
            end

            // 4MB array write
            if (array_4MB_write_valid) begin
                array_4MB_by_set[array_4MB_write_index] <= array_4MB_write_set;
            end

            // 4KB array write to read forward
            if (
                array_4KB_read_next_valid
                & array_4KB_write_valid
                & array_4KB_read_next_index == array_4KB_write_index
            ) begin
                array_4KB_read_set <= array_4KB_write_set;
            end
            // otherwise regular 4KB array read
            else if (array_4KB_read_next_valid) begin
                array_4KB_read_set <= array_4KB_by_set[array_4KB_read_next_index];
            end

            // 4MB array write to read forward
            if (
                array_4MB_read_next_valid
                & array_4MB_write_valid
                & array_4MB_read_next_index == array_4MB_write_index
            ) begin
                array_4MB_read_set <= array_4MB_write_set;
            end
            // otherwise regular 4MB array read
            else if (array_4MB_read_next_valid) begin
                array_4MB_read_set <= array_4MB_by_set[array_4MB_read_next_index];
            end
        end
    end

endmodule