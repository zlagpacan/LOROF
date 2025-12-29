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
    parameter ITLB_4MBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4MBPAGE_INDEX_WIDTH - VPN0_WIDTH - PO_WIDTH // 9b
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
    output logic                    l2_tlb_req_valid,
    output logic [ASID_WIDTH-1:0]   l2_tlb_req_ASID,
    output logic [VPN_WIDTH-1:0]    l2_tlb_req_VPN,
    input logic                     l2_tlb_req_ready,

    // resp from L2 TLB
    input logic                     l2_tlb_resp_valid,
    input logic [ASID_WIDTH-1:0]    l2_tlb_resp_ASID,
    input logic [VPN_WIDTH-1:0]     l2_tlb_resp_VPN,
    input pte_t                     l2_tlb_resp_pte,
    input logic                     l2_tlb_resp_is_superpage,
    input logic                     l2_tlb_resp_access_fault,

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

    // ----------------------------------------------------------------
    // Signals:

    // 4KB page array:
        // reg
    
    typedef struct packed {

        // access components:
        logic                               valid;
        logic [ASID_WIDTH-1:0]              ASID;
        logic [ITLB_4KBPAGE_TAG_WIDTH-1:0]  tag;

        // PTE components:
        logic [11:0]                        pte_PPN1;
        logic [9:0]                         pte_PPN0;
        logic [1:0]                         pte_RSW; // RSW; preserve SW value
        logic                               pte_D; // Dirty; no guarantees on value (e.g. self-modifying codes)
                                            // Accessed; guaranteed 1 if in any TLB
        logic                               pte_G; // Global; also relevant for VTM to bypass ASID match
        logic                               pte_U; // User
        logic                               pte_X; // eXecutable
        logic                               pte_W; // Writeable
        logic                               pte_R; // Readable
        logic                               pte_V; // Valid

        // PMA components:
        logic                               pma_executable;

    } array_4KB_entry_t;

    typedef struct packed {
        array_4KB_entry_t [ITLB_4KBPAGE_ASSOC-1:0]  entry_by_way;
        logic [ITLB_4KBPAGE_ASSOC-2:0]              plru;
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
    
    typedef struct packed {

        // access components:
        logic                               valid;
        logic [ASID_WIDTH-1:0]              ASID;
        logic [ITLB_4MBPAGE_TAG_WIDTH-1:0]  tag;

        // PTE components:
        logic [11:0]                        pte_PPN1;
        logic [9:0]                         pte_PPN0;
        logic [1:0]                         pte_RSW; // RSW; preserve SW value
        logic                               pte_D; // Dirty; no guarantees on value (e.g. self-modifying codes)
                                            // Accessed; guaranteed 1 if in any TLB
        logic                               pte_G; // Global; also relevant for VTM to bypass ASID match
        logic                               pte_U; // User
        logic                               pte_X; // eXecutable
        logic                               pte_W; // Writeable
        logic                               pte_R; // Readable
        logic                               pte_V; // Valid

        // PMA components:
        logic                               pma_executable;

    } array_4MB_entry_t;

    typedef struct packed {
        array_4MB_entry_t [ITLB_4MBPAGE_ASSOC-1:0]  entry_by_way;
        logic [ITLB_4MBPAGE_ASSOC-2:0]              plru;
    } array_4MB_set_t;

    array_4MB_set_t [ITLB_4MBPAGE_NUM_SETS-1:0] array_4MB_by_set;

    logic                                   array_4MB_read_next_valid;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    array_4MB_read_next_index;
    array_4MB_set_t                         array_4MB_read_set;

    logic                                   array_4MB_write_valid;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    array_4MB_write_index;
    array_4MB_set_t                         array_4MB_write_set;



    // mem map
    logic [PPN_WIDTH-1:0]   mem_map_PPN;
    logic                   mem_map_DRAM;
    logic                   mem_map_ROM;

    // ----------------------------------------------------------------
    // Logic:



    // array logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            array_4KB_by_set <= '0;
            array_4MB_by_set <= '0;

            array_4KB_read_set <= '0;
            array_4MB_read_set <= '0; 
        end
        else begin
            if (array_4KB_write_valid) begin
                array_4KB_by_set[array_4KB_write_index] <= array_4KB_write_set;
            end
            if (array_4MB_write_valid) begin
                array_4MB_by_set[array_4MB_write_index] <= array_4MB_write_set;
            end

            if (array_4KB_read_next_valid) begin
                array_4KB_read_set <= array_4KB_by_set[array_4KB_read_next_index];
            end
            if (array_4MB_read_next_valid) begin
                array_4MB_read_set <= array_4MB_by_set[array_4MB_read_next_index];
            end
        end
    end

endmodule