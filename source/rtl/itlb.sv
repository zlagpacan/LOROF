/*
    Filename: itlb.sv
    Author: zlagpacan
    Description: RTL for L1 Instruction TLB. Blocking, 4KB page array, 4MB page array, configurable way counts and set counts
    Spec: LOROF/spec/design/itlb.md
*/

`include "system_types_pkg.vh"
import system_types_pkg::*;

module itlb #(
    // 4KB page array
    parameter ITLB_4KBPAGE_ENTRIES = 32, // 32-entry
    parameter ITLB_4KBPAGE_ASSOC = 2, // 2x
    parameter ITLB_4KBPAGE_NUM_SETS = ITLB_4KBPAGE_ENTRIES / ITLB_4KBPAGE_ASSOC, // 16x
    parameter ITLB_4KBPAGE_INDEX_WIDTH = $clog2(ITLB_4KBPAGE_NUM_SETS), // 4b
    parameter ITLB_4KBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4KBPAGE_INDEX_WIDTH - PO_WIDTH, // 16b

    // 4MB page array
    parameter ITLB_4MBPAGE_ENTRIES = 8, // 4-entry
    parameter ITLB_4MBPAGE_ASSOC = 2, // 1x
    parameter ITLB_4MBPAGE_NUM_SETS = ITLB_4MBPAGE_ENTRIES / ITLB_4MBPAGE_ASSOC, // 4x
    parameter ITLB_4MBPAGE_INDEX_WIDTH = $clog2(ITLB_4MBPAGE_NUM_SETS), // 2b
    parameter ITLB_4MBPAGE_TAG_WIDTH = VA_WIDTH - ITLB_4MBPAGE_INDEX_WIDTH - VPN0_WIDTH - PO_WIDTH // 8b
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

    // l2 evict to L2 TLB
    output logic                    l2_tlb_evict_valid,
    output logic [ASID_WIDTH-1:0]   l2_tlb_evict_ASID,
    output logic [VPN_WIDTH-1:0]    l2_tlb_evict_VPN,
    output pte_t                    l2_tlb_evict_pte,
    output logic                    l2_tlb_resp_is_superpage,

    // sfence invalidation
    input logic                     sfence_inv_valid,
    input logic [ASID_WIDTH-1:0]    sfence_inv_ASID,
    input logic [VA_WIDTH-1:0]      sfence_inv_VA,

    // sfence invalidation backpressure
    output logic                    sfence_inv_ready
);

    // simple hit paradigm
        // hit solely based on native array hit structures
            // also single native PMA check structure (mem_map)
        // fine since uncommon case, not latency sensitive to misses

    // ----------------------------------------------------------------
    // Signals:

    // 4KB page array:
        // reg
    
    typedef struct packed {
        logic                               valid;
        logic [ITLB_4KBPAGE_TAG_WIDTH-1:0]  tag;
        logic [ASID_WIDTH-1:0]              ASID;

        // PTE components:
        logic [11:0]                        PPN1;
        logic [9:0]                         PPN0;
                                            // RSW don't care
        logic                               Dirty; // in case have self-modifying code and evict from dTLB 
                                            // Accessed guaranteed if in any TLB
        logic                               Global; // also relevant for VTM to bypass ASID match
        logic                               User;
        logic                               eXecutable;
        logic                               Writeable;
        logic                               Readable;
        logic                               Valid;

        // other components:
        logic                               is_mem;
    } array_4KB_entry_t;

    typedef struct packed {
        array_4KB_entry_t [ITLB_4KBPAGE_ASSOC-1:0]  entry_by_way;
        logic [ITLB_4KBPAGE_ASSOC-2:0]              plru;
    } array_4KB_set_t;

    array_4KB_set_t [ITLB_4KBPAGE_NUM_SETS-1:0] array_4KB_by_set_by_way;

    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    array_4KB_read_index;
    array_4KB_entry_t                       array_4KB_read_data;

    logic                                   array_4KB_write_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    array_4KB_write_index;
    logic [$clog2(ITLB_4KBPAGE_ASSOC)-1:0]  array_4KB_write_way;
    array_4KB_entry_t                       array_4KB_write_data;

endmodule