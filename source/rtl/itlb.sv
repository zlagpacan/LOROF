/*
    Filename: itlb.sv
    Author: zlagpacan
    Description: RTL for L1 Instruction TLB. Blocking, 4KB page array, 4MB page array, configurable associativity and set count
    Spec: LOROF/spec/design/itlb.md
*/

`include "system_types_pkg.vh"
import system_types_pkg::*;

module itlb #(
    // 4KB page array
    parameter ITLB_4KBPAGE_ENTRIES = 16, // 16-entry
    parameter ITLB_4KBPAGE_ASSOC = 4, // 4x
    parameter LOG_ITLB_4KBPAGE_ASSOC = $clog2(ITLB_4KBPAGE_ASSOC), // 2b
    parameter ITLB_4KBPAGE_NUM_SETS = ITLB_4KBPAGE_ENTRIES / ITLB_4KBPAGE_ASSOC, // 4x
    parameter ITLB_4KBPAGE_INDEX_WIDTH = $clog2(ITLB_4KBPAGE_NUM_SETS), // 2b

    // 4MB page array
    parameter ITLB_4MBPAGE_ENTRIES = 4, // 4-entry
    parameter ITLB_4MBPAGE_ASSOC = 2, // 2x
    parameter LOG_ITLB_4MBPAGE_ASSOC = $clog2(ITLB_4MBPAGE_ASSOC), // 1b
    parameter ITLB_4MBPAGE_NUM_SETS = ITLB_4MBPAGE_ENTRIES / ITLB_4MBPAGE_ASSOC, // 2x
    parameter ITLB_4MBPAGE_INDEX_WIDTH = $clog2(ITLB_4MBPAGE_NUM_SETS), // 1b
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
    output logic                    l2_tlb_evict_is_superpage,
    input logic                     l2_tlb_evict_ready,

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
                                            // RSW; don't care
        logic                               pte_D; // Dirty; no guarantees on value (e.g. self-modifying codes)
                                            // Accessed; guaranteed 1 if in any TLB
        logic                               pte_G; // Global; also relevant for VTM to bypass ASID match
        logic                               pte_U; // User
        logic                               pte_X; // eXecutable
        logic                               pte_W; // Writeable
        logic                               pte_R; // Readable
        logic                               pte_V; // Valid

        // PMA components:
        logic                               is_mem;

    } array_4KB_entry_t;

    typedef struct packed {
        array_4KB_entry_t [ITLB_4KBPAGE_ASSOC-1:0]  entry_by_way;
        logic [ITLB_4KBPAGE_ASSOC-2:0]              plru;
    } array_4KB_set_t;

    array_4KB_set_t [ITLB_4KBPAGE_NUM_SETS-1:0] array_4KB_by_set_by_way;

    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    array_4KB_read_index;
    array_4KB_set_t                         array_4KB_read_set;

    logic                                   array_4KB_write_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    array_4KB_write_index;
    logic [LOG_ITLB_4KBPAGE_ASSOC-1:0]      array_4KB_write_way;
    array_4KB_entry_t                       array_4KB_write_data;

    // 4MB page array:
        // reg
    
    typedef struct packed {

        // access components:
        logic                               valid;
        logic [ITLB_4MBPAGE_TAG_WIDTH-1:0]  tag;
        logic [ASID_WIDTH-1:0]              ASID;

        // PTE components:
        logic [11:0]                        pte_PPN1;
        logic [9:0]                         pte_PPN0;
                                            // RSW; don't care
        logic                               pte_D; // Dirty; no guarantees on value (e.g. self-modifying codes)
                                            // Accessed; guaranteed 1 if in any TLB
        logic                               pte_G; // Global; also relevant for VTM to bypass ASID match
        logic                               pte_U; // User
        logic                               pte_X; // eXecutable
        logic                               pte_W; // Writeable
        logic                               pte_R; // Readable
        logic                               pte_V; // Valid

        // other components:
        logic                               is_mem;

    } array_4MB_entry_t;

    typedef struct packed {
        array_4MB_entry_t [ITLB_4MBPAGE_ASSOC-1:0]  entry_by_way;
        logic [ITLB_4MBPAGE_ASSOC-2:0]              plru;
    } array_4MB_set_t;

    array_4MB_set_t [ITLB_4MBPAGE_NUM_SETS-1:0] array_4MB_by_set_by_way;

    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    array_4MB_read_index;
    array_4MB_set_t                         array_4MB_read_set;

    logic                                   array_4MB_write_valid;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    array_4MB_write_index;
    logic [LOG_ITLB_4MBPAGE_ASSOC-1:0]      array_4MB_write_way;
    array_4MB_entry_t                       array_4MB_write_data;

    // read port usage:
        // arbitration b/w:
            // sfence inv
            // core req
        // use 4KB array and 4MB array together
        // core backpressure is only implicit so prioritize sfence inv

    logic                                   read_port_sfence_inv_using;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    read_port_sfence_inv_4KB_read_index;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    read_port_sfence_inv_4MB_read_index;

    logic                                   read_port_core_req_using;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    read_port_core_req_4KB_read_index;
    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    read_port_core_req_4MB_read_index;

    // write port usage:
        // arbitration b/w:
            // miss resp
            // sfence inv
        // use 4KB array and 4MB array together
        // sfence can be easily backpressured and don't want to buffer miss resp data so prioritize miss resp

    logic                                   write_port_miss_resp_using;
    logic                                   write_port_miss_resp_4KB_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    write_port_miss_resp_4KB_index;
    logic [LOG_ITLB_4KBPAGE_ASSOC]          write_port_miss_resp_4KB_way;
    array_4KB_entry_t                       write_port_miss_resp_4KB_data;
    logic                                   write_port_miss_resp_4MB_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    write_port_miss_resp_4MB_index;
    logic [LOG_ITLB_4KBPAGE_ASSOC]          write_port_miss_resp_4MB_way;
    array_4KB_entry_t                       write_port_miss_resp_4MB_data;

    logic                                   write_port_sfence_inv_using;
    logic                                   write_port_sfence_inv_4KB_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    write_port_sfence_inv_4KB_index;
    logic [LOG_ITLB_4KBPAGE_ASSOC]          write_port_sfence_inv_4KB_way;
    array_4KB_entry_t                       write_port_sfence_inv_4KB_data;
    logic                                   write_port_sfence_inv_4MB_valid;
    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    write_port_sfence_inv_4MB_index;
    logic [LOG_ITLB_4KBPAGE_ASSOC]          write_port_sfence_inv_4MB_way;
    array_4KB_entry_t                       write_port_sfence_inv_4MB_data;

    // core resp
    logic                   core_resp_stage_valid;
    logic                   core_resp_stage_missing;
    logic [ASID_WIDTH-1:0]  core_resp_stage_ASID;
    logic [VPN_WIDTH-1:0]   core_resp_stage_VPN;

    // miss reg
    logic                   miss_reg_valid;
    logic                   miss_reg_requested;
    logic [ASID_WIDTH-1:0]  miss_reg_ASID;
    logic [VPN_WIDTH-1:0]   miss_reg_VPN;

    // sfence inv
    logic                                   sfence_inv_second_stage_valid;
    logic                                   sfence_inv_second_stage_stall;

    logic [ITLB_4KBPAGE_INDEX_WIDTH-1:0]    sfence_inv_second_stage_4KB_index;
    logic [ITLB_4KBPAGE_ASSOC-1:0]          sfence_inv_second_stage_4KB_hit_by_way;

    logic [ITLB_4MBPAGE_INDEX_WIDTH-1:0]    sfence_inv_second_stage_4MB_index;
    logic [ITLB_4MBPAGE_ASSOC-1:0]          sfence_inv_second_stage_4MB_hit_by_way;

    // ----------------------------------------------------------------
    // Logic:

    // read port logic
        // arbitration b/w:
            // sfence inv
            // core req
        // use 4KB array and 4MB array together
        // core backpressure is only implicit so prioritize sfence inv
    itlb_4KB_index_hash ITLB_SFENCE_INV_4KB_INDEX_HASH (
        .VPN(sfence_inv_VPN),
        .ASID(sfence_inv_ASID),
        .index(read_port_sfence_inv_4KB_read_index)
    );
    itlb_4MB_index_hash ITLB_SFENCE_INV_4MB_INDEX_HASH (
        .VPN(sfence_inv_VPN),
        .ASID(sfence_inv_ASID),
        .index(read_port_sfence_inv_4MB_read_index)
    );
    itlb_4KB_index_hash ITLB_CORE_REQ_4KB_INDEX_HASH (
        .VPN(core_req_VPN),
        .ASID(core_req_ASID),
        .index(read_port_core_req_4KB_read_index)
    );
    itlb_4MB_index_hash ITLB_CORE_REQ_4MB_INDEX_HASH (
        .VPN(core_req_VPN),
        .ASID(core_req_ASID),
        .index(read_port_core_req_4MB_read_index)
    );
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

        end
        else begin

        end
    end
    always_comb begin
        read_port_sfence_inv_using = sfence_inv_valid;
        read_port_core_req_using = core_req_valid & ~read_port_sfence_inv_using;

        if (read_port_sfence_inv_using) begin
            array_4KB_read_index = read_port_sfence_inv_4KB_read_index;
            array_4MB_read_index = read_port_sfence_inv_4MB_read_index;
        end
        else begin
            array_4KB_read_index = read_port_core_req_4KB_read_index;
            array_4MB_read_index = read_port_core_req_4MB_read_index;
        end
    end

    // write port logic
        // arbitration b/w:
            // miss resp
            // sfence inv
        // use 4KB array and 4MB array together
        // sfence can be easily backpressured and don't want to buffer miss resp data so prioritize miss resp
    always_comb begin

    end

    // core resp mini pipeline logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

        end
        else begin

        end
    end
    always_comb begin

    end

    // miss reg logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

        end
        else begin

        end
    end
    always_comb begin

    end

    // sfence inv mini pipeline logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

        end
        else begin

        end
    end
    always_comb begin

    end

    // array logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            array_4KB_by_set_by_way <= '0;
            array_4MB_by_set_by_way <= '0;
        end
        else begin
            if (array_4KB_write_valid) begin
                array_4KB_by_set_by_way[array_4KB_write_index][array_4KB_write_way] <= array_4KB_write_data;
            end
            if (array_4MB_write_valid) begin
                array_4MB_by_set_by_way[array_4MB_write_index][array_4MB_write_way] <= array_4MB_write_data;
            end
        end
    end
    always_comb begin
        array_4KB_read_set = array_4KB_by_set_by_way[array_4KB_read_index];
        array_4MB_read_set = array_4MB_by_set_by_way[array_4MB_read_index];
    end

endmodule