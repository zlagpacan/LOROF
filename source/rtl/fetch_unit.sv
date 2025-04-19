/*
    Filename: fetch_unit.sv
    Author: zlagpacan
    Description: RTL for Fetch Unit
    Spec: LOROF/spec/design/fetch_unit.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module fetch_unit #(
    parameter INIT_PC = 32'h0,
    parameter INIT_ASID = 9'h0,
    parameter INIT_EXEC_MODE = M_MODE,
    parameter INIT_VIRTUAL_MODE = 1'b0,
    parameter INIT_WAIT_FOR_RESTART_STATE = 1'b1
) (

    // seq
    input logic CLK,
    input logic nRST,

    // itlb req
    output logic                    itlb_req_valid,
    output logic                    itlb_req_exec_mode,
    output logic                    itlb_req_virtual_mode,
    output logic [VPN_WIDTH-1:0]    itlb_req_vpn,
    output logic [ASID_WIDTH-1:0]   itlb_req_ASID,

    // itlb resp
    input logic                     itlb_resp_valid,
    input logic [PPN_WIDTH-1:0]     itlb_resp_ppn,
    input logic                     itlb_resp_page_fault,
    input logic                     itlb_resp_access_fault,

    // icache req
    output logic                                        icache_req_valid,
    output logic [ICACHE_FETCH_BLOCK_OFFSET_WIDTH-1:0]  icache_req_block_offset,
    output logic [ICACHE_INDEX_WIDTH-1:0]               icache_req_index,

    // icache resp
    input logic [1:0]                               icache_resp_valid_by_way,
    input logic [1:0][ICACHE_TAG_WIDTH-1:0]         icache_resp_tag_by_way,
    input logic [1:0][ICACHE_FETCH_WIDTH-1:0][7:0]  icache_resp_instr_16B_by_way,

    // icache resp feedback
    output logic                            icache_resp_hit_valid,
    output logic                            icache_resp_hit_way,
    output logic                            icache_resp_miss_valid,
    output logic [ICACHE_TAG_WIDTH-1:0]     icache_resp_miss_tag,

    // output to istream
    output logic                                    istream_valid_SENQ,
    output logic [7:0]                              istream_valid_by_fetch_2B_SENQ,
    output logic [7:0]                              istream_one_hot_redirect_by_fetch_2B_SENQ,
    output logic [7:0][15:0]                        istream_instr_2B_by_fetch_2B_SENQ,
    output logic [7:0][BTB_PRED_INFO_WIDTH-1:0]     istream_pred_info_by_fetch_2B_SENQ,
    output logic [7:0]                              istream_pred_lru_by_fetch_2B_SENQ,
    output logic [7:0][MDPT_INFO_WIDTH-1:0]         istream_mdp_info_by_fetch_2B_SENQ,
    output logic [31:0]                             istream_after_PC_SENQ,
    output logic [LH_LENGTH-1:0]                    istream_LH_SENQ,
    output logic [GH_LENGTH-1:0]                    istream_GH_SENQ,
    output logic [RAS_INDEX_WIDTH-1:0]              istream_ras_index_SENQ,
    output logic                                    istream_page_fault_SENQ,
    output logic                                    istream_access_fault_SENQ,

    // istream feedback
    input logic istream_stall_SENQ,

    // fetch + decode restart from ROB
    input logic         rob_restart_valid,
    input logic [31:0]  rob_restart_PC,
    input logic [8:0]   rob_restart_ASID,
    input logic [1:0]   rob_restart_exec_mode,
    input logic         rob_restart_virtual_mode,

    // decode unit control
    input logic         decode_restart_valid,
    input logic [31:0]  decode_restart_PC,
    input logic         decode_trigger_wait_for_restart,

    // branch update from decode unit
    input logic                             decode_unit_branch_update_valid,
    input logic                             decode_unit_branch_update_has_checkpoint,
    input logic                             decode_unit_branch_update_is_mispredict,
    input logic                             decode_unit_branch_update_is_taken,
    input logic                             decode_unit_branch_update_is_complex,
    input logic                             decode_unit_branch_update_use_upct,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   decode_unit_branch_update_intermediate_pred_info,
    input logic                             decode_unit_branch_update_pred_lru,
    input logic [31:0]                      decode_unit_branch_update_start_PC,
    input logic [31:0]                      decode_unit_branch_update_target_PC,
    input logic [LH_LENGTH-1:0]             decode_unit_branch_update_LH,
    input logic [GH_LENGTH-1:0]             decode_unit_branch_update_GH,
    input logic [RAS_INDEX_WIDTH-1:0]       decode_unit_branch_update_ras_index,

    // mdpt update
    input logic                         mdpt_update_valid,
    input logic [31:0]                  mdpt_update_start_full_PC,
    input logic [ASID_WIDTH-1:0]        mdpt_update_ASID,
    input logic [MDPT_INFO_WIDTH-1:0]   mdpt_update_mdp_info
);

    // ----------------------------------------------------------------
    // Signals:

    //////////////////////
    // Fetch Req Stage: //
    //////////////////////

    // state
    logic                   fetch_req_wait_for_restart_state, next_fetch_req_wait_for_restart_state;
    logic [VA_WIDTH-1:0]    fetch_req_PC_VA, next_fetch_req_PC_VA;
    logic [ASID_WIDTH-1:0]  fetch_req_ASID, next_fetch_req_ASID;
    logic [1:0]             fetch_req_exec_mode, next_fetch_req_exec_mode;
    logic                   fetch_req_virtual_mode, next_fetch_req_virtual_mode;

    // control
    logic fetch_req_valid;
    // logic fetch_req_clear; // have all info in restarts

    // interruptable access PC
    logic [VA_WIDTH-1:0]    fetch_req_access_PC_VA;

    logic use_fetch_resp_PC;
    logic use_fetch_resp_pred_PC;

    // PC arithmetic
    logic [27:0] fetch_req_PC28_plus_1;
    logic [27:0] fetch_resp_PC28_plus_1;
    logic [27:0] fetch_resp_pred_PC28_plus_1;
    logic [27:0] fetch_req_access_PC28_plus_1;

    // modules:

    // btb:

        // REQ stage
        logic                   btb_valid_REQ;
        logic [31:0]            btb_full_PC_REQ;
        logic [ASID_WIDTH-1:0]  btb_ASID_REQ;

        // RESP stage
        logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_PRED_INFO_WIDTH-1:0] btb_pred_info_by_instr_RESP;
        logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]                          btb_pred_lru_by_instr_RESP;
        logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_TARGET_WIDTH-1:0]    btb_target_by_instr_RESP;

        // Update 0
        logic                   btb_update0_valid;
        logic [31:0]            btb_update0_start_full_PC;
        logic [ASID_WIDTH-1:0]  btb_update0_ASID;

        // Update 1
        logic [BTB_PRED_INFO_WIDTH-1:0] btb_update1_pred_info;
        logic                           btb_update1_pred_lru;
        logic [31:0]                    btb_update1_target_full_PC;

    // lht:

        // REQ stage
        logic                     lht_valid_REQ;
        logic [31:0]              lht_full_PC_REQ;
        logic [ASID_WIDTH-1:0]    lht_ASID_REQ;

        // RESP stage
        logic [LHT_ENTRIES_PER_BLOCK-1:0][LH_LENGTH-1:0] lht_LH_by_instr_RESP;

        // Update 0 stage
        logic                     lht_update0_valid;
        logic [31:0]              lht_update0_start_full_PC;
        logic [ASID_WIDTH-1:0]    lht_update0_ASID;
        logic [LH_LENGTH-1:0]     lht_update0_LH;

    // mdpt:

        // REQ stage
        logic                   mdpt_valid_REQ;
        logic [31:0]            mdpt_full_PC_REQ;
        logic [ASID_WIDTH-1:0]  mdpt_ASID_REQ;

        // RESP stage
        logic [MDPT_ENTRIES_PER_BLOCK-1:0][MDPT_INFO_WIDTH-1:0] mdpt_mdp_info_by_instr_RESP;

        // MDPT Update 0 stage
        logic                           mdpt_mdpt_update0_valid;
        logic [31:0]                    mdpt_mdpt_update0_start_full_PC;
        logic [ASID_WIDTH-1:0]          mdpt_mdpt_update0_ASID;
        logic [MDPT_INFO_WIDTH-1:0]     mdpt_mdpt_update0_mdp_info;

    // itlb req:
        
        // in frontend interface

    // icache req:
    
        // in frontend interface

    ///////////////////////
    // Fetch Resp Stage: //
    ///////////////////////

    // state
    typedef enum logic [1:0] {
        FETCH_RESP_IDLE,
        FETCH_RESP_ACTIVE,
        FETCH_RESP_COMPLEX_BRANCH,
        // FETCH_RESP_ITLB_MISS, 
            // tlb misses are handled in ACTIVE and ICACHE_MISS states
            // can become TLB miss on invalidation during ICACHE_MISS
        FETCH_RESP_ICACHE_MISS
    } fetch_resp_state_t;

    fetch_resp_state_t fetch_resp_state, next_fetch_resp_state;

    // pipeline latch
    logic [VA_WIDTH-1:0]    fetch_resp_PC_VA, next_fetch_resp_PC_VA;
    logic [7:0]             fetch_resp_PC_mask;
    
    // PC arithmetic
    logic [UPPER_PC_WIDTH-1:0] fetch_resp_upper_PC_plus_saved_pred_info;
    logic [UPPER_PC_WIDTH-1:0] fetch_resp_upper_PC_plus_selected_pred_info;

    // selected index arithmetic
    logic [2:0] fetch_resp_selected_index_plus_1;

    // control
    // logic fetch_resp_clear; // have all info in restarts
    logic fetch_resp_instr_yield;
    logic fetch_resp_perform_pred_actions;

    // ghr
    logic [GH_LENGTH-1:0] ghr, next_ghr;

    // hit logic
    logic ihit;
    logic [PA_WIDTH-1:0] fetch_resp_PC_PA;
    logic [ICACHE_FETCH_WIDTH-1:0][7:0] fetch_resp_selected_instr_16B;

    // pred logic
    logic [7:0]                     fetch_resp_raw_pred_vec;
    logic [7:0]                     fetch_resp_candidate_pred_vec;
    logic                           fetch_resp_pred_present;

    logic [7:0]                     fetch_resp_selected_one_hot;
    logic [7:0]                     fetch_resp_selected_cold_ack_mask;
    logic [2:0]                     fetch_resp_selected_index;
    logic [7:0]                     fetch_resp_selected_pred_info;
    logic [BTB_TARGET_WIDTH-1:0]    fetch_resp_selected_target;
    logic [LH_LENGTH-1:0]           fetch_resp_selected_LH;

    logic [7:0]                     fetch_resp_saved_one_hot, next_fetch_resp_saved_one_hot;
    logic [7:0]                     fetch_resp_saved_cold_ack_mask, next_fetch_resp_saved_cold_ack_mask;
    logic [2:0]                     fetch_resp_saved_index, next_fetch_resp_saved_index;
    logic [7:0]                     fetch_resp_saved_pred_info, next_fetch_resp_saved_pred_info;
    logic [BTB_TARGET_WIDTH-1:0]    fetch_resp_saved_target, next_fetch_resp_saved_target;
    logic [LH_LENGTH-1:0]           fetch_resp_saved_LH, next_fetch_resp_saved_LH;

    logic [31:0] fetch_resp_pred_PC_VA;

    logic fetch_resp_check_complex_branch_taken;
    logic fetch_resp_complex_branch_taken;

    // pred actions
    logic [7:0] fetch_resp_instr_16B_yield_vec;
    logic [7:0] fetch_resp_redirect_vec;

    // modules:

    // lbpt:

        // RESP stage
        logic                   lbpt_valid_RESP;
        logic [31:0]            lbpt_full_PC_RESP;
        logic [LH_LENGTH-1:0]   lbpt_LH_RESP;
        logic [ASID_WIDTH-1:0]  lbpt_ASID_RESP;

        // RESTART stage
        logic lbpt_pred_taken_RESTART;

        // Update 0
        logic                   lbpt_update0_valid;
        logic [31:0]            lbpt_update0_start_full_PC;
        logic [LH_LENGTH-1:0]   lbpt_update0_LH;
        logic [ASID_WIDTH-1:0]  lbpt_update0_ASID;
        logic                   lbpt_update0_taken;

        // Update 1
        logic lbpt_update1_correct;

    // gbpt:

        // RESP stage
        logic                   gbpt_valid_RESP;
        logic [31:0]            gbpt_full_PC_RESP;
        logic [GH_LENGTH-1:0]   gbpt_GH_RESP;
        logic [ASID_WIDTH-1:0]  gbpt_ASID_RESP;

        // RESTART stage
        logic gbpt_pred_taken_RESTART;

        // Update 0
        logic                   gbpt_update0_valid;
        logic [31:0]            gbpt_update0_start_full_PC;
        logic [GH_LENGTH-1:0]   gbpt_update0_GH;
        logic [ASID_WIDTH-1:0]  gbpt_update0_ASID;
        logic                   gbpt_update0_taken;

        // Update 1
        logic gbpt_update1_correct;

    // upct:

        // RESP stage
        logic                           upct_valid_RESP;
        logic [LOG_UPCT_ENTRIES-1:0]    upct_upct_index_RESP;
        logic [UPPER_PC_WIDTH-1:0]      upct_upper_PC_RESP;

        // Update 0
        logic           upct_update0_valid;
        logic [31:0]    upct_update0_start_full_PC;

        // Update 1
        logic [LOG_UPCT_ENTRIES-1:0]    upct_update1_upct_index;

    // ras:

        // RESP stage
        logic           ras_link_RESP;
        logic [31:0]    ras_link_full_PC_RESP;
        logic           ras_ret_RESP;

        logic [31:0]                ras_ret_full_PC_RESP;
        logic [RAS_INDEX_WIDTH-1:0] ras_ras_index_RESP;

        // Update 0
        logic                       ras_update0_valid;
        logic [RAS_INDEX_WIDTH-1:0] ras_update0_ras_index;

    // itlb resp:

        // in frontend interface

    // icache resp:

        // in frontend interface

    /////////////////////
    // Update 0 Stage: //
    /////////////////////
        // combined with branch update from decode unit

    logic [ASID_WIDTH-1:0] update0_ASID;

    /////////////////////
    // Update 1 Stage: //
    /////////////////////

    // upct index
    // pred info
    // pred lru
    // target full pc

    logic [BTB_PRED_INFO_WIDTH-1:0]     update1_final_pred_info;
    
    // saved from update0
    logic                               update1_is_complex;
    logic                               update1_use_upct;
    logic [BTB_PRED_INFO_WIDTH-1:0]     update1_intermediate_pred_info;
    logic                               update1_pred_lru;
    logic [31:0]                        update1_target_full_PC;

    // ----------------------------------------------------------------
    // Logic:

    //////////////////////
    // Fetch Req Stage: //
    //////////////////////

    // FF logic;
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_req_PC_VA <= INIT_PC;
            fetch_req_ASID <= INIT_ASID;
            fetch_req_exec_mode <= INIT_EXEC_MODE;
            fetch_req_virtual_mode <= INIT_VIRTUAL_MODE;
            fetch_req_wait_for_restart_state <= INIT_WAIT_FOR_RESTART_STATE;
        end
        else begin
            fetch_req_PC_VA <= next_fetch_req_PC_VA;
            fetch_req_ASID <= next_fetch_req_ASID;
            fetch_req_exec_mode <= next_fetch_req_exec_mode;
            fetch_req_virtual_mode <= next_fetch_req_virtual_mode;
            fetch_req_wait_for_restart_state <= next_fetch_req_wait_for_restart_state;
        end
    end

    // next state logic:
    always_comb begin

        next_fetch_req_wait_for_restart_state = fetch_req_wait_for_restart_state;
        next_fetch_req_PC_VA = fetch_req_PC_VA;
        next_fetch_req_ASID = fetch_req_ASID;
        next_fetch_req_exec_mode = fetch_req_exec_mode;
        next_fetch_req_virtual_mode = fetch_req_virtual_mode;

        if (rob_restart_valid) begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            next_fetch_req_PC_VA = rob_restart_PC;
            next_fetch_req_ASID = rob_restart_ASID;
            next_fetch_req_exec_mode = rob_restart_exec_mode;
            next_fetch_req_virtual_mode = rob_restart_virtual_mode;
        end
        else if (decode_restart_valid) begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            next_fetch_req_PC_VA = decode_restart_PC;
        end
        else if (decode_trigger_wait_for_restart) begin
            next_fetch_req_wait_for_restart_state = 1'b1;
        end
        else if (fetch_req_wait_for_restart_state) begin
            next_fetch_req_wait_for_restart_state = 1'b1;
        end
        else begin
            next_fetch_req_wait_for_restart_state = 1'b0;
            next_fetch_req_PC_VA = {
                fetch_req_access_PC28_plus_1,
                4'b0000};
        end
    end

    // fetch req PC arithmetic
    always_comb begin
        fetch_req_PC28_plus_1 = fetch_req_PC_VA[31:4] + 28'h1;
        fetch_resp_PC28_plus_1 = fetch_resp_PC_VA[31:4] + 28'h1;
        fetch_resp_pred_PC28_plus_1 = fetch_resp_pred_PC_VA[31:4] + 28'h1;
        
        if (use_fetch_resp_PC) begin
            fetch_req_access_PC28_plus_1 = fetch_resp_PC28_plus_1;
        end
        else if (use_fetch_resp_pred_PC) begin
            fetch_req_access_PC28_plus_1 = fetch_resp_pred_PC28_plus_1;
        end
        else begin
            fetch_req_access_PC28_plus_1 = fetch_req_PC28_plus_1;
        end
    end

    // next pipeline latch
    always_comb begin
        next_fetch_resp_PC_VA = fetch_req_access_PC_VA;
    end

    // control
    always_comb begin
        fetch_req_valid = ~fetch_req_wait_for_restart_state;
    end

    // module connections:
    always_comb begin

        // btb:
        btb_valid_REQ = fetch_req_valid;
        btb_full_PC_REQ = fetch_req_access_PC_VA;
        btb_ASID_REQ = fetch_req_ASID;
        
        btb_update0_valid = decode_unit_branch_update_valid;
        btb_update0_start_full_PC = decode_unit_branch_update_start_PC;
        btb_update0_ASID = update0_ASID;

        btb_update1_pred_info = update1_final_pred_info;
        btb_update1_pred_lru = update1_pred_lru;
        btb_update1_target_full_PC = update1_target_full_PC;

        // lht:
        lht_valid_REQ = fetch_req_valid;
        lht_full_PC_REQ = fetch_req_access_PC_VA;
        lht_ASID_REQ = fetch_req_ASID;

        // check for complex branch restart value of LH
        if (
            decode_unit_branch_update_valid 
            & decode_unit_branch_update_has_checkpoint
            & decode_unit_branch_update_is_mispredict
            & decode_unit_branch_update_is_complex
        ) begin
            // shift in based on if update is T/NT
            lht_update0_valid = 1'b1;
            lht_update0_start_full_PC = decode_unit_branch_update_start_PC;
            lht_update0_ASID = update0_ASID;
            lht_update0_LH = {
                decode_unit_branch_update_LH[LH_LENGTH-2:0],
                decode_unit_branch_update_is_taken};
        end
        // check for complex branch update present
        else if (fetch_resp_check_complex_branch_taken & fetch_resp_perform_pred_actions) begin
            // shift in based on if complex branch is T/NT
            lht_update0_valid = 1'b1;
            lht_update0_start_full_PC = {fetch_resp_PC_VA[31:4], fetch_resp_saved_index, 1'b0};
            lht_update0_ASID = fetch_req_ASID;
            lht_update0_LH = {
                fetch_resp_saved_LH[LH_LENGTH-2:0],
                fetch_resp_complex_branch_taken};
        end
        // otherwise no update
        else begin
            lht_update0_valid = 1'b0;
            lht_update0_start_full_PC = {fetch_resp_PC_VA[31:4], fetch_resp_saved_index, 1'b0};
            lht_update0_ASID = fetch_req_ASID;
            lht_update0_LH = {
                fetch_resp_saved_LH[LH_LENGTH-2:0],
                fetch_resp_complex_branch_taken};
        end

        // mdpt:
        mdpt_valid_REQ = fetch_req_valid;
        mdpt_full_PC_REQ = fetch_req_access_PC_VA;
        mdpt_ASID_REQ = fetch_req_ASID;

        mdpt_mdpt_update0_valid = mdpt_update_valid;
        mdpt_mdpt_update0_start_full_PC = mdpt_update_start_full_PC;
        mdpt_mdpt_update0_ASID = mdpt_update_ASID;
        mdpt_mdpt_update0_mdp_info = mdpt_update_mdp_info;

        // itlb:
        itlb_req_valid = fetch_req_valid;
        itlb_req_exec_mode = fetch_req_exec_mode;
        itlb_req_virtual_mode = fetch_req_virtual_mode;
        itlb_req_vpn = fetch_req_access_PC_VA;
        itlb_req_ASID = fetch_req_ASID;

        // icache:
        icache_req_valid = fetch_req_valid;
        icache_req_block_offset = fetch_req_access_PC_VA[ICACHE_BLOCK_OFFSET_WIDTH]; // choose first or second 16B of 32B block
        icache_req_index = fetch_req_access_PC_VA[
            ICACHE_INDEX_WIDTH + ICACHE_BLOCK_OFFSET_WIDTH - 1 : ICACHE_BLOCK_OFFSET_WIDTH
        ];
    end

    // modules:

    btb BTB (
        .CLK(CLK),
        .nRST(nRST),
        .valid_REQ(btb_valid_REQ),
        .full_PC_REQ(btb_full_PC_REQ),
        .ASID_REQ(btb_ASID_REQ),
        .pred_info_by_instr_RESP(btb_pred_info_by_instr_RESP),
        .pred_lru_by_instr_RESP(btb_pred_lru_by_instr_RESP),
        .target_by_instr_RESP(btb_target_by_instr_RESP),
        .update0_valid(btb_update0_valid),
        .update0_start_full_PC(btb_update0_start_full_PC),
        .update0_ASID(btb_update0_ASID),
        .update1_pred_info(btb_update1_pred_info),
        .update1_pred_lru(btb_update1_pred_lru),
        .update1_target_full_PC(btb_update1_target_full_PC)
    );

    lht LHT (
        .CLK(CLK),
        .nRST(nRST),
        .valid_REQ(lht_valid_REQ),
        .full_PC_REQ(lht_full_PC_REQ),
        .ASID_REQ(lht_ASID_REQ),
        .LH_by_instr_RESP(lht_LH_by_instr_RESP),
        .update0_valid(lht_update0_valid),
        .update0_start_full_PC(lht_update0_start_full_PC),
        .update0_ASID(lht_update0_ASID),
        .update0_LH(lht_update0_LH)
    );

    mdpt MPDT (
        .CLK(CLK),
        .nRST(nRST),
        .valid_REQ(mdpt_valid_REQ),
        .full_PC_REQ(mdpt_full_PC_REQ),
        .ASID_REQ(mdpt_ASID_REQ),
        .mdp_info_by_instr_RESP(mdpt_mdp_info_by_instr_RESP),
        .mdpt_update0_valid(mdpt_mdpt_update0_valid),
        .mdpt_update0_start_full_PC(mdpt_mdpt_update0_start_full_PC),
        .mdpt_update0_ASID(mdpt_mdpt_update0_ASID),
        .mdpt_update0_mdp_info(mdpt_mdpt_update0_mdp_info)
    );

    ///////////////////////
    // Fetch Resp Stage: //
    ///////////////////////

    // FF logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_resp_state <= FETCH_RESP_IDLE;
            ghr <= '0;
        end
        else begin
            if (rob_restart_valid | decode_restart_valid) begin
                fetch_resp_state <= FETCH_RESP_IDLE;
            end
            else begin
                fetch_resp_state <= next_fetch_resp_state;
            end

            // check for complex branch restart value of GHR
            if (
                decode_unit_branch_update_valid
                & decode_unit_branch_update_has_checkpoint
                & decode_unit_branch_update_is_mispredict
                & decode_unit_branch_update_is_complex
            ) begin
                // shift in based on if update is T/NT
                ghr <= {
                    decode_unit_branch_update_GH[GH_LENGTH-2:0],
                    decode_unit_branch_update_is_taken};
            end
            // check for non-complex restart value of GHR
            else if (
                // take update pure GH
                decode_unit_branch_update_valid
                & decode_unit_branch_update_has_checkpoint
                & decode_unit_branch_update_is_mispredict
            ) begin
                ghr <= decode_unit_branch_update_GH;
            end
            // check for complex branch update present
            else if (fetch_resp_check_complex_branch_taken & fetch_resp_perform_pred_actions) begin
                // shift in based on if complex branch is T/NT
                ghr <= {
                    ghr[GH_LENGTH-2:0],
                    fetch_resp_complex_branch_taken};
            end
        end
    end

    // pipeline latch logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            fetch_resp_PC_VA <= 32'h0;
            fetch_resp_PC_mask <= 8'b11111111;

            fetch_resp_saved_one_hot <= 8'b00000000;
            fetch_resp_saved_cold_ack_mask <= 8'b11111111;
            fetch_resp_saved_index <= 3'h0;
            fetch_resp_saved_pred_info <= 8'h0;
            fetch_resp_saved_target <= '0;
            fetch_resp_saved_LH <= 8'h0;
        end
        else begin
            fetch_resp_PC_VA <= next_fetch_resp_PC_VA;

            // create PC mask
            case (next_fetch_resp_PC_VA[3:1])
                3'b000: fetch_resp_PC_mask <= 8'b11111111;
                3'b001: fetch_resp_PC_mask <= 8'b11111110;
                3'b010: fetch_resp_PC_mask <= 8'b11111100;
                3'b011: fetch_resp_PC_mask <= 8'b11111000;
                3'b100: fetch_resp_PC_mask <= 8'b11110000;
                3'b101: fetch_resp_PC_mask <= 8'b11100000;
                3'b110: fetch_resp_PC_mask <= 8'b11000000;
                3'b111: fetch_resp_PC_mask <= 8'b10000000;
            endcase

            fetch_resp_saved_one_hot <= next_fetch_resp_saved_one_hot;
            fetch_resp_saved_cold_ack_mask <= next_fetch_resp_saved_cold_ack_mask;
            fetch_resp_saved_index <= next_fetch_resp_saved_index;
            fetch_resp_saved_pred_info <= next_fetch_resp_saved_pred_info;
            fetch_resp_saved_target <= next_fetch_resp_saved_target;
            fetch_resp_saved_LH <= next_fetch_resp_saved_LH;
        end
    end

    // hit logic
    always_comb begin

        // defaults:
        ihit = 1'b0;
        fetch_resp_PC_PA = {itlb_resp_ppn, fetch_resp_PC_VA[PO_WIDTH-1:0]};
        fetch_resp_selected_instr_16B = icache_resp_instr_16B_by_way[0];

        icache_resp_hit_valid = 1'b0;
        icache_resp_hit_way = 1'b0;
        icache_resp_miss_valid = 1'b0;
        icache_resp_miss_tag = fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH];

        // TODO: optimize hit path

        // TLB hit check
        if (itlb_resp_valid) begin

            // page fault or access fault
            if (itlb_resp_page_fault | itlb_resp_access_fault) begin

                // automatic ihit
                ihit = 1'b1;
            end

            // cache hit check way 0
            if (icache_resp_valid_by_way[0] & 
                icache_resp_tag_by_way[0] == fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH]
            ) begin
                ihit = 1'b1;
                fetch_resp_selected_instr_16B = icache_resp_instr_16B_by_way[0];

                icache_resp_hit_valid = 1'b1;
                icache_resp_hit_way = 1'b0;
            end
        
            // cache hit check way 1
            else if (icache_resp_valid_by_way[1] & 
                icache_resp_tag_by_way[1] == fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH]
            ) begin
                ihit = 1'b1;
                fetch_resp_selected_instr_16B = icache_resp_instr_16B_by_way[1];

                icache_resp_hit_valid = 1'b1;
                icache_resp_hit_way = 1'b1;
            end

            // otherwise, cache miss
            else begin
                ihit = 1'b0;

                // only send cache miss on first time missing
                    // can be in ACTIVE, COMPLEX_BRANCH, or ITLB_MISS state
                icache_resp_miss_valid = fetch_resp_state != FETCH_RESP_ICACHE_MISS;
                icache_resp_miss_tag = fetch_resp_PC_PA[31:32-ICACHE_TAG_WIDTH];
            end
        end

        // otherwise, TLB miss
        else begin
            ihit = 1'b0;
        end
    end

    // pred selection logic:
    always_comb begin

        for (int i = 0; i < 8; i++) begin
            fetch_resp_raw_pred_vec[i] = 
                (
                    btb_pred_info_by_instr_RESP[i][6] 
                        // jump, ret, or complex branch
                    |
                    btb_pred_info_by_instr_RESP[i][7] & btb_pred_info_by_instr_RESP[i][5]
                        // simple branch taken
                )
                & fetch_resp_saved_cold_ack_mask[i];
            ;
        end

        fetch_resp_candidate_pred_vec = fetch_resp_raw_pred_vec & fetch_resp_PC_mask;

        fetch_resp_pred_present = |fetch_resp_candidate_pred_vec;

        // use one hot mux to quickly select out pred and target of interest
        fetch_resp_selected_pred_info = '0;
        fetch_resp_selected_target = '0;
        fetch_resp_selected_LH = '0;
        for (int i = 0; i < 8; i++) begin
            if (fetch_resp_selected_one_hot[i]) begin
                fetch_resp_selected_pred_info |= btb_pred_info_by_instr_RESP[i];
                fetch_resp_selected_target |= btb_target_by_instr_RESP[i];
                fetch_resp_selected_LH |= lht_LH_by_instr_RESP[i];
            end
        end
    end

    pe_lsb #(
        .WIDTH(8),
        .USE_ONE_HOT(1),
        .USE_COLD(1),
        .USE_INDEX(1)
    ) PRED_PE (
        .req_vec(fetch_resp_candidate_pred_vec),
        .ack_one_hot(fetch_resp_selected_one_hot),
        .cold_ack_mask(fetch_resp_selected_cold_ack_mask),
        .ack_index(fetch_resp_selected_index)
    );

    // fast pred actions
    always_comb begin

        // check use global for complex branch taken
        if (fetch_resp_saved_pred_info[5]) begin
            fetch_resp_complex_branch_taken = gbpt_pred_taken_RESTART;
        end
        // otherwise use local for complex branch taken
        else begin
            fetch_resp_complex_branch_taken = lbpt_pred_taken_RESTART;
        end

        // check for predicted complex branch
        if (fetch_resp_check_complex_branch_taken & fetch_resp_complex_branch_taken) begin
            // yield below complex branch (saved cold ack mask)
            fetch_resp_instr_16B_yield_vec = fetch_resp_PC_mask & ~fetch_resp_saved_cold_ack_mask;
            // redirect at complex branch (saved one hot)
            fetch_resp_redirect_vec = fetch_resp_saved_one_hot;
        end
        // check for simple branch or jump
        else if (fetch_resp_selected_pred_info[7] | fetch_resp_selected_pred_info[6]) begin
            // can yield up to and including branch and jump (this cold ack mask)
            fetch_resp_instr_16B_yield_vec = fetch_resp_PC_mask & ~fetch_resp_selected_cold_ack_mask;
            // redirect at this branch or jump (this one hot)
            fetch_resp_redirect_vec = fetch_resp_selected_one_hot;
        end
        // otherwise, no branches
        else begin
            // yield everything after PC
            fetch_resp_instr_16B_yield_vec = fetch_resp_PC_mask;
            fetch_resp_redirect_vec = 8'b10000000;
        end
    end

    // fetch resp PC arithmetic
    always_comb begin
        fetch_resp_upper_PC_plus_saved_pred_info = 
            fetch_resp_PC_VA[31:32-UPPER_PC_WIDTH]
            +
            {{(UPPER_PC_WIDTH-2){fetch_resp_saved_pred_info[2]}}, fetch_resp_saved_pred_info[1:0]};

        fetch_resp_upper_PC_plus_selected_pred_info = 
            fetch_resp_PC_VA[31:32-UPPER_PC_WIDTH]
            +
            {{(UPPER_PC_WIDTH-2){fetch_resp_selected_pred_info[2]}}, fetch_resp_selected_pred_info[1:0]};
    end

    // pred-specific actions
    always_comb begin
        fetch_resp_pred_PC_VA = {
            fetch_resp_upper_PC_plus_saved_pred_info, 
            fetch_resp_saved_target, 1'b0};

        upct_valid_RESP = 1'b0;
        upct_upct_index_RESP = fetch_resp_saved_pred_info[2:0]; 

        ras_link_RESP = 1'b0;
        ras_ret_RESP = 1'b0;

        // check complex branch taken
        if (fetch_resp_check_complex_branch_taken & fetch_resp_complex_branch_taken) begin
            upct_upct_index_RESP = fetch_resp_saved_pred_info[2:0];
            // bit [3] tells if use upct
            if (fetch_resp_saved_pred_info[3]) begin
                upct_valid_RESP = 1'b1;
                fetch_resp_pred_PC_VA = {
                    upct_upper_PC_RESP, 
                    fetch_resp_saved_target, 1'b0};
            end
            // otherwise, upper PC + 3bindex, target
            else begin
                fetch_resp_pred_PC_VA = {
                    fetch_resp_upper_PC_plus_saved_pred_info, 
                    fetch_resp_saved_target, 1'b0};
            end
        end
        // otherwise, other branch or don't care
        else begin
            upct_upct_index_RESP = fetch_resp_selected_pred_info[2:0];

            casez (fetch_resp_selected_pred_info[7:4])

                4'b00??: // no pred
                begin
                    // don't care
                end

                4'b0100: // J
                begin
                    // bit [3] tells if use upct
                    if (fetch_resp_saved_pred_info[3]) begin
                        upct_valid_RESP = 1'b1;
                        fetch_resp_pred_PC_VA = {
                            upct_upper_PC_RESP, 
                            fetch_resp_saved_target, 1'b0};
                    end
                    // otherwise, upper PC + 3bindex, target
                    else begin
                        fetch_resp_pred_PC_VA = {
                            fetch_resp_upper_PC_plus_selected_pred_info, 
                            fetch_resp_saved_target, 1'b0};
                    end
                end

                4'b0101: // JAL PC+2
                begin
                    // bit [3] tells if use upct
                    if (fetch_resp_saved_pred_info[3]) begin
                        upct_valid_RESP = 1'b1;
                        fetch_resp_pred_PC_VA = {
                            upct_upper_PC_RESP, 
                            fetch_resp_saved_target, 1'b0};
                    end
                    // otherwise, upper PC + 3bindex, target
                    else begin
                        fetch_resp_pred_PC_VA = {
                            fetch_resp_upper_PC_plus_selected_pred_info, 
                            fetch_resp_saved_target, 1'b0};
                    end

                    // link
                    if (fetch_resp_perform_pred_actions) begin
                        ras_link_RESP = 1'b1;
                    end
                end

                4'b0110: // RET
                begin
                    // take directly from ras
                    fetch_resp_pred_PC_VA = ras_ret_full_PC_RESP;
                end

                4'b0111: // RETL PC+2
                begin
                    // take directly from ras
                    fetch_resp_pred_PC_VA = ras_ret_full_PC_RESP;

                    // link
                    if (fetch_resp_perform_pred_actions) begin
                        ras_link_RESP = 1'b1;
                    end
                end

                4'b10??: // simple branch
                begin
                    // just treat as taken, not taken will not be selected
                    fetch_resp_pred_PC_VA = {
                        fetch_resp_PC_VA[31:32-UPPER_PC_WIDTH], 
                        fetch_resp_selected_target, 1'b0};
                end

                4'b11??: // complex branch
                begin
                    // don't care
                end

            endcase
        end
    end

    // state machine + control + interruptable access PC
    always_comb begin

        fetch_req_access_PC_VA = fetch_req_PC_VA;
        use_fetch_resp_PC = 1'b0;
        use_fetch_resp_pred_PC = 1'b0;
            // interrupt on istream stall
            // interrupt on branch prediction
            // interrupt on itlb or icache miss

        next_fetch_resp_state = fetch_resp_state;

        // reset cold ack mask
        next_fetch_resp_saved_cold_ack_mask = '1;
        // keep saving pred info
        next_fetch_resp_saved_one_hot = fetch_resp_saved_one_hot;
        next_fetch_resp_saved_index = fetch_resp_saved_index;
        next_fetch_resp_saved_pred_info = fetch_resp_saved_pred_info;
        next_fetch_resp_saved_target = fetch_resp_saved_target;
        next_fetch_resp_saved_LH = fetch_resp_saved_LH;

        fetch_resp_check_complex_branch_taken = 1'b0;

        fetch_resp_instr_yield = 1'b0;
        fetch_resp_perform_pred_actions = 1'b0;

        // state machine:
            // restarts are taken care of in FF logic
        case (fetch_resp_state)

            FETCH_RESP_IDLE:
            begin
                // only go into active when fetch req not in wait for restart state
                if (fetch_req_valid) begin
                    next_fetch_resp_state = FETCH_RESP_ACTIVE;
                end
            end

            FETCH_RESP_ACTIVE:
            begin
                // check miss
                if (~ihit) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                    use_fetch_resp_PC = 1'b1;

                    // check itlb miss -> stay here
                    if (~itlb_resp_valid) begin
                        next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    end
                    // otherwise, icache miss
                    else begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                end
                // check istream stall with icache hit
                else if (istream_stall_SENQ) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                    use_fetch_resp_PC = 1'b1;
                end
                // otherwise, clean icache hit
                else begin

                    // can perform pred actions
                    fetch_resp_perform_pred_actions = 1'b1;

                    // check for pred
                    if (fetch_resp_pred_present) begin

                        // check for complex branch
                        if (fetch_resp_selected_pred_info[7:6] == 2'b11) begin

                            // redo current fetch resp access in fetch req
                            fetch_req_access_PC_VA = fetch_resp_PC_VA;
                            use_fetch_resp_PC = 1'b1;

                            // will get complex branch info next cycle
                            next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;

                            // save complex branch state
                            next_fetch_resp_saved_one_hot = fetch_resp_selected_one_hot;
                            next_fetch_resp_saved_cold_ack_mask = fetch_resp_selected_cold_ack_mask;
                            next_fetch_resp_saved_index = fetch_resp_selected_index;
                            next_fetch_resp_saved_pred_info = fetch_resp_selected_pred_info;
                            next_fetch_resp_saved_target = fetch_resp_selected_target;
                            next_fetch_resp_saved_LH = fetch_resp_selected_LH;

                            // no instr yields yet
                            fetch_resp_instr_yield = 1'b0;
                        end

                        // otherwise, branch or jump
                        else begin

                            // use predicted fetch resp access in fetch req
                            fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;
                            use_fetch_resp_pred_PC = 1'b1;

                            // yield instr's
                            fetch_resp_instr_yield = 1'b1;
                        end
                    end
                    // otherwise, simple move on
                    else begin

                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;
                    end
                end
            end

            FETCH_RESP_COMPLEX_BRANCH:
            begin
                // check for complex branch taken
                fetch_resp_check_complex_branch_taken = 1'b1;

                // check miss
                if (~ihit) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                    use_fetch_resp_PC = 1'b1;

                    // check itlb miss -> stay here
                    if (~itlb_resp_valid) begin
                    
                        // hold all complex branch state state
                        next_fetch_resp_saved_one_hot = fetch_resp_saved_one_hot;
                        next_fetch_resp_saved_cold_ack_mask = fetch_resp_saved_cold_ack_mask;
                        next_fetch_resp_saved_index = fetch_resp_saved_index;
                        next_fetch_resp_saved_pred_info = fetch_resp_saved_pred_info;
                        next_fetch_resp_saved_target = fetch_resp_saved_target;
                        next_fetch_resp_saved_LH = fetch_resp_saved_LH;

                        next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;
                    end
                    // otherwise, icache miss
                    else begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                end
                // if istream_stall_SENQ, hold all complex branch state
                else if (istream_stall_SENQ) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                    use_fetch_resp_PC = 1'b1;
                    
                    // hold all complex branch state
                    next_fetch_resp_saved_one_hot = fetch_resp_saved_one_hot;
                    next_fetch_resp_saved_cold_ack_mask = fetch_resp_saved_cold_ack_mask;
                    next_fetch_resp_saved_index = fetch_resp_saved_index;
                    next_fetch_resp_saved_pred_info = fetch_resp_saved_pred_info;
                    next_fetch_resp_saved_target = fetch_resp_saved_target;
                    next_fetch_resp_saved_LH = fetch_resp_saved_LH;
                end
                // if hit, continue using complex branch state
                else begin

                    // can perform pred actions
                    fetch_resp_perform_pred_actions = 1'b1;
                    
                    // check this complex branch taken
                    if (fetch_resp_complex_branch_taken) begin

                        // use predicted fetch resp access in fetch req
                        fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;
                        use_fetch_resp_pred_PC = 1'b1;
                    
                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;

                        // back to active
                        next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    end
                    // else check for other pred
                    else if (fetch_resp_pred_present) begin

                        // check for complex branch
                        if (fetch_resp_selected_pred_info[7:6] == 2'b11) begin

                            // redo current fetch resp access in fetch req
                            fetch_req_access_PC_VA = fetch_resp_PC_VA;
                            use_fetch_resp_PC = 1'b1;

                            // will get complex branch info next cycle
                            next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;

                            // save complex branch state
                            next_fetch_resp_saved_one_hot = fetch_resp_selected_one_hot;
                            next_fetch_resp_saved_cold_ack_mask = fetch_resp_selected_cold_ack_mask;
                            next_fetch_resp_saved_index = fetch_resp_selected_index;
                            next_fetch_resp_saved_pred_info = fetch_resp_selected_pred_info;
                            next_fetch_resp_saved_target = fetch_resp_selected_target;
                            next_fetch_resp_saved_LH = fetch_resp_selected_LH;

                            // no instr yields yet
                            fetch_resp_instr_yield = 1'b0;
                        end

                        // otherwise, branch or jump
                        else begin

                            // use predicted fetch resp access in fetch req
                            fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;
                            use_fetch_resp_pred_PC = 1'b1;

                            // yield instr's
                            fetch_resp_instr_yield = 1'b1;

                            // back to active
                            next_fetch_resp_state = FETCH_RESP_ACTIVE;
                        end
                    end
                    // otherwise, simple move on
                    else begin

                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;

                        // back to active
                        next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    end
                end
            end

            FETCH_RESP_ICACHE_MISS:
            begin
                // check miss
                if (~ihit) begin
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                    use_fetch_resp_PC = 1'b1;

                    // check itlb miss -> stay here
                    if (~itlb_resp_valid) begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                    // otherwise, icache miss
                    else begin
                        next_fetch_resp_state = FETCH_RESP_ICACHE_MISS;
                    end
                end
                // check istream stall with icache hit
                else if (istream_stall_SENQ) begin

                    // back to ACTIVE
                    next_fetch_resp_state = FETCH_RESP_ACTIVE;
                    
                    // redo current fetch resp access in fetch req
                    fetch_req_access_PC_VA = fetch_resp_PC_VA;
                    use_fetch_resp_PC = 1'b1;
                end
                // otherwise, clean icache hit
                else begin

                    // back to ACTIVE
                    next_fetch_resp_state = FETCH_RESP_ACTIVE;

                    // can perform pred actions
                    fetch_resp_perform_pred_actions = 1'b1;

                    // check for pred
                    if (fetch_resp_pred_present) begin

                        // check for complex branch
                        if (fetch_resp_selected_pred_info[7:6] == 2'b11) begin

                            // redo current fetch resp access in fetch req
                            fetch_req_access_PC_VA = fetch_resp_PC_VA;
                            use_fetch_resp_PC = 1'b1;

                            // will get complex branch info next cycle
                            next_fetch_resp_state = FETCH_RESP_COMPLEX_BRANCH;

                            // save complex branch state
                            next_fetch_resp_saved_one_hot = fetch_resp_selected_one_hot;
                            next_fetch_resp_saved_cold_ack_mask = fetch_resp_selected_cold_ack_mask;
                            next_fetch_resp_saved_index = fetch_resp_selected_index;
                            next_fetch_resp_saved_pred_info = fetch_resp_selected_pred_info;
                            next_fetch_resp_saved_target = fetch_resp_selected_target;
                            next_fetch_resp_saved_LH = fetch_resp_selected_LH;

                            // no instr yields yet
                            fetch_resp_instr_yield = 1'b0;
                        end

                        // otherwise, branch or jump
                        else begin

                            // use predicted fetch resp access in fetch req
                            fetch_req_access_PC_VA = fetch_resp_pred_PC_VA;
                            use_fetch_resp_pred_PC = 1'b1;

                            // yield instr's
                            fetch_resp_instr_yield = 1'b1;
                        end
                    end
                    // otherwise, simple move on
                    else begin

                        // yield instr's
                        fetch_resp_instr_yield = 1'b1;
                    end
                end
            end

        endcase
    end

    // selected index arithmetic
    always_comb begin

        fetch_resp_selected_index_plus_1 = fetch_resp_selected_index + 3'h1;
    end

    // module connections:
    always_comb begin

        // lbpt:
        lbpt_valid_RESP = fetch_resp_selected_pred_info[7:6] == 2'b11;
        lbpt_full_PC_RESP = {fetch_resp_PC_VA[31:4], fetch_resp_selected_index, 1'b0};
        lbpt_LH_RESP = fetch_resp_selected_LH;
        lbpt_ASID_RESP = fetch_req_ASID;

        lbpt_update0_valid = 
            decode_unit_branch_update_valid 
            & decode_unit_branch_update_has_checkpoint
            & decode_unit_branch_update_is_complex;
        lbpt_update0_start_full_PC = decode_unit_branch_update_start_PC;
        lbpt_update0_LH = decode_unit_branch_update_LH;
        lbpt_update0_ASID = update0_ASID;
        lbpt_update0_taken = decode_unit_branch_update_is_taken;

        // gbpt:
        gbpt_valid_RESP = fetch_resp_selected_pred_info[7:6] == 2'b11;
        gbpt_full_PC_RESP = {fetch_resp_PC_VA[31:4], fetch_resp_selected_index, 1'b0};;
        gbpt_GH_RESP = ghr;
        gbpt_ASID_RESP = fetch_req_ASID;
        
        gbpt_update0_valid = 
            decode_unit_branch_update_valid 
            & decode_unit_branch_update_has_checkpoint
            & decode_unit_branch_update_is_complex;
        gbpt_update0_start_full_PC = decode_unit_branch_update_start_PC;
        gbpt_update0_GH = decode_unit_branch_update_GH;
        gbpt_update0_ASID = update0_ASID;
        gbpt_update0_taken = decode_unit_branch_update_is_taken;

        // upct:
        // upct_valid_RESP = ; // handled in pred-specific actions
        // upct_upct_index_RESP = ; // handled in pred-specific actions
        
        upct_update0_valid = 
            decode_unit_branch_update_valid
            & decode_unit_branch_update_use_upct;
        upct_update0_start_full_PC = decode_unit_branch_update_start_PC;

        // ras:
        // ras_link_RESP = ; // handled in pred-specific actions
        if (fetch_resp_selected_one_hot[7]) begin
            // use PC+16 if link on last instr in this 16B
            ras_link_full_PC_RESP = {fetch_req_PC_VA, fetch_resp_selected_index_plus_1, 1'b0};
        end
        else begin
            // use next instr PC link
            ras_link_full_PC_RESP = {fetch_resp_PC_VA, fetch_resp_selected_index_plus_1, 1'b0};
        end
        // ras_ret_RESP = ; // handled in pred-specific actions

        ras_update0_valid = 
            decode_unit_branch_update_valid
            & decode_unit_branch_update_has_checkpoint;
        ras_update0_ras_index = decode_unit_branch_update_ras_index;
    end

    // modules:

    lbpt LBPT (
        .CLK(CLK),
        .nRST(nRST),
        .valid_RESP(lbpt_valid_RESP),
        .full_PC_RESP(lbpt_full_PC_RESP),
        .LH_RESP(lbpt_LH_RESP),
        .ASID_RESP(lbpt_ASID_RESP),
        .pred_taken_RESTART(lbpt_pred_taken_RESTART),
        .update0_valid(lbpt_update0_valid),
        .update0_start_full_PC(lbpt_update0_start_full_PC),
        .update0_LH(lbpt_update0_LH),
        .update0_ASID(lbpt_update0_ASID),
        .update0_taken(lbpt_update0_taken),
        .update1_correct(lbpt_update1_correct)
    );

    gbpt GPBT (
        .CLK(CLK),
        .nRST(nRST),
        .valid_RESP(gbpt_valid_RESP),
        .full_PC_RESP(gbpt_full_PC_RESP),
        .GH_RESP(gbpt_GH_RESP),
        .ASID_RESP(gbpt_ASID_RESP),
        .pred_taken_RESTART(gbpt_pred_taken_RESTART),
        .update0_valid(gbpt_update0_valid),
        .update0_start_full_PC(gbpt_update0_start_full_PC),
        .update0_GH(gbpt_update0_GH),
        .update0_ASID(gbpt_update0_ASID),
        .update0_taken(gbpt_update0_taken),
        .update1_correct(gbpt_update1_correct)
    );

    upct UPCT (
        .CLK(CLK),
        .nRST(nRST),
        .valid_RESP(upct_valid_RESP),
        .upct_index_RESP(upct_upct_index_RESP),
        .upper_PC_RESP(upct_upper_PC_RESP),
        .update0_valid(upct_update0_valid),
        .update0_start_full_PC(upct_update0_start_full_PC),
        .update1_upct_index(upct_update1_upct_index)
    );

    ras RAS (
        .CLK(CLK),
        .nRST(nRST),
        .link_RESP(ras_link_RESP),
        .link_full_PC_RESP(ras_link_full_PC_RESP),
        .ret_RESP(ras_ret_RESP),
        .ret_full_PC_RESP(ras_ret_full_PC_RESP),
        .ras_index_RESP(ras_ras_index_RESP),
        .update0_valid(ras_update0_valid),
        .update0_ras_index(ras_update0_ras_index)
    );

    ///////////////////////
    // Stream EnQ Stage: //
    ///////////////////////

    always_comb begin

        istream_valid_SENQ = fetch_resp_instr_yield;
        istream_valid_by_fetch_2B_SENQ = fetch_resp_instr_16B_yield_vec;
        istream_one_hot_redirect_by_fetch_2B_SENQ = fetch_resp_redirect_vec;
        istream_instr_2B_by_fetch_2B_SENQ = fetch_resp_selected_instr_16B;
        istream_pred_info_by_fetch_2B_SENQ = btb_pred_info_by_instr_RESP;
        istream_pred_lru_by_fetch_2B_SENQ = btb_pred_lru_by_instr_RESP;
        istream_mdp_info_by_fetch_2B_SENQ = mdpt_mdp_info_by_instr_RESP;
        istream_after_PC_SENQ = fetch_req_access_PC_VA;
        istream_LH_SENQ = fetch_resp_saved_LH;
        istream_GH_SENQ = ghr;
        istream_ras_index_SENQ = ras_ras_index_RESP;
        istream_page_fault_SENQ = itlb_resp_page_fault;
        istream_access_fault_SENQ = itlb_resp_access_fault;
    end

    /////////////////////
    // Update 0 Stage: //
    /////////////////////

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            update0_ASID <= INIT_ASID;
        end
        else begin
            if (rob_restart_valid) begin
                update0_ASID <= rob_restart_ASID;
            end
        end
    end

    /////////////////////
    // Update 1 Stage: //
    /////////////////////

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            update1_is_complex <= 1'b0;
            update1_use_upct <= 1'b0;
            update1_intermediate_pred_info <= 8'h0;
            update1_pred_lru <= 1'b0;
            update1_target_full_PC <= 32'h0;
        end
        else begin
            update1_is_complex <= decode_unit_branch_update_is_complex;
            update1_use_upct <= decode_unit_branch_update_use_upct;
            update1_intermediate_pred_info <= decode_unit_branch_update_intermediate_pred_info;
            update1_pred_lru <= decode_unit_branch_update_pred_lru;
            update1_target_full_PC <= decode_unit_branch_update_target_PC;
        end
    end

    always_comb begin
        update1_final_pred_info = update1_intermediate_pred_info;

        // check for complex branch 2bc increment/decrement using gbpt, lbpt correctness feedback in update1
        if (update1_is_complex) begin

            case (update1_intermediate_pred_info[5:4])

                2'b00:
                begin
                    // increment
                    if (gbpt_update1_correct & ~lbpt_update1_correct) begin
                        update1_final_pred_info[5:4] = 2'b01;
                    end
                end

                2'b01:
                begin
                    // increment
                    if (gbpt_update1_correct & ~lbpt_update1_correct) begin
                        update1_final_pred_info[5:4] = 2'b10;
                    end

                    // decrement
                    if (~gbpt_update1_correct & lbpt_update1_correct) begin
                        update1_final_pred_info[5:4] = 2'b00;
                    end
                end

                2'b10:
                begin
                    // increment
                    if (gbpt_update1_correct & ~lbpt_update1_correct) begin
                        update1_final_pred_info[5:4] = 2'b11;
                    end

                    // decrement
                    if (~gbpt_update1_correct & lbpt_update1_correct) begin
                        update1_final_pred_info[5:4] = 2'b01;
                    end
                end

                2'b11:
                begin
                    // decrement
                    if (~gbpt_update1_correct & lbpt_update1_correct) begin
                        update1_final_pred_info[5:4] = 2'b10;
                    end
                end
            endcase
        end

        // use upct's index generated in update1
        if (update1_use_upct) begin
            update1_final_pred_info[2:0] = upct_update1_upct_index;
        end
    end

endmodule