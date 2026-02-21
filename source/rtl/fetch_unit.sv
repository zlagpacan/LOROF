/*
    Filename: fetch_unit.sv
    Author: zlagpacan
    Description: RTL for Fetch Unit
    Spec: LOROF/spec/design/fetch_unit.md
*/

// TODO: RV64GC, Sv39 changes
// TODO: fast redirect
    // pipelined pc_gen which resolves details quickly if can else defer to third stage
    // can quickly redirect by only needing BTB_big_target or ras TOS
    // fast vs. slow redirect for upct case depends on if BTB_small_target is big enough to build REQ index
    // pipeline: REQ, RESP, LATE
        // REQ:
            // btb, pht, mdpt req
            // itlb, icache req
        // RESP:
            // btb, pht, mdpt resp
            // itlb, icache resp
            // ras read/write
            // btb hit check
            // yield PC index bits if fast redirect
            // fast redirect -> REQ
        // LATE:
            // ibtb lookup
            // yield full pc
            // slow redirect -> REQ
        // RESP2:
            // upct
            // yield full pc after fast redirect w/ small target + upct
// TODO: prediction <-> fetch interaction
    // idea: index Q + tag Q
        // probably want to rename something like index Q + tag Q
        // can asynchronously and non-lock-step enQ index and tag for given wide fetch access as info comes
        // this naturally decouples prediction pipeline and fetch pipeline so easier control:
            // simple individual pipeline control
            // simple interface
        // loss is Q size
        // index yield
            // RESP no redirect to REQ -> pc38 + 8
            // RESP fast redirect to REQ -> fast redirect pc index bits
            // LATE slow redirect to REQ -> full pc bits
        // tag yield
            // RESP fast redirect
            // LATE slow redirect
    // idea: prediction and fetch directly coupled
        // was overthinking how tough the FSM would be ^ for index yield but no tag yield
            // both pipelines would stall in this case anyway
            // no benefit from 1-cycle early index lookup as miss req's aren't initiated until have tag
                // it could even be worse as have 1-cycle stale data
// TODO: blocking itlb interface for simplicity
    // stall read resp stage if no itlb hit
    // always know if icache hit and send miss in read resp stage

`include "corep.vh"
`include "sysp.vh"

module fetch_unit (

    // seq
    input logic CLK,
    input logic nRST,

    // itlb req
    output logic                itlb_req_valid,
    output corep::asid_t        itlb_req_asid,
    output corep::exec_mode_t   itlb_req_exec_mode,
    output logic                itlb_req_virtual_mode,
    output corep::fetch_idx_t   itlb_req_fetch_idx,

    // itlb resp
    output sysp::vpn_t          itlb_resp_vpn,

    input logic                 itlb_resp_valid,
    input sysp::ppn_t           itlb_resp_ppn,
    input logic                 itlb_resp_page_fault,
    input logic                 itlb_resp_access_fault,

    // icache req
    output logic                                            icache_req_valid,
    output corep::fetch_idx_t                               icache_req_fetch_idx,

    // icache resp
    input logic                 [sysp::ICACHE_ASSOC-1:0]    icache_resp_valid_by_way,
    input sysp::icache_tag_t    [sysp::ICACHE_ASSOC-1:0]    icache_resp_tag_by_way,
    input corep::fetch16B_t     [sysp::ICACHE_ASSOC-1:0]    icache_resp_fetch16B_by_way,

    // icache feedback hit
    output logic                icache_feedback_hit_valid,
    output sysp::icache_way_t   icache_feedback_hit_way,

    // icache feedback miss
    output logic                icache_feedback_miss_valid,
    output corep::fmid_t        icache_feedback_miss_fmid,
    output sysp::pa39_t         icache_feedback_miss_pa39,

    input logic                 icache_feedback_miss_ready,

    // icache miss return
    input logic                 icache_miss_return_valid,
    input corep::fmid_t         icache_miss_return_fmid,
    input corep::fetch16B_t     icache_miss_return_fetch16B,

    // instr yield
    output logic                        instr_yield_valid,
    output corep::instr_yield_t [3:0]   instr_yield_by_way,

    // instr yield feedback
    input logic                         instr_yield_ready,

    // wfr trigger from rob
    input logic rob_trigger_wfr,

    // restart from ROB (non-branch restarts)
    input logic                 rob_restart_valid,
    input corep::bcb_idx_t      rob_restart_bcb_idx,
    input corep::pc38_t         rob_restart_pc38,
    input corep::asid_t         rob_restart_asid,
    input corep::exec_mode_t    rob_restart_exec_mode,
    input logic                 rob_restart_virtual_mode,

    // wfr trigger from decode_unit
    input logic decode_unit_trigger_wfr,

    // restart from decode_unit (due to erroneous btb hit -> also implies clearing update to btb)
    input logic             decode_unit_restart_valid,
    input corep::bcb_idx_t  decode_unit_restart_bcb_idx,
    input corep::pc38_t     decode_unit_restart_pc38,

    // branch update (and also restart if mispred)
    input logic                 branch_update_valid,
    input logic                 branch_update_mispred,
    input corep::bcb_idx_t      branch_update_bcb_idx,
    input corep::pc38_t         branch_update_src_pc38,
    input corep::asid_t         branch_update_asid,
    input corep::btb_info_t     branch_update_btb_info,
    input corep::pc38_t         branch_update_tgt_pc38,
    input logic                 branch_update_taken,
    input logic                 branch_update_btb_hit,

    output logic                branch_update_ready,

    // mdpt update
    input logic             mdpt_update_valid,
    input corep::pc38_t     mdpt_update_pc38,
    input corep::asid_t     mdpt_update_asid,
    input corep::mdp_t      mdpt_update_mdp
);

    // ----------------------------------------------------------------
    // Signals:

    ////////////////////
    // misc. control: //
    ////////////////////

    // any restart (helpful for not forgetting cases for latches) 
    logic any_restart;

    // wait for restart
    logic wfr;

    // fetch arch state
    corep::asid_t       fetch_arch_asid;
    corep::exec_mode_t  fetch_arch_exec_mode;
    logic               fetch_arch_virtual_mode;

    ////////////////
    // REQ stage: //
    ////////////////

    logic REQ_valid;
    logic REQ_pass;

    corep::pc38_t           REQ_latched_pc38;
    corep::pc38_t           REQ_received_pc38;

    corep::gh_t         REQ_latched_gh;
    corep::gh_t         REQ_received_gh;

    /////////////////
    // RESP stage: //
    /////////////////

    logic RESP_valid;

    logic RESP_pass;

    logic RESP_icache_hit;

    corep::pc38_t       RESP_received_pc38;
    corep::pc38_t       RESP_received_pc38_next_8;
    sysp::icache_tag_t  RESP_received_icache_tag;

    corep::gh_t RESP_received_gh;

    logic RESP_redirect;
    logic RESP_redirect_no_double_hit_not_taken;

    logic [corep::FETCH_LANES-1:0] RESP_valid_by_lane;

    //////////////////
    // RESP2 stage: //
    //////////////////

    logic RESP2_valid;

    corep::pc38_t RESP2_src_pc38;

    corep::pc38_t RESP2_tgt_pc38;

    ///////////////////
    // update stage: //
    ///////////////////

    corep::btb_info_t   update_final_btb_info;

    corep::gh_t         restart_final_gh;
    corep::pc38_t       restart_final_pc38;

    /////////////
    // pc mux: //
    /////////////

    // REQ_received_pc38.upc.msbs
    logic [6:0] REQ_received_pc38_upc_msbs_one_hot;

    // REQ_received_pc38.upc.big_tgt_msbs
    logic [8:0] REQ_received_pc38_upc_big_tgt_msbs_one_hot;

    // REQ_received_pc38.idx
    logic [6:0] REQ_received_pc38_idx_one_hot;

    // REQ_received_pc38.lane
    logic [6:0] REQ_received_pc38_lane_one_hot;

    // REQ_received_gh
    logic [3:0] REQ_received_gh_one_hot;

    ////////////////
    // module IO: //
    ////////////////

    // upct IO:

    // read in
    logic               upct_read_valid;
    corep::upct_idx_t   upct_read_idx_way0;
    corep::upct_idx_t   upct_read_idx_way1;
    corep::upct_idx_t   upct_read_idx_touch;
    // read out
    corep::upc_t [1:0]  upct_read_upc_by_way;
    // update in
    logic               upct_update_valid;
    corep::upc_t        upct_update_upc;
    // update out
    corep::upct_idx_t   upct_update_upct_idx;

    // ras IO:

    // pc_gen link control
    logic               ras_link_valid;
    corep::pc38_t       ras_link_pc38;
    // pc_gen return control
    logic               ras_ret_valid;
    logic               ras_ret_fallback;
    corep::pc38_t       ras_ret_pc38;
    corep::ras_idx_t    ras_ret_ras_idx;
    corep::ras_cnt_t    ras_ret_ras_cnt;
    // update control
    logic               ras_update_valid;
    corep::ras_idx_t    ras_update_ras_idx;
    corep::ras_cnt_t    ras_update_ras_cnt;

    // btb IO:

    // read req stage
    logic                       btb_read_req_valid;
    corep::fetch_idx_t          btb_read_req_fetch_idx;
    corep::asid_t               btb_read_req_asid;
    // read resp stage
    corep::pc38_t               btb_read_resp_pc38;
    logic                       btb_read_resp_hit;
    logic                       btb_read_resp_double_hit;
    corep::btb_way_t            btb_read_resp_hit_way;
    corep::fetch_lane_t [1:0]   btb_read_resp_hit_lane_by_way;
    corep::btb_info_t [1:0]     btb_read_resp_btb_info_by_way;
    // update
    logic                       btb_update_valid;
    corep::pc38_t               btb_update_pc38;
    corep::asid_t               btb_update_asid;
    corep::btb_info_t           btb_update_btb_info;
    logic                       btb_update_hit;
    corep::btb_way_t            btb_update_hit_way;

    // pht IO:

    // read req stage
    logic                   pht_read_req_valid;
    corep::fetch_idx_t      pht_read_req_fetch_idx;
    corep::gh_t             pht_read_req_gh;
    corep::asid_t           pht_read_req_asid;
    // read resp stage
    corep::fetch_lane_t     pht_read_resp_redirect_lane_way0;
    corep::fetch_lane_t     pht_read_resp_redirect_lane_way1;
    logic [1:0]             pht_read_resp_taken_by_way;
    // update
    logic                   pht_update_valid;
    corep::pc38_t           pht_update_pc38;
    corep::gh_t             pht_update_gh;
    corep::asid_t           pht_update_asid;
    logic                   pht_update_taken;

    // ibtb IO:

    // read
    corep::pc38_t       ibtb_read_src_pc38;
    corep::ibtb_gh_t    ibtb_read_ibtb_gh;
    corep::asid_t       ibtb_read_asid;
    corep::pc38_t       ibtb_read_tgt_pc38;
    // update
    logic               ibtb_update_valid;
    corep::pc38_t       ibtb_update_src_pc38;
    corep::pc38_t       ibtb_update_ibtb_gh;
    corep::asid_t       ibtb_update_asid;
    corep::pc38_t       ibtb_update_tgt_pc38;

    // mdpt IO:

    // read req stage
    logic               mdpt_read_req_valid;
    corep::fetch_idx_t  mdpt_read_req_fetch_idx;
    corep::asid_t       mdpt_read_req_asid;
    // read resp stage
    corep::mdpt_set_t   mdpt_read_resp_mdp_by_lane;
    // // update
    // logic               mdpt_update_valid;
    // corep::pc38_t       mdpt_update_pc38;
    // corep::asid_t       mdpt_update_asid;
    // corep::mdp_t        mdpt_update_mdp;
        // in fetch_unit IO

    // bcb IO:

    // save control
    logic               bcb_save_valid;
    corep::bcb_info_t   bcb_save_bcb_info;
    corep::bcb_idx_t    bcb_save_bcb_idx;
    // restore control
    corep::bcb_idx_t    bcb_restore_bcb_idx;
    corep::bcb_info_t   bcb_restore_bcb_info;

    // ibuffer IO:

    // enq
    logic                       ibuffer_enq_valid;
    corep::ibuffer_enq_info_t   ibuffer_enq_info;
    logic                       ibuffer_enq_fetch_hit_valid;
    corep::fetch16B_t           ibuffer_enq_fetch_hit_fetch16B;
    // enq feedback
    logic                       ibuffer_enq_ready;
    corep::fmid_t               ibuffer_enq_fmid;
    // // fetch miss return
    // logic                       ibuffer_fetch_miss_return_valid;
    // corep::fmid_t               ibuffer_fetch_miss_return_fmid;
    // corep::fetch16B_t           ibuffer_fetch_miss_return_fetch16B;
    // // deq
    // logic                       ibuffer_instr_yield_valid;
    // corep::instr_yield_t [3:0]  ibuffer_instr_yield_by_way;
    // // def feedback
    // logic                       ibuffer_instr_yield_ready;
        // in fetch_unit IO
    // restart
    logic                       ibuffer_restart_valid;

    // ----------------------------------------------------------------
    // Logic:
    
    // misc. state logic
    always_comb begin
        any_restart =
            rob_restart_valid
            | decode_unit_restart_valid
            | (branch_update_valid & branch_update_ready & branch_update_mispred)
        ;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            wfr <= 1'b1;

            fetch_arch_asid <= corep::INIT_ASID;
            fetch_arch_exec_mode <= corep::INIT_EXEC_MODE;
            fetch_arch_virtual_mode <= corep::INIT_VIRTUAL_MODE;
        end
        else begin
            // prioritize restarts
            if (any_restart) begin
                wfr <= 1'b0;
            end
            // otherwise, can enter wfr
            else if (rob_trigger_wfr | decode_unit_trigger_wfr) begin
                wfr <= 1'b1;
            end

            if (rob_restart_valid) begin
                fetch_arch_asid <= rob_restart_asid;
                fetch_arch_exec_mode <= rob_restart_exec_mode;
                fetch_arch_virtual_mode <= rob_restart_virtual_mode;
            end
        end
    end

    // REQ logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            REQ_latched_pc38 <= corep::INIT_PC38;
            REQ_latched_gh <= corep::INIT_GH;
        end
        else if (any_restart) begin
            REQ_latched_pc38 <= restart_final_pc38;
            REQ_latched_gh <= restart_final_gh;
        end
    end
    always_comb begin
        REQ_valid = ~wfr;
        REQ_pass = (~RESP_valid | RESP_pass);
    end

    // RESP logic
        // also info pass back to REQ
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            RESP_valid <= 1'b0;
            RESP_received_pc38 <= 38'h0;
            RESP_received_gh <= '0;
        end
        else if (~RESP_valid | RESP_pass) begin
            RESP_valid <= REQ_valid;
            RESP_received_pc38 <= REQ_received_pc38;
            RESP_received_gh <= REQ_received_gh;
        end
    end
    always_comb begin
        {RESP_received_pc38_next_8.upc, RESP_received_pc38_next_8.idx} = {RESP_received_pc38.upc, RESP_received_pc38.idx} + 35'h1;
        RESP_received_pc38_next_8.lane = 3'h0;

        RESP_received_icache_tag = sysp::icache_tag_from_pc38(RESP_received_pc38);
    end
    // // TODO: delete
    // always_comb begin
    //     // build REQ pc38 based on btb way
    //     for (int way = 0; way < corep::BTB_ASSOC; way++) begin

    //         // default: RESP empty, use all REQ latched
    //         REQ_received_pc38_by_way[way] = REQ_latched_pc38;

    //         REQ_received_gh_by_way[way] = REQ_latched_gh;

    //         RESP_redirect_by_way[way] = 1'b0;
    //         RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b0;

    //         // default: non-btb-hit dependent pass requirements (can be further disabled later in logic)
    //             // itlb hit
    //         RESP_pass_by_way[way] =
    //             itlb_resp_valid
    //             & (RESP_icache_hit | icache_feedback_miss_ready)
    //             & ibuffer_enq_ready
    //         ;

    //         // default: no double hit
    //         potential_double_hit_by_way[way] = 1'b0;

    //         // btb action cases
    //         case (btb_read_resp_btb_info_by_way[way].action)
    //             corep::BTB_ACTION_NONE: begin
    //                 REQ_received_pc38_by_way[way] = RESP_received_pc38_next_8;
                    
    //                 REQ_received_gh_by_way[way] = RESP_received_gh;

    //                 RESP_redirect_by_way[way] = 1'b0;
    //                 RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b0;
    //             end
    //             corep::BTB_ACTION_BRANCH: begin
    //                 // taken
    //                 if (pht_read_resp_taken_by_way[way]) begin
    //                     if (btb_read_resp_btb_info_by_way[way].use_upct) begin
    //                         REQ_received_pc38_by_way[way].upc = upct_read_upc_by_way[way];
    //                     end
    //                     else begin
    //                         REQ_received_pc38_by_way[way].upc.msbs = RESP_received_pc38.upc.msbs;
    //                         REQ_received_pc38_by_way[way].upc.big_tgt_msbs = btb_read_resp_btb_info_by_way[way].big_tgt.upct_idx;
    //                     end
    //                     REQ_received_pc38_by_way[way].idx = btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.idx;
    //                     REQ_received_pc38_by_way[way].lane = btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.lane;

    //                     REQ_received_gh_by_way[way] = {RESP_received_gh << 1, 1'b1};

    //                     RESP_redirect_by_way[way] = 1'b1;
    //                     RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b1;
    //                 end
    //                 // otherwise, not taken
    //                 else begin
    //                     // move onto next 16B, double hit possible
    //                     REQ_received_pc38_by_way[way] = RESP_received_pc38_next_8;
                        
    //                     REQ_received_gh_by_way[way] = {RESP_received_gh << 1, 1'b0};

    //                     RESP_redirect_by_way[way] = 1'b0;
    //                     RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b0;
                        
    //                     potential_double_hit_by_way[way] = 1'b1;
    //                 end
    //             end
    //             corep::BTB_ACTION_JUMP, corep::BTB_ACTION_JUMP_L: begin
    //                 // do big_tgt behavior by default, use_upct determines if only accept small_tgt bits
    //                 if (btb_read_resp_btb_info_by_way[way].use_upct) begin
    //                     REQ_received_pc38_by_way[way].upc = upct_read_upc_by_way[way];
    //                 end
    //                 else begin
    //                     REQ_received_pc38_by_way[way].upc.msbs = RESP_received_pc38.upc.msbs;
    //                     REQ_received_pc38_by_way[way].upc.big_tgt_msbs = btb_read_resp_btb_info_by_way[way].big_tgt.upct_idx;
    //                 end
    //                 REQ_received_pc38_by_way[way].idx = btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.idx;
    //                 REQ_received_pc38_by_way[way].lane = btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.lane;

    //                 REQ_received_gh_by_way[way] = RESP_received_gh;

    //                 RESP_redirect_by_way[way] = 1'b1;
    //                 RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b1;
    //             end
    //             corep::BTB_ACTION_RET, corep::BTB_ACTION_RET_L: begin
    //                 // take from ras
    //                 REQ_received_pc38_by_way[way] = ras_ret_pc38;
                    
    //                 REQ_received_gh_by_way[way] = RESP_received_gh;

    //                 RESP_redirect_by_way[way] = 1'b1;
    //                 RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b1;
    //             end
    //             corep::BTB_ACTION_INDIRECT, corep::BTB_ACTION_INDIRECT_L: begin
    //                 // take from ibtb
    //                 REQ_received_pc38_by_way[way] = RESP2_tgt_pc38;
                    
    //                 REQ_received_gh_by_way[way] = RESP_received_gh;

    //                 RESP_redirect_by_way[way] = 1'b1;
    //                 RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b1;

    //                 if (~RESP2_valid) begin
    //                     RESP_pass_by_way[way] = 1'b0;
    //                 end
    //             end
    //             default: begin // default is BTB_ACTION_NONE
    //                 REQ_received_pc38_by_way[way] = RESP_received_pc38_next_8;
                    
    //                 REQ_received_gh_by_way[way] = RESP_received_gh;

    //                 RESP_redirect_by_way[way] = 1'b0;
    //                 RESP_redirect_no_double_hit_not_taken_by_way[way] = 1'b0;
    //             end
    //         endcase
    //     end
    // end
    // always_comb begin
    //     // build double hit pc38 based on btb way
    //     for (int way = 0; way < corep::BTB_ASSOC; way++) begin
    //         // re-yield after not taken branch 
    //         if (btb_read_resp_hit_lane_by_way[way] == 3'h7) begin
    //             double_hit_REQ_received_pc38_by_way[way] = RESP_received_pc38_next_8;
    //             // possible for lane 7 double branch
    //                 // this is aliasing case, but at least can yield if correctly guess not taken like this
    //         end
    //         else begin
    //             double_hit_REQ_received_pc38_by_way[way].upc = RESP_received_pc38.upc;
    //             double_hit_REQ_received_pc38_by_way[way].idx = RESP_received_pc38.idx;
    //             double_hit_REQ_received_pc38_by_way[way].lane = btb_read_resp_hit_lane_by_way[way] + 3'h1;
    //         end
    //     end
    // end
    // always_comb begin
    //     if (RESP_valid) begin
    //         if (btb_read_resp_hit) begin
    //             // check for double hit, where use built double hit pc38
    //             if (btb_read_resp_double_hit & potential_double_hit_by_way[btb_read_resp_hit_way]) begin
    //                 REQ_received_pc38 = double_hit_REQ_received_pc38_by_way[btb_read_resp_hit_way];
            
    //                 REQ_received_gh = {RESP_received_gh << 1, 1'b0};

    //                 RESP_redirect = 1'b1;
    //                 RESP_redirect_no_double_hit_not_taken = 1'b0;
    //             end
    //             // otherwise, use regular built pc38 by way
    //             else begin
    //                 REQ_received_pc38 = REQ_received_pc38_by_way[btb_read_resp_hit_way];

    //                 REQ_received_gh = REQ_received_gh_by_way[btb_read_resp_hit_way];

    //                 RESP_redirect = RESP_redirect_by_way[btb_read_resp_hit_way];
    //                 RESP_redirect_no_double_hit_not_taken = RESP_redirect_no_double_hit_not_taken_by_way[btb_read_resp_hit_way];
    //             end
    //         end
    //         // otherwise, no action
    //         else begin
    //             REQ_received_pc38 = RESP_received_pc38_next_8;
                
    //             REQ_received_gh = RESP_received_gh;

    //             RESP_redirect = 1'b0;
    //             RESP_redirect_no_double_hit_not_taken = 1'b0;
    //         end
    //     end
    //     // otherwise, stick with latched pc38 and gh
    //     else begin
    //         REQ_received_pc38 = REQ_latched_pc38;

    //         REQ_received_gh = REQ_latched_gh;

    //         RESP_redirect = 1'b0;
    //         RESP_redirect_no_double_hit_not_taken = 1'b0;
    //     end

    //     // simple selection of by btb way for pass's and valid's
    //     RESP_pass = RESP_pass_by_way[btb_read_resp_hit_way];

    //     RESP_valid_by_lane = RESP_valid_by_lane_by_way[btb_read_resp_hit_way];
    // end
    // always_comb begin
    //     for (int way = 0; way < corep::BTB_ASSOC; way++) begin
    //         for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin
    //             RESP_valid_by_lane_by_way[way][lane] =
    //                 (lane >= RESP_received_pc38.lane)
    //                 & (~RESP_redirect_by_way[way] | (lane <= btb_read_resp_hit_lane_by_way[way]))
    //             ;
    //         end
    //     end
    // end
    // always_comb begin
    //     selected_btb_read_resp_btb_info = btb_read_resp_btb_info_by_way[btb_read_resp_hit_way];
    // end
    //     // TODO: forgot ras fallback ^

    // one-hot PC mux:

        // REQ_received_pc38 possibilities:
            // REQ_latched_pc38
            // RESP_received_pc38_next_8
            // {upct_read_upc_by_way[way], btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.idx, btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.lane}
            // {RESP_received_pc38.upc.msbs, btb_read_resp_btb_info_by_way[way].big_tgt.upct_idx, btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.idx, btb_read_resp_btb_info_by_way[way].big_tgt.small_tgt.lane}
            // ras_ret_pc38
            // RESP2_tgt_pc38
            // {RESP_received_pc38.upc, RESP_received_pc38.idx, btb_read_resp_hit_lane_by_way[way] + 3'h1}

        // REQ_received_pc38.upc.msbs
            // REQ_latched_pc38.upc.msbs
            // RESP_received_pc38_next_8.upc.msbs
            // upct_read_upc_by_way[0].msbs
            // upct_read_upc_by_way[1].msbs
            // RESP_received_pc38.upc.msbs
            // ras_ret_pc38.upc.msbs
            // RESP2_tgt_pc38.upc.msbs

        // REQ_received_pc38.upc.big_tgt_msbs
            // REQ_latched_pc38.upc.big_tgt_msbs
            // RESP_received_pc38_next_8.upc.big_tgt_msbs
            // upct_read_upc_by_way[0].big_tgt_msbs
            // upct_read_upc_by_way[1].big_tgt_msbs
            // btb_read_resp_btb_info_by_way[0].big_tgt.upct_idx
            // btb_read_resp_btb_info_by_way[1].big_tgt.upct_idx
            // ras_ret_pc38.upc.big_tgt_msbs
            // RESP2_tgt_pc38.upc.big_tgt_msbs
            // RESP_received_pc38.upc.big_tgt_msbs

        // REQ_received_pc38.idx
            // REQ_latched_pc38.idx
            // RESP_received_pc38_next_8.idx
            // btb_read_resp_btb_info_by_way[0].big_tgt.small_tgt.idx
            // btb_read_resp_btb_info_by_way[1].big_tgt.small_tgt.idx
            // ras_ret_pc38.idx
            // RESP2_tgt_pc38.idx
            // RESP_received_pc38.idx
            
        // REQ_received_pc38.lane
            // REQ_latched_pc38.lane
            // 3'b000 -> skip case
            // btb_read_resp_btb_info_by_way[0].big_tgt.small_tgt.lane
            // btb_read_resp_btb_info_by_way[1].big_tgt.small_tgt.lane
            // ras_ret_pc38.lane
            // RESP2_tgt_pc38.lane
            // btb_read_resp_hit_lane_by_way[0] + 3'h1
            // btb_read_resp_hit_lane_by_way[1] + 3'h1

    // REQ_received_pc38.upc.msbs
    always_comb begin
        // REQ_latched_pc38.upc.msbs
        REQ_received_pc38_upc_msbs_one_hot[6] =
            ~RESP_valid
        ;
        // RESP_received_pc38_next_8.upc.msbs
        REQ_received_pc38_upc_msbs_one_hot[5] =
            RESP_valid & (
                ~btb_read_resp_hit
                | (btb_read_resp_hit & (
                    ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0] & (
                        ~btb_read_resp_double_hit
                        | btb_read_resp_double_hit & (btb_read_resp_hit_lane_by_way[0] == 3'h7)
                    )
                    | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1] & (
                        ~btb_read_resp_double_hit
                        | btb_read_resp_double_hit & (btb_read_resp_hit_lane_by_way[1] == 3'h7)
                    )
                ))
            )
        ;
        // upct_read_upc_by_way[0].msbs
        REQ_received_pc38_upc_msbs_one_hot[4] =
            RESP_valid & btb_read_resp_hit & ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].use_upct & (
                btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_btb_info_by_way[0].action.jump
                | btb_read_resp_btb_info_by_way[0].action.ret & ras_ret_fallback
            )
        ;
        // upct_read_upc_by_way[1].msbs
        REQ_received_pc38_upc_msbs_one_hot[3] =
            RESP_valid & btb_read_resp_hit & btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].use_upct & (
                btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                | btb_read_resp_btb_info_by_way[1].action.jump
                | btb_read_resp_btb_info_by_way[1].action.ret & ras_ret_fallback
            )
        ;
        // RESP_received_pc38.upc.msbs
        REQ_received_pc38_upc_msbs_one_hot[2] =
            RESP_valid & (
                btb_read_resp_hit & ~btb_read_resp_hit_way & ~btb_read_resp_btb_info_by_way[0].use_upct & (
                    btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                    | btb_read_resp_btb_info_by_way[0].action.jump
                    | btb_read_resp_btb_info_by_way[0].action.ret & ras_ret_fallback
                )
                | btb_read_resp_hit & btb_read_resp_hit_way & ~btb_read_resp_btb_info_by_way[1].use_upct & (
                    btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                    | btb_read_resp_btb_info_by_way[1].action.jump
                    | btb_read_resp_btb_info_by_way[1].action.ret & ras_ret_fallback
                )
                | btb_read_resp_double_hit & (
                    ~btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[0] != 3'h7) & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0]
                    | btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[1] != 3'h7) & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1]
                )
            )
        ;
        // ras_ret_pc38.upc.msbs
        REQ_received_pc38_upc_msbs_one_hot[1] =
            RESP_valid & btb_read_resp_hit & ~ras_ret_fallback & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ret
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ret
            )
        ;
        // RESP2_tgt_pc38.upc.msbs
        REQ_received_pc38_upc_msbs_one_hot[0] =
            RESP_valid & btb_read_resp_hit & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ibtb
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ibtb
            )
        ;
    end
    mux_one_hot #(
        .COUNT(7),
        .WIDTH($bits(REQ_received_pc38.upc.msbs))
    ) REQ_RECEIVED_PC38_UPC_MSBS_ONE_HOT_MUX (
        .sel_one_hot(REQ_received_pc38_upc_msbs_one_hot),
        .data_by_requestor({
            REQ_latched_pc38.upc.msbs,
            RESP_received_pc38_next_8.upc.msbs,
            upct_read_upc_by_way[0].msbs,
            upct_read_upc_by_way[1].msbs,
            RESP_received_pc38.upc.msbs,
            ras_ret_pc38.upc.msbs,
            RESP2_tgt_pc38.upc.msbs
        }),
        .selected_data(REQ_received_pc38.upc.msbs)
    );

    // REQ_received_pc38.upc.big_tgt_msbs
    always_comb begin
        // REQ_latched_pc38.upc.big_tgt_msbs
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[8] =
            ~RESP_valid
        ;
        // RESP_received_pc38_next_8.upc.big_tgt_msbs
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[7] =
            RESP_valid & (
                ~btb_read_resp_hit
                | (btb_read_resp_hit & (
                    ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0] & (
                        ~btb_read_resp_double_hit
                        | btb_read_resp_double_hit & (btb_read_resp_hit_lane_by_way[0] == 3'h7)
                    )
                    | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1] & (
                        ~btb_read_resp_double_hit
                        | btb_read_resp_double_hit & (btb_read_resp_hit_lane_by_way[1] == 3'h7)
                    )
                ))
            )
        ;
        // upct_read_upc_by_way[0].big_tgt_msbs
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[6] =
            RESP_valid & btb_read_resp_hit & ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].use_upct & (
                btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_btb_info_by_way[0].action.jump
                | btb_read_resp_btb_info_by_way[0].action.ret & ras_ret_fallback
            )
        ;
        // upct_read_upc_by_way[1].big_tgt_msbs
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[5] =
            RESP_valid & btb_read_resp_hit & btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].use_upct & (
                btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                | btb_read_resp_btb_info_by_way[1].action.jump
                | btb_read_resp_btb_info_by_way[1].action.ret & ras_ret_fallback
            )
        ;
        // btb_read_resp_btb_info_by_way[0].big_tgt.upct_idx
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[4] =
            RESP_valid & btb_read_resp_hit & ~btb_read_resp_hit_way & ~btb_read_resp_btb_info_by_way[0].use_upct & (
                btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_btb_info_by_way[0].action.jump
                | btb_read_resp_btb_info_by_way[0].action.ret & ras_ret_fallback
            )
        ;
        // btb_read_resp_btb_info_by_way[1].big_tgt.upct_idx
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[3] =
            RESP_valid & btb_read_resp_hit & btb_read_resp_hit_way & ~btb_read_resp_btb_info_by_way[1].use_upct & (
                btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                | btb_read_resp_btb_info_by_way[1].action.jump
                | btb_read_resp_btb_info_by_way[1].action.ret & ras_ret_fallback
            )
        ;
        // ras_ret_pc38.upc.big_tgt_msbs
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[2] =
            RESP_valid & btb_read_resp_hit & ~ras_ret_fallback & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ret
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ret
            )
        ;
        // RESP2_tgt_pc38.upc.big_tgt_msbs
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[1] =
            RESP_valid & btb_read_resp_hit & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ibtb
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ibtb
            )
        ;
        // RESP_received_pc38.upc.big_tgt_msbs
        REQ_received_pc38_upc_big_tgt_msbs_one_hot[0] =
            RESP_valid & btb_read_resp_double_hit & (
                ~btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[0] != 3'h7) & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0]
                | btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[1] != 3'h7) & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1]
            )
        ;
    end
    mux_one_hot #(
        .COUNT(9),
        .WIDTH($bits(REQ_received_pc38.upc.big_tgt_msbs))
    ) REQ_RECEIVED_PC38_UPC_BIG_TGT_MSBS_ONE_HOT_MUX (
        .sel_one_hot(REQ_received_pc38_upc_big_tgt_msbs_one_hot),
        .data_by_requestor({
            REQ_latched_pc38.upc.big_tgt_msbs,
            RESP_received_pc38_next_8.upc.big_tgt_msbs,
            upct_read_upc_by_way[0].big_tgt_msbs,
            upct_read_upc_by_way[1].big_tgt_msbs,
            btb_read_resp_btb_info_by_way[0].big_tgt.upct_idx,
            btb_read_resp_btb_info_by_way[1].big_tgt.upct_idx,
            ras_ret_pc38.upc.big_tgt_msbs,
            RESP2_tgt_pc38.upc.big_tgt_msbs,
            RESP_received_pc38.upc.big_tgt_msbs
        }),
        .selected_data(REQ_received_pc38.upc.big_tgt_msbs)
    );

    // REQ_received_pc38.idx
    always_comb begin
        // REQ_latched_pc38.idx
        REQ_received_pc38_idx_one_hot[6] =
            ~RESP_valid
        ;
        // RESP_received_pc38_next_8.idx
        REQ_received_pc38_idx_one_hot[5] =
            RESP_valid & (
                ~btb_read_resp_hit
                | (btb_read_resp_hit & (
                    ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0] & (
                        ~btb_read_resp_double_hit
                        | btb_read_resp_double_hit & (btb_read_resp_hit_lane_by_way[0] == 3'h7)
                    )
                    | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1] & (
                        ~btb_read_resp_double_hit
                        | btb_read_resp_double_hit & (btb_read_resp_hit_lane_by_way[1] == 3'h7)
                    )
                ))
            )
        ;
        // btb_read_resp_btb_info_by_way[0].big_tgt.small_tgt.idx
        REQ_received_pc38_idx_one_hot[4] =
            RESP_valid & btb_read_resp_hit & ~btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_btb_info_by_way[0].action.jump
                | btb_read_resp_btb_info_by_way[0].action.ret & ras_ret_fallback
            )
        ;
        // btb_read_resp_btb_info_by_way[1].big_tgt.small_tgt.idx
        REQ_received_pc38_idx_one_hot[3] =
            RESP_valid & btb_read_resp_hit & btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                | btb_read_resp_btb_info_by_way[1].action.jump
                | btb_read_resp_btb_info_by_way[1].action.ret & ras_ret_fallback
            )
        ;
        // ras_ret_pc38.idx
        REQ_received_pc38_idx_one_hot[2] =
            RESP_valid & btb_read_resp_hit & ~ras_ret_fallback & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ret
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ret
            )
        ;
        // RESP2_tgt_pc38.idx
        REQ_received_pc38_idx_one_hot[1] =
            RESP_valid & btb_read_resp_hit & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ibtb
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ibtb
            )
        ;
        // RESP_received_pc38.idx
        REQ_received_pc38_idx_one_hot[0] =
            RESP_valid & btb_read_resp_double_hit & (
                ~btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[0] != 3'h7) & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0]
                | btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[1] != 3'h7) & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1]
            )
        ;
    end
    mux_one_hot #(
        .COUNT(7),
        .WIDTH($bits(REQ_received_pc38.idx))
    ) REQ_RECEIVED_PC38_IDX_ONE_HOT_MUX (
        .sel_one_hot(REQ_received_pc38_idx_one_hot),
        .data_by_requestor({
            REQ_latched_pc38.idx,
            // 3'b000 -> skip case
            RESP_received_pc38_next_8.idx,
            btb_read_resp_btb_info_by_way[0].big_tgt.small_tgt.idx,
            btb_read_resp_btb_info_by_way[1].big_tgt.small_tgt.idx,
            ras_ret_pc38.idx,
            RESP2_tgt_pc38.idx,
            RESP_received_pc38.idx
        }),
        .selected_data(REQ_received_pc38.idx)
    );

    // REQ_received_pc38.lane
    always_comb begin
        // REQ_latched_pc38.lane
        REQ_received_pc38_lane_one_hot[6] =
            ~RESP_valid
        ;
        // 3'b000 -> skip case
        // btb_read_resp_btb_info_by_way[0].big_tgt.small_tgt.lane
        REQ_received_pc38_lane_one_hot[5] =
            RESP_valid & btb_read_resp_hit & ~btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_btb_info_by_way[0].action.jump
                | btb_read_resp_btb_info_by_way[0].action.ret & ras_ret_fallback
            )
        ;
        // btb_read_resp_btb_info_by_way[1].big_tgt.small_tgt.lane
        REQ_received_pc38_lane_one_hot[4] =
            RESP_valid & btb_read_resp_hit & btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                | btb_read_resp_btb_info_by_way[1].action.jump
                | btb_read_resp_btb_info_by_way[1].action.ret & ras_ret_fallback
            )
        ;
        // ras_ret_pc38.lane
        REQ_received_pc38_lane_one_hot[3] =
            RESP_valid & btb_read_resp_hit & ~ras_ret_fallback & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ret
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ret
            )
        ;
        // RESP2_tgt_pc38.lane
        REQ_received_pc38_lane_one_hot[2] =
            RESP_valid & btb_read_resp_hit & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ibtb
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ibtb
            )
        ;
        // btb_read_resp_hit_lane_by_way[0] + 3'h1
        REQ_received_pc38_lane_one_hot[1] =
            RESP_valid & btb_read_resp_double_hit & ~btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[0] != 3'h7) & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0]
        ;
        // btb_read_resp_hit_lane_by_way[1] + 3'h1
        REQ_received_pc38_lane_one_hot[0] =
            RESP_valid & btb_read_resp_double_hit & btb_read_resp_hit_way & (btb_read_resp_hit_lane_by_way[1] != 3'h7) & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1]
        ;
    end
    mux_one_hot #(
        .COUNT(7),
        .WIDTH($bits(REQ_received_pc38.lane))
    ) REQ_RECEIVED_PC38_LANE_ONE_HOT_MUX (
        .sel_one_hot(REQ_received_pc38_lane_one_hot),
        .data_by_requestor({
            REQ_latched_pc38.lane,
            btb_read_resp_btb_info_by_way[0].big_tgt.small_tgt.lane,
            btb_read_resp_btb_info_by_way[1].big_tgt.small_tgt.lane,
            ras_ret_pc38.lane,
            RESP2_tgt_pc38.lane,
            btb_read_resp_hit_lane_by_way[0] + 3'h1,
            btb_read_resp_hit_lane_by_way[1] + 3'h1
        }),
        .selected_data(REQ_received_pc38.lane)
    );

    // one-hot GH mux
    always_comb begin
        // REQ_latched_gh
        REQ_received_gh_one_hot[3] =
            ~RESP_valid
        ;
        // RESP_received_gh
        REQ_received_gh_one_hot[2] =
            RESP_valid & (
                ~btb_read_resp_hit
                | ~btb_read_resp_hit_way & ~btb_read_resp_btb_info_by_way[0].action.branch
                | btb_read_resp_hit_way & ~btb_read_resp_btb_info_by_way[1].action.branch
            )
        ;
        // {RESP_received_gh << 1, 1'b1}
        REQ_received_gh_one_hot[1] =
            RESP_valid & btb_read_resp_hit & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
            )
        ;
        // {RESP_received_gh << 1, 1'b0}
        REQ_received_gh_one_hot[0] =
            RESP_valid & btb_read_resp_hit & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.branch & ~pht_read_resp_taken_by_way[0]
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.branch & ~pht_read_resp_taken_by_way[1]
            )
        ;
    end
    mux_one_hot #(
        .COUNT(4),
        .WIDTH($bits(REQ_received_gh))
    ) REQ_RECEIVED_GH_ONE_HOT_MUX (
        .sel_one_hot(REQ_received_gh_one_hot),
        .data_by_requestor({
            REQ_latched_gh,
            RESP_received_gh,
            {RESP_received_gh << 1, 1'b1},
            {RESP_received_gh << 1, 1'b0}
        }),
        .selected_data(REQ_received_gh)
    );

    // binary selects
    always_comb begin
        RESP_redirect =
            RESP_valid & btb_read_resp_hit & ~btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_btb_info_by_way[0].action.jump
                | btb_read_resp_btb_info_by_way[0].action.ret
                | btb_read_resp_btb_info_by_way[0].action.ibtb
            )
            | RESP_valid & btb_read_resp_hit & btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                | btb_read_resp_btb_info_by_way[1].action.jump
                | btb_read_resp_btb_info_by_way[1].action.ret
                | btb_read_resp_btb_info_by_way[1].action.ibtb
            )
        ;
        // no difference vs. RESP_redirect right now
        RESP_redirect_no_double_hit_not_taken =
            RESP_valid & btb_read_resp_hit & ~btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[0].action.branch & pht_read_resp_taken_by_way[0]
                | btb_read_resp_btb_info_by_way[0].action.jump
                | btb_read_resp_btb_info_by_way[0].action.ret
                | btb_read_resp_btb_info_by_way[0].action.ibtb
            )
            | RESP_valid & btb_read_resp_hit & btb_read_resp_hit_way & (
                btb_read_resp_btb_info_by_way[1].action.branch & pht_read_resp_taken_by_way[1]
                | btb_read_resp_btb_info_by_way[1].action.jump
                | btb_read_resp_btb_info_by_way[1].action.ret
                | btb_read_resp_btb_info_by_way[1].action.ibtb
            )
        ;

        RESP_pass =
            itlb_resp_valid
            & (RESP_icache_hit | icache_feedback_miss_ready)
            & ibuffer_enq_ready
            & ~(
                btb_read_resp_hit & ~RESP2_valid & (
                    ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ibtb
                    | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ibtb
                )
            )
        ;

        for (int lane = 0; lane < corep::FETCH_LANES; lane++) begin
            RESP_valid_by_lane[lane] =
                (lane >= RESP_received_pc38.lane)
                & (
                    ~RESP_redirect 
                    | (
                        ~btb_read_resp_hit_way & (lane <= btb_read_resp_hit_lane_by_way[0])
                        | btb_read_resp_hit_way & (lane <= btb_read_resp_hit_lane_by_way[1])
                    )
                )
            ;
        end
    end

    // RESP2 logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            RESP2_valid <= 1'b0;
            RESP2_src_pc38 <= 0;
        end
        else begin
            RESP2_valid <= RESP_valid & ~RESP_pass;
            RESP2_src_pc38.upc <= RESP_received_pc38.upc;
            RESP2_src_pc38.idx <= RESP_received_pc38.idx;
            RESP2_src_pc38.lane <= btb_read_resp_hit_lane_by_way[btb_read_resp_hit_way];
        end
    end
    always_comb begin
        RESP2_tgt_pc38 = ibtb_read_tgt_pc38;
    end

    // update logic
    always_comb begin
        update_final_btb_info = branch_update_btb_info;
        if (branch_update_btb_info.use_upct) begin
            update_final_btb_info.big_tgt.upct_idx = upct_update_upct_idx;
        end

        restart_final_gh = bcb_restore_bcb_info.gh;
        if (
            ~rob_restart_valid
            & branch_update_valid
            & branch_update_ready
            & branch_update_mispred
            & branch_update_btb_info.action.branch
        ) begin
            restart_final_gh = {bcb_restore_bcb_info.gh << 1, branch_update_taken};
        end

        if (rob_restart_valid) begin
            restart_final_pc38 = rob_restart_pc38; 
        end
        else if (decode_unit_restart_valid) begin
            restart_final_pc38 = decode_unit_restart_pc38;
        end
        else begin
            restart_final_pc38 = branch_update_tgt_pc38;
        end
    end

    // itlb req:
    always_comb begin
        itlb_req_valid = REQ_valid & REQ_pass;
        itlb_req_asid = fetch_arch_asid;
        itlb_req_exec_mode = fetch_arch_exec_mode;
        itlb_req_virtual_mode = fetch_arch_virtual_mode;
        itlb_req_fetch_idx = REQ_received_pc38.idx;
    end

    // itlb resp:
    always_comb begin
        itlb_resp_vpn = RESP_received_pc38[38-1:sysp::PO_WIDTH-1];
    end

    // icache req:
    always_comb begin
        icache_req_valid = REQ_valid & REQ_pass;
        icache_req_fetch_idx = REQ_received_pc38.idx;
    end

    // icache resp feedback:
    always_comb begin
        RESP_icache_hit = 1'b0;
        icache_feedback_hit_way = 0;
        // prioritize lowest way
        for (int way = sysp::ICACHE_ASSOC-1; way >= 0; way--) begin
            if (icache_resp_valid_by_way[way] & (icache_resp_tag_by_way[way] == RESP_received_icache_tag)) begin
                RESP_icache_hit = 1'b1;
                icache_feedback_hit_way = way;
            end
        end
        icache_feedback_hit_valid = RESP_icache_hit & RESP_valid & RESP_pass;

        icache_feedback_miss_valid = ~RESP_icache_hit & RESP_valid & RESP_pass;
        icache_feedback_miss_fmid = ibuffer_enq_fmid;
        icache_feedback_miss_pa39 = {RESP_received_pc38, 1'b0};
    end

    // upct:
    always_comb begin
        upct_read_valid = RESP_valid & RESP_pass;
        upct_read_idx_way0 = btb_read_resp_btb_info_by_way[0].big_tgt.upct_idx;
        upct_read_idx_way1 = btb_read_resp_btb_info_by_way[1].big_tgt.upct_idx;
        upct_read_idx_touch = btb_read_resp_hit_way ? upct_read_idx_way1 : upct_read_idx_way0;

        upct_update_valid = branch_update_valid & branch_update_ready & branch_update_btb_info.use_upct;
        upct_update_upc = branch_update_tgt_pc38.upc;
    end
    upct UPCT (
        .CLK(CLK),
        .nRST(nRST),
        .read_valid(upct_read_valid),
        .read_idx_way0(upct_read_idx_way0),
        .read_idx_way1(upct_read_idx_way1),
        .read_idx_touch(upct_read_idx_touch),
        .read_upc_way0(upct_read_upc_by_way[0]),
        .read_upc_way1(upct_read_upc_by_way[1]),
        .update_valid(upct_update_valid),
        .update_upc(upct_update_upc),
        .update_upct_idx(upct_update_upct_idx)
    );

    // ras:
    always_comb begin
        ras_link_valid =
            RESP_valid
            & RESP_pass
            & btb_read_resp_hit
            & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.link
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.link
            )
        ;
        if (btb_read_resp_hit_way) begin
            if (btb_read_resp_hit_lane_by_way[1] == 3'h7) begin
                ras_link_pc38 = RESP_received_pc38_next_8;
            end
            else begin
                ras_link_pc38.upc = RESP_received_pc38.upc;
                ras_link_pc38.idx = RESP_received_pc38.idx;
                ras_link_pc38.lane = btb_read_resp_hit_lane_by_way[1] + 3'h1;
            end
        end
        else begin
            if (btb_read_resp_hit_lane_by_way[0] == 3'h7) begin
                ras_link_pc38 = RESP_received_pc38_next_8;
            end
            else begin
                ras_link_pc38.upc = RESP_received_pc38.upc;
                ras_link_pc38.idx = RESP_received_pc38.idx;
                ras_link_pc38.lane = btb_read_resp_hit_lane_by_way[0] + 3'h1;
            end
        end

        ras_ret_valid =
            RESP_valid
            & RESP_pass
            & btb_read_resp_hit
            & (
                ~btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[0].action.ret
                | btb_read_resp_hit_way & btb_read_resp_btb_info_by_way[1].action.ret
            )
            & ~ras_ret_fallback
        ;
        
        ras_update_valid = any_restart;
        ras_update_ras_idx = bcb_restore_bcb_info.ras_idx;
        ras_update_ras_cnt = bcb_restore_bcb_info.ras_cnt;
    end
    ras RAS (
        .CLK(CLK),
        .nRST(nRST),
        .link_valid(ras_link_valid),
        .link_pc38(ras_link_pc38),
        .ret_valid(ras_ret_valid),
        .ret_fallback(ras_ret_fallback),
        .ret_pc38(ras_ret_pc38),
        .ret_ras_idx(ras_ret_ras_idx),
        .ret_ras_cnt(ras_ret_ras_cnt),
        .update_valid(ras_update_valid),
        .update_ras_idx(ras_update_ras_idx),
        .update_ras_cnt(ras_update_ras_cnt)
    );

    // btb:
    always_comb begin
        btb_read_req_valid = REQ_valid & REQ_pass;
        btb_read_req_fetch_idx = REQ_received_pc38.idx;
        btb_read_req_asid = fetch_arch_asid;

        btb_read_resp_pc38 = RESP_received_pc38;
        
        btb_update_valid = decode_unit_restart_valid | branch_update_valid;
        if (decode_unit_restart_valid) begin
            btb_update_pc38 = decode_unit_restart_pc38;
            btb_update_asid = fetch_arch_asid; // can guarantee decode_unit and fetch_unit are on same asid since last restart
            btb_update_btb_info = '0; // clear entry
            btb_update_hit = 1'b1; // this forces clearing of correct entry but plru is unfortunately reversed
            btb_update_hit_way = bcb_restore_bcb_info.btb_hit_way; // can be incorrect if rob_restart same cycle

            branch_update_ready = 1'b0;
        end else begin
            btb_update_pc38 = branch_update_src_pc38;
            btb_update_asid = branch_update_asid;
            btb_update_btb_info = update_final_btb_info;
            btb_update_hit = branch_update_btb_hit;
            btb_update_hit_way = bcb_restore_bcb_info.btb_hit_way; // can be incorrect if rob_restart same cycle

            branch_update_ready = 1'b1;
        end
    end
    btb BTB (
        .CLK(CLK),
        .nRST(nRST),
        .read_req_valid(btb_read_req_valid),
        .read_req_fetch_idx(btb_read_req_fetch_idx),
        .read_req_asid(btb_read_req_asid),
        .read_resp_pc38(btb_read_resp_pc38),
        .read_resp_hit(btb_read_resp_hit),
        .read_resp_double_hit(btb_read_resp_double_hit),
        .read_resp_hit_way(btb_read_resp_hit_way),
        .read_resp_hit_lane_way0(btb_read_resp_hit_lane_by_way[0]),
        .read_resp_hit_lane_way1(btb_read_resp_hit_lane_by_way[1]),
        .read_resp_btb_info_way0(btb_read_resp_btb_info_by_way[0]),
        .read_resp_btb_info_way1(btb_read_resp_btb_info_by_way[1]),
        .update_valid(btb_update_valid),
        .update_pc38(btb_update_pc38),
        .update_asid(btb_update_asid),
        .update_btb_info(btb_update_btb_info),
        .update_hit(btb_update_hit),
        .update_hit_way(btb_update_hit_way)
    );

    // pht:
    always_comb begin
        pht_read_req_valid = REQ_valid & REQ_pass;
        pht_read_req_fetch_idx = REQ_received_pc38.idx;
        pht_read_req_gh = REQ_received_gh;
        pht_read_req_asid = fetch_arch_asid;

        pht_read_resp_redirect_lane_way0 = btb_read_resp_hit_lane_by_way[0];
        pht_read_resp_redirect_lane_way1 = btb_read_resp_hit_lane_by_way[1];

        pht_update_valid = branch_update_valid & branch_update_ready & branch_update_btb_info.action.branch;
        pht_update_pc38 = branch_update_src_pc38;
        pht_update_gh = bcb_restore_bcb_info.gh; // can be incorrect if rob_restart same cycle
        pht_update_asid = branch_update_asid;
        pht_update_taken = branch_update_taken;
    end
    pht PHT (
        .CLK(CLK),
        .nRST(nRST),
        .read_req_valid(pht_read_req_valid),
        .read_req_fetch_idx(pht_read_req_fetch_idx),
        .read_req_gh(pht_read_req_gh),
        .read_req_asid(pht_read_req_asid),
        .read_resp_redirect_lane_way0(pht_read_resp_redirect_lane_way0),
        .read_resp_redirect_lane_way1(pht_read_resp_redirect_lane_way1),
        .read_resp_taken_way0(pht_read_resp_taken_by_way[0]),
        .read_resp_taken_way1(pht_read_resp_taken_by_way[1]),
        .update_valid(pht_update_valid),
        .update_pc38(pht_update_pc38),
        .update_gh(pht_update_gh),
        .update_asid(pht_update_asid),
        .update_taken(pht_update_taken)
    );

    // ibtb:
    always_comb begin
        ibtb_read_src_pc38.upc = RESP_received_pc38.upc;
        ibtb_read_src_pc38.idx = RESP_received_pc38.idx;
        ibtb_read_src_pc38.lane = btb_read_resp_hit_lane_by_way[btb_read_resp_hit_way];
        ibtb_read_ibtb_gh = RESP_received_gh;
        ibtb_read_asid = fetch_arch_asid;
        
        ibtb_update_valid = branch_update_valid & branch_update_ready & branch_update_btb_info.action.ibtb;
        ibtb_update_src_pc38 = branch_update_src_pc38;
        ibtb_update_ibtb_gh = bcb_restore_bcb_info.gh; // can be incorrect if rob_restart same cycle
        ibtb_update_asid = branch_update_asid;
        ibtb_update_tgt_pc38 = branch_update_tgt_pc38;
    end
    ibtb IBTB (
        .CLK(CLK),
        .nRST(nRST),
        .read_src_pc38(ibtb_read_src_pc38),
        .read_ibtb_gh(ibtb_read_ibtb_gh),
        .read_asid(ibtb_read_asid),
        .read_tgt_pc38(ibtb_read_tgt_pc38),
        .update_valid(ibtb_update_valid),
        .update_src_pc38(ibtb_update_src_pc38),
        .update_ibtb_gh(ibtb_update_ibtb_gh),
        .update_asid(ibtb_update_asid),
        .update_tgt_pc38(ibtb_update_tgt_pc38)
    );

    // mdpt:
    always_comb begin
        mdpt_read_req_valid = REQ_valid & REQ_pass;
        mdpt_read_req_fetch_idx = REQ_received_pc38.idx;
        mdpt_read_req_asid = fetch_arch_asid;
    end
    mdpt MDPT (
        .CLK(CLK),
        .nRST(nRST),
        .read_req_valid(mdpt_read_req_valid),
        .read_req_fetch_idx(mdpt_read_req_fetch_idx),
        .read_req_asid(mdpt_read_req_asid),
        .read_resp_mdp_by_lane(mdpt_read_resp_mdp_by_lane),
        .update_valid(mdpt_update_valid),
        .update_pc38(mdpt_update_pc38),
        .update_asid(mdpt_update_asid),
        .update_mdp(mdpt_update_mdp)
    );

    // bcb:
    always_comb begin
        bcb_save_valid = 
            RESP_valid
            & RESP_pass
            & btb_read_resp_hit
            & (
                ~btb_read_resp_hit_way & corep::btb_action_saves_bcb(btb_read_resp_btb_info_by_way[0].action)
                | btb_read_resp_hit_way & corep::btb_action_saves_bcb(btb_read_resp_btb_info_by_way[1].action)
            )
        ;
        bcb_save_bcb_info.gh = RESP_received_gh;
        bcb_save_bcb_info.ras_idx = ras_ret_ras_idx;
        bcb_save_bcb_info.ras_cnt = ras_ret_ras_cnt;
        bcb_save_bcb_info.btb_hit_way = btb_read_resp_hit_way;

        if (rob_restart_valid) begin
            bcb_restore_bcb_idx = rob_restart_bcb_idx;
        end
        else if (branch_update_valid & branch_update_ready & branch_update_mispred) begin
            bcb_restore_bcb_idx = branch_update_bcb_idx;
        end
        else begin
            bcb_restore_bcb_idx = branch_update_bcb_idx;
        end
    end
    bcb BCB (
        .CLK(CLK),
        .nRST(nRST),
        .save_valid(bcb_save_valid),
        .save_bcb_info(bcb_save_bcb_info),
        .save_bcb_idx(bcb_save_bcb_idx),
        .restore_bcb_idx(bcb_restore_bcb_idx),
        .restore_bcb_info(bcb_restore_bcb_info)
    );

    // ibuffer:
    always_comb begin
        ibuffer_enq_valid = RESP_valid & RESP_pass;

        ibuffer_enq_info.valid_by_lane = RESP_valid_by_lane;
        ibuffer_enq_info.btb_hit_by_lane = btb_read_resp_hit << btb_read_resp_hit_way;
        ibuffer_enq_info.redirect_taken_by_lane = RESP_redirect_no_double_hit_not_taken << btb_read_resp_hit_way;
        ibuffer_enq_info.bcb_idx = bcb_save_bcb_idx;
        ibuffer_enq_info.src_pc35.upc = RESP_received_pc38.upc;
        ibuffer_enq_info.src_pc35.idx = RESP_received_pc38.idx;
        ibuffer_enq_info.tgt_pc38.upc = REQ_received_pc38.upc;
        ibuffer_enq_info.tgt_pc38.idx = REQ_received_pc38.idx;
        ibuffer_enq_info.tgt_pc38.lane = REQ_received_pc38.lane;
        ibuffer_enq_info.page_fault = itlb_resp_page_fault;
        ibuffer_enq_info.access_fault = itlb_resp_access_fault;
        ibuffer_enq_info.mdp_by_lane = mdpt_read_resp_mdp_by_lane;

        ibuffer_enq_fetch_hit_valid = icache_feedback_hit_valid; // need to make sure = 1'b0 means miss that has been launched
        ibuffer_enq_fetch_hit_fetch16B = icache_resp_fetch16B_by_way[icache_feedback_hit_way];

        ibuffer_restart_valid = any_restart;
    end
    ibuffer IBUFFER (
        .CLK(CLK),
        .nRST(nRST),
        .enq_valid(ibuffer_enq_valid),
        .enq_info(ibuffer_enq_info),
        .enq_fetch_hit_valid(ibuffer_enq_fetch_hit_valid),
        .enq_fetch_hit_fetch16B(ibuffer_enq_fetch_hit_fetch16B),
        .enq_ready(ibuffer_enq_ready),
        .enq_fmid(ibuffer_enq_fmid),
        .fetch_miss_return_valid(icache_miss_return_valid),
        .fetch_miss_return_fmid(icache_miss_return_fmid),
        .fetch_miss_return_fetch16B(icache_miss_return_fetch16B),
        .instr_yield_valid(instr_yield_valid),
        .instr_yield_by_way(instr_yield_by_way),
        .instr_yield_ready(instr_yield_ready),
        .restart_valid(ibuffer_restart_valid)
    );

endmodule
