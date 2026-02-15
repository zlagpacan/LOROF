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

    // icache resp feedback
    output logic                icache_feedback_hit_valid,
    output sysp::icache_way_t   icache_feedback_hit_way,
    output logic                icache_feedback_miss_valid,
    output corep::fmid_t        icache_feedback_fmid,
    output sysp::pa39_t         icache_feedback_pa39,

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

    // restart from decode_unit
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

    corep::pc38_t   REQ_latched_pc38;
    corep::pc38_t   REQ_received_pc38;
    logic           REQ_received_upc_valid;

    corep::gh_t REQ_latched_gh;
    corep::gh_t REQ_received_gh;

    /////////////////
    // RESP stage: //
    /////////////////

    logic RESP_valid;
    logic RESP_pass;

    logic RESP_src_uses_upct;
    
    logic RESP_tgt_uses_ibtb;
    logic RESP_tgt_uses_upct;

    corep::pc38_t   RESP_received_pc38;
    logic           RESP_received_upc_valid;
    corep::pc38_t   RESP_final_pc38;
    corep::pc38_t   RESP_final_pc38_next_8;

    corep::gh_t RESP_received_gh;

    //////////////////
    // RESP2 stage: //
    //////////////////

    logic RESP2_valid;

    corep::pc38_t RESP2_tgt_pc38;

    /////////////////
    // LATE stage: //
    /////////////////

    logic LATE_valid;
    logic LATE_pass;

    corep::upct_idx_t   LATE_upct_idx;
    corep::pc38_t       LATE_tgt_upc;

    ///////////////////
    // update stage: //
    ///////////////////

    corep::btb_info_t   update_final_btb_info;
    corep::gh_t         update_final_gh;

    ////////////////
    // module IO: //
    ////////////////

    // upct IO:

    // read in
    logic               upct_read_valid;
    corep::upct_idx_t   upct_read_idx;
    // read out
    corep::upc_t        upct_read_upc;
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
    logic                   btb_read_req_valid;
    corep::fetch_idx_t      btb_read_req_fetch_idx;
    corep::asid_t           btb_read_req_asid;
    // read resp stage
    corep::pc38_t           btb_read_resp_pc38;
    logic                   btb_read_resp_hit;
    corep::btb_way_t        btb_read_resp_hit_way;
    corep::fetch_lane_t     btb_read_resp_hit_lane;
    logic                   btb_read_resp_double_hit;
    corep::btb_info_t       btb_read_resp_btb_info;
    // update
    logic                   btb_update_valid;
    corep::pc38_t           btb_update_pc38;
    corep::asid_t           btb_update_asid;
    corep::btb_info_t       btb_update_btb_info;
    logic                   btb_update_hit;
    corep::btb_way_t        btb_update_hit_way;

    // pht IO:

    // read req stage
    logic                   pht_read_req_valid;
    corep::fetch_idx_t      pht_read_req_fetch_idx;
    corep::gh_t             pht_read_req_gh;
    corep::asid_t           pht_read_req_asid;
    // read resp stage
    corep::fetch_lane_t     pht_read_resp_redirect_lane;
    logic                   pht_read_resp_taken;
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
            | (branch_update_valid & branch_update_mispred)
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
    always_comb begin
        REQ_valid = ~wfr;
        REQ_pass = (~RESP_valid | RESP_pass);

        REQ_received_pc38 = // TODO
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

        end
        else begin

        end
    end

    // RESP logic

    // RESP2 logic

    // LATE logic

    // update logic
    always_comb begin
        update_final_btb_info = branch_update_btb_info;
        if (branch_update_valid & branch_update_btb_info.use_upct) begin
            update_final_btb_info.upct_idx = upct_update_upct_idx;
        end

        update_final_gh = bcb_restore_bcb_info.gh;
        if (
            branch_update_valid
            & branch_update_mispred
            & (branch_update_btb_info.action == corep::BTB_ACTION_BRANCH)
        ) begin
            update_final_gh = {bcb_restore_bcb_info.gh << 1, branch_update_taken};
        end
    end

    // itlb req:

    // itlb resp:

    // icache req:

    // icache resp feedback:

    // icache miss return:

    // instr yield:

    // upct:
    always_comb begin
        upct_read_valid = LATE_valid & LATE_pass;
        upct_read_idx = LATE_upct_idx;

        upct_update_valid = branch_update_valid & branch_update_btb_info.use_upct;
        upct_update_upc = branch_update_tgt_pc38.upc;
    end
    upct UPCT (
        .CLK(CLK),
        .nRST(nRST),
        .read_valid(upct_read_valid),
        .read_idx(upct_read_idx),
        .read_upc(upct_read_upc),
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
            & corep::btb_action_is_link(btb_read_resp_btb_info.action)
        ;
        if (btb_read_resp_hit_lane == 3'h7) begin
            ras_link_pc38 = RESP_final_pc38_next_8;
        end
        else begin
            ras_link_pc38 = {RESP_final_pc38.upc, RESP_final_pc38.idx, btb_read_resp_hit_lane + 3'h1};
        end

        ras_ret_valid =
            RESP_valid
            & RESP_pass
            & btb_read_resp_hit
            & corep::btb_action_is_ret(btb_read_resp_btb_info.action)
        ;
        
        ras_update_valid = branch_update_valid & branch_update_mispred;
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

        btb_read_resp_pc38 = RESP_final_pc38;
        
        btb_update_valid = branch_update_valid;
        btb_update_pc38 = branch_update_src_pc38;
        btb_update_asid = branch_update_asid;
        btb_update_btb_info = update_final_btb_info;
        btb_update_hit = branch_update_btb_hit;
        btb_update_hit_way = bcb_restore_bcb_info.btb_hit_way;
    end
    btb BTB (
        .CLK(CLK),
        .nRST(nRST),
        .read_req_valid(btb_read_req_valid),
        .read_req_fetch_idx(btb_read_req_fetch_idx),
        .read_req_asid(btb_read_req_asid),
        .read_resp_pc38(btb_read_resp_pc38),
        .read_resp_hit(btb_read_resp_hit),
        .read_resp_hit_way(btb_read_resp_hit_way),
        .read_resp_hit_lane(btb_read_resp_hit_lane),
        .read_resp_double_hit(btb_read_resp_double_hit),
        .read_resp_btb_info(btb_read_resp_btb_info),
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

        pht_read_resp_redirect_lane = btb_read_resp_hit_lane;
        
        pht_update_valid = branch_update_valid & (branch_update_btb_info.action == corep::BTB_ACTION_BRANCH);
        pht_update_pc38 = branch_update_src_pc38;
        pht_update_gh = bcb_restore_bcb_info.gh;
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
        .read_resp_redirect_lane(pht_read_resp_redirect_lane),
        .read_resp_taken(pht_read_resp_taken),
        .update_valid(pht_update_valid),
        .update_pc38(pht_update_pc38),
        .update_gh(pht_update_gh),
        .update_asid(pht_update_asid),
        .update_taken(pht_update_taken)
    );

    // ibtb:
    always_comb begin
        ibtb_read_src_pc38 = {RESP_final_pc38.upc, RESP_final_pc38.idx, btb_read_resp_hit_lane};
        ibtb_read_ibtb_gh = RESP_received_gh;
        ibtb_read_asid = fetch_arch_asid;
        
        ibtb_update_valid = branch_update_valid & corep::btb_action_is_ibtb(branch_update_btb_info.action);
        ibtb_update_src_pc38 = branch_update_src_pc38;
        ibtb_update_ibtb_gh = bcb_restore_bcb_info.gh;
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
            & corep::btb_action_saves_bcb(btb_read_resp_btb_info.action)
        ;
        bcb_save_bcb_info.gh = RESP_received_gh;
        bcb_save_bcb_info.ras_idx = ras_ret_ras_idx;
        bcb_save_bcb_info.ras_cnt = ras_ret_ras_cnt;
        bcb_save_bcb_info.btb_hit_way = btb_read_resp_hit_way;

        if (rob_restart_valid) begin
            bcb_restore_bcb_idx = rob_restart_bcb_idx;
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
        ibuffer_enq_info. // TODO
        ibuffer_enq_fetch_hit_valid = icache_feedback_hit_valid;
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
