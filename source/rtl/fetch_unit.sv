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
            // btb, gbpt, mdpt req
            // itlb, icache req
        // RESP:
            // btb, gbpt, mdpt resp
            // itlb, icache resp
            // ras read/write
            // btb hit check
            // yield PC index bits if fast redirect
            // fast redirect -> REQ
        // LATE:
            // upct, ibtb lookup
            // yield full pc
            // slow redirect -> REQ
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
    output logic                icache_resp_hit_valid,
    output sysp::icache_way_t   icache_resp_hit_way,
    output logic                icache_resp_miss_valid,
    output corep::fmid_t        icache_resp_fmid,
    output sysp::pa39_t         icache_resp_pa39,

    input logic                 icache_resp_miss_ready,

    // icache miss return
    input logic                 icache_miss_return_valid,
    input corep::fmid_t         icache_miss_return_fmid,
    input corep::fetch16B_t     icache_miss_return_fetch16B,

    // ibuffer enq
    input logic                         ibuffer_enq_valid,
    input corep::ibuffer_enq_info_t     ibuffer_enq_info,
    input logic                         ibuffer_enq_fetch_hit_valid,
    input corep::fetch16B_t             ibuffer_enq_fetch_hit_fetch16B,

    // ibuffer enq feedback
    output logic                        ibuffer_enq_ready,
    output corep::fmid_t                ibuffer_enq_fmid,

    // fetch + decode restart from ROB
    input logic                 rob_restart_valid,
    input corep::pc38_t         rob_restart_pc38,
    input corep::asid_t         rob_restart_asid,
    input corep::exec_mode_t    rob_restart_exec_mode,
    input logic                 rob_restart_virtual_mode,

    // decode unit control
    input logic             decode_unit_trigger_wait_for_restart,

    input logic             decode_unit_restart_valid,
    input corep::pc38_t     decode_unit_restart_pc38,

    // branch update
    input logic                 branch_update_valid,
    input corep::asid_t         branch_update_asid,
    input corep::btb_info_t     branch_update_btb_info,
    input corep::pc38_t         branch_update_src_pc38,
    input corep::pc38_t         branch_update_tgt_pc38,
    input logic                 branch_update_taken,
    input logic                 branch_update_btb_hit,
    input corep::bcb_idx_t      branch_update_bcb_idx,

    // mdpt update
    input logic             mdpt_update_valid,
    input corep::pc38_t     mdpt_update_pc38,
    input corep::asid_t     mdpt_update_asid,
    input corep::mdp_t      mdpt_update_mdp
);

    // need to save LATE upct in RESP stage in case where previous instr needed upct to route to this instr
        // and this instr needs LATE for ibtb

    // ----------------------------------------------------------------
    // Signals:

    // control signals
    logic stall_REQ;
    logic stall_RESP;
    logic stall_LATE;

    logic REQ_valid;
    logic RESP_valid;
    logic LATE_valid;
    logic LATE_for_RESP;

    // wait for restart state
    logic wait_for_restart_state;

    // fetch arch state
    corep::asid_t       fetch_arch_asid;
    corep::exec_mode_t  fetch_arch_exec_mode;
    logic               fetch_arch_virtual_mode;

    ////////////////
    // REQ stage: //
    ////////////////

    corep::pc38_t       REQ_latched_pc38;
    corep::pc38_t       REQ_pc38_next_8;
    corep::fetch_idx_t  REQ_broadcast_fetch_idx;

    corep::gh_t REQ_gh;
    corep::gh_t REQ_broadcast_gh;

    /////////////////
    // RESP stage: //
    /////////////////

    corep::pc38_t       RESP_latched_pc38;
    corep::fetch_idx_t  RESP_fetch_idx;

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

    // ----------------------------------------------------------------
    // Logic:

    

endmodule

