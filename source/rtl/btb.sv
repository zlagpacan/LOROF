/*
    Filename: btb.sv
    Author: zlagpacan
    Description: RTL for Branch Target (and Branch Prediction Info) Buffer
    Spec: LOROF/spec/design/btb.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module btb (

    // seq
    input logic CLK,
    input logic nRST,

    // REQ stage
    input logic         valid_REQ,
    input logic [31:0]  PC_REQ,
    input logic [8:0]   ASID_REQ,

    // RESP stage
    output logic                                    hit_by_instr_RESP,
    output logic [15:0][BTB_PRED_INFO_WIDTH-1:0]    pred_info_by_instr_RESP,
    output logic [15:0]                             pred_lru_by_instr_RESP,
    output logic [15:0][BTB_TARGET_WIDTH-1:0]       target_by_instr_RESP,

    // update
    input logic                             update_valid,
    input logic [31:0]                      update_start_PC,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   update_pred_info,
    input logic                             update_pred_lru,
    input logic [31:0]                      update_target_PC
);

    // ----------------------------------------------------------------
    // Signals:

    // REQ Stage:
    logic [BTB_INDEX_WIDTH-1:0]     index_REQ;
    logic [BTB_TAG_WIDTH-1:0]       hashed_tag_REQ;

    // RESP Stage:
    
    // array outputs
    typedef struct packed {
        logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info;
        logic [BTB_TAG_WIDTH-1:0]           tag;
        logic [BTB_TARGET_WIDTH-1:0]        target;
    } pred_info_tag_target_one_way_t;

    pred_info_tag_target_one_way_t [15:0][1:0] array_pred_info_tag_target_by_instr_by_way_RESP;
    logic [15:0] array_pred_lru_by_instr_RESP;

    // replicated tags
    logic [15:0][BTB_TAG_WIDTH-1:0] replicated_tags_by_instr_RESP;

    // VTM's
    logic [15:0][1:0] vtm_by_instr_by_way_RESP;

    // Update 0:


    // Update 1:

    
    // ----------------------------------------------------------------
    // REQ Stage Logic:

    assign index_REQ = PC_REQ[BTB_INDEX_WIDTH+1-1:1];

    btb_tag_hash BTB_TAG_HASH (
        .PC(PC_REQ),
        .ASID(ASID_REQ),
        .tag(hashed_tag_REQ)
    );

    // ----------------------------------------------------------------
    // RESP Stage Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            replicated_tags_by_instr_RESP <= '0;
        end
        else begin
            replicated_tags_by_instr_RESP <= {16{hashed_tag_REQ}};
        end
    end

    always_comb begin

        // iter over instr's
        for (int i = 0; i < 16; i++) begin

            // check way 0 and way 1 for vtm
            vtm_by_instr_by_way_RESP[i][0] = replicated_tags_by_instr_RESP[i] == array_pred_info_tag_target_by_instr_by_way_RESP[i][0].tag;
            vtm_by_instr_by_way_RESP[i][1] = replicated_tags_by_instr_RESP[i] == array_pred_info_tag_target_by_instr_by_way_RESP[i][1].tag;
        
            // hit if either way vtm
            hit_by_instr_RESP[i] = vtm_by_instr_by_way_RESP[i][0] | vtm_by_instr_by_way_RESP[i][1];

            // prioritize way 0
            if (vtm_by_instr_by_way_RESP[i][0]) begin

                // pred info
                pred_info_by_instr_RESP[i] = array_pred_info_tag_target_by_instr_by_way_RESP[i][0].pred_info;

                // target
                target_by_instr_RESP[i] = array_pred_info_tag_target_by_instr_by_way_RESP[i][0].target;

                // lru -> this way: 0
                pred_lru_by_instr_RESP[i] = 1'b0;
            end

            // way 1 and not way 0
            else if (vtm_by_instr_by_way_RESP[i][1]) begin

                // pred info
                pred_info_by_instr_RESP[i] = array_pred_info_tag_target_by_instr_by_way_RESP[i][1].pred_info;

                // target
                target_by_instr_RESP[i] = array_pred_info_tag_target_by_instr_by_way_RESP[i][1].target;

                // lru -> this way: 1
                pred_lru_by_instr_RESP[i] = 1'b1;
            end

            // otherwise, inv pred info
            else begin

                // pred info
                    // default to way 0
                pred_info_by_instr_RESP[i] = array_pred_info_tag_target_by_instr_by_way_RESP[i][0].pred_info;

                // target
                    // default to way 0
                target_by_instr_RESP[i] = array_pred_info_tag_target_by_instr_by_way_RESP[i][0].target;

                // lru -> given lru
                pred_lru_by_instr_RESP[i] = array_pred_lru_by_instr_RESP[i];
            end
        end
    end
    
    // ----------------------------------------------------------------
    // Update 0 Logic:


    
    // ----------------------------------------------------------------
    // Update 1 Logic:


    
    // ----------------------------------------------------------------
    // BRAMs:

    // pred info + tag + target BRAM bank
    bram_1rport_1wport #(
        .INNER_WIDTH(
            BTB_NWAY_ENTRIES_PER_BLOCK * 
            BTB_ENTRY_ASSOC * 
            (BTB_PRED_INFO_WIDTH + BTB_TAG_WIDTH + BTB_TARGET_WIDTH)
        ),
        .OUTER_WIDTH(BTB_SETS)
    ) PRED_INFO_BRAM_BANK (
        .CLK(CLK),
        .nRST(nRST),

        .ren(valid_REQ),
        .rindex(index_REQ),
        .rdata(pred_info_tag_target_by_instr_by_way_RESP),

        .wen_byte(),
        .windex(),
        .wdata()
    );

    // LRU BRAM bank
    bram_1rport_1wport #(
        .INNER_WIDTH(BTB_NWAY_ENTRIES_PER_BLOCK),
        .OUTER_WIDTH(BTB_SETS)
    ) TAG_TARGET_BRAM_BANK (
        .CLK(CLK),
        .nRST(nRST),

        .ren(valid_REQ),
        .rindex(index_REQ),
        .rdata(array_pred_lru_by_instr_RESP),

        .wen_byte(),
        .windex(),
        .wdata()
    );

endmodule