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
    input logic                     valid_REQ,
    input logic [31:0]              full_PC_REQ,
    input logic [ASID_WIDTH-1:0]    ASID_REQ,

    // RESP stage
    output logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_PRED_INFO_WIDTH-1:0]  pred_info_by_instr_RESP,
    output logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]                           pred_lru_by_instr_RESP,
    output logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_TARGET_WIDTH-1:0]     target_by_instr_RESP,

    // Update 0
    input logic                     update0_valid,
    input logic [31:0]              update0_start_full_PC,
    input logic [ASID_WIDTH-1:0]    update0_ASID,

    // Update 1
    input logic [BTB_PRED_INFO_WIDTH-1:0]   update1_pred_info,
    input logic                             update1_pred_lru,
    input logic [31:0]                      update1_target_full_PC
);

    // ----------------------------------------------------------------
    // Signals:

    // REQ Stage:
    logic [BTB_INDEX_WIDTH-1:0]             index_REQ;
    logic [BTB_TAG_WIDTH-1:0]               hashed_tag_REQ;
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]  array_pred_lru_by_instr_REQ;

    // RESP Stage:
    
    // array outputs
    typedef struct packed {
        logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info;
        logic [BTB_TAG_WIDTH-1:0]           tag;
        logic [BTB_TARGET_WIDTH-1:0]        target;
    } pred_info_tag_target_one_way_t;

    pred_info_tag_target_one_way_t [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][1:0]
        array_pred_info_tag_target_by_instr_by_way_RESP;
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0] array_pred_lru_by_instr_RESP;

    // replicated tags
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][BTB_TAG_WIDTH-1:0] replicated_tags_by_instr_RESP;

    // VTM's
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][1:0] vtm_by_instr_by_way_RESP;

    // Update 0:
    logic [BTB_INDEX_WIDTH-1:0]                 update0_index;
    logic [BTB_TAG_WIDTH-1:0]                   update0_hashed_tag;
    logic [LOG_BTB_NWAY_ENTRIES_PER_BLOCK-1:0]  update0_instr;
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]      update0_old_pred_lru_by_instr;

    // Update 1:
    logic                                       update1_valid;
    logic [BTB_INDEX_WIDTH-1:0]                 update1_index;
    logic [BTB_TAG_WIDTH-1:0]                   update1_hashed_tag;
    logic [LOG_BTB_NWAY_ENTRIES_PER_BLOCK-1:0]  update1_instr;
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]      update1_old_pred_lru_by_instr;
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]      update1_new_pred_lru_by_instr;
    logic [BTB_TARGET_WIDTH-1:0]                update1_target_PC;

    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0][1:0][(BTB_PRED_INFO_WIDTH+BTB_TAG_WIDTH+BTB_TARGET_WIDTH)/8-1:0] 
        update1_byte_mask_pred_info_tag_target_by_instr_by_way;

    logic                                   last_update1_conflict;
    logic [BTB_NWAY_ENTRIES_PER_BLOCK-1:0]  last_update1_new_pred_lru_by_instr;

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    assign index_REQ = full_PC_REQ[BTB_INDEX_WIDTH+LOG_BTB_NWAY_ENTRIES_PER_BLOCK+1-1 : LOG_BTB_NWAY_ENTRIES_PER_BLOCK+1];

    btb_tag_hash BTB_REQ_TAG_HASH (
        .PC(full_PC_REQ),
        .ASID(ASID_REQ),
        .tag(hashed_tag_REQ)
    );

    // ----------------------------------------------------------------
    // RESP Stage Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            replicated_tags_by_instr_RESP <= '0;
            array_pred_lru_by_instr_RESP <= '0;
        end
        else begin
            replicated_tags_by_instr_RESP <= {BTB_NWAY_ENTRIES_PER_BLOCK{hashed_tag_REQ}};
            array_pred_lru_by_instr_RESP <= array_pred_lru_by_instr_REQ;
        end
    end

    always_comb begin

        // iter over instr's
        for (int i = 0; i < BTB_NWAY_ENTRIES_PER_BLOCK; i++) begin

            // check way 0 and way 1 for vtm
            vtm_by_instr_by_way_RESP[i][0] = replicated_tags_by_instr_RESP[i] == array_pred_info_tag_target_by_instr_by_way_RESP[i][0].tag;
            vtm_by_instr_by_way_RESP[i][1] = replicated_tags_by_instr_RESP[i] == array_pred_info_tag_target_by_instr_by_way_RESP[i][1].tag;

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
                    // 2 msb's cleared since inv
                    // lower bits default to way 0
                pred_info_by_instr_RESP[i][7:6] = 2'b00;
                pred_info_by_instr_RESP[i][5:0] = array_pred_info_tag_target_by_instr_by_way_RESP[i][0].pred_info[5:0];

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

    assign update0_index = update0_start_full_PC[BTB_INDEX_WIDTH+LOG_BTB_NWAY_ENTRIES_PER_BLOCK+1-1 : LOG_BTB_NWAY_ENTRIES_PER_BLOCK+1];
    assign update0_instr = update0_start_full_PC[LOG_BTB_NWAY_ENTRIES_PER_BLOCK+1-1 : 1];

    btb_tag_hash BTB_UPDATE0_TAG_HASH (
        .PC(update0_start_full_PC),
        .ASID(update0_ASID),
        .tag(update0_hashed_tag)
    );
    
    // ----------------------------------------------------------------
    // Update 1 Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            update1_valid <= 1'b0;
            update1_index <= '0;
            update1_hashed_tag <= '0;
            update1_instr <= '0;
            update1_old_pred_lru_by_instr <= '0;

            last_update1_conflict <= 1'b0;
            last_update1_new_pred_lru_by_instr <= '0;
        end
        else begin
            update1_valid <= update0_valid;
            update1_index <= update0_index;
            update1_hashed_tag <= update0_hashed_tag;
            update1_instr <= update0_instr;
            update1_old_pred_lru_by_instr <= update0_old_pred_lru_by_instr;

            last_update1_conflict <= update0_valid & update1_valid & update0_index == update1_index;
            last_update1_new_pred_lru_by_instr <= update1_new_pred_lru_by_instr;
        end
    end

    always_comb begin
        update1_target_PC = update1_target_full_PC[BTB_TARGET_WIDTH+1-1:1];

        // RMW pred lru for this set
            // flip LRU to opposite of this update
            // if conflicted last cycle, use update value from last cycle
        if (last_update1_conflict) begin
            update1_new_pred_lru_by_instr = last_update1_new_pred_lru_by_instr;
        end else begin
            update1_new_pred_lru_by_instr = update1_old_pred_lru_by_instr;
        end
        update1_new_pred_lru_by_instr[update1_instr] = ~update1_pred_lru;

        // pred info tag target byte mask follows 4B associated with this instr and way
        update1_byte_mask_pred_info_tag_target_by_instr_by_way = '0;
        update1_byte_mask_pred_info_tag_target_by_instr_by_way[update1_instr][update1_pred_lru] 
            = update1_valid ? '1 : '0;
    end
    
    // ----------------------------------------------------------------
    // RAM Arrays:

    /////////////////////////////////////
    // BRAM Array shared over Instr's: //
    /////////////////////////////////////

    // pred info + tag + target BRAM array
    bram_1rport_1wport #(
        .INNER_WIDTH(
            BTB_NWAY_ENTRIES_PER_BLOCK * 
            BTB_ENTRY_ASSOC * 
            (BTB_PRED_INFO_WIDTH + BTB_TAG_WIDTH + BTB_TARGET_WIDTH)
        ),
        .OUTER_WIDTH(BTB_SETS)
    ) PRED_INFO_TAG_TARGET_BRAM_ARRAY (
        .CLK(CLK),
        .nRST(nRST),

        .ren(valid_REQ),
        .rindex(index_REQ),
        .rdata(array_pred_info_tag_target_by_instr_by_way_RESP),

        .wen_byte(update1_byte_mask_pred_info_tag_target_by_instr_by_way),
        .windex(update1_index),
        .wdata({(BTB_NWAY_ENTRIES_PER_BLOCK*BTB_ENTRY_ASSOC){update1_pred_info, update1_hashed_tag, update1_target_PC}})
    );

    // //////////////////////////
    // // BRAM Array per Instr //
    // //////////////////////////

    // // pred info + tag + target BRAM array
    // genvar bram_instr;
    // generate
    // for (bram_instr = 0; bram_instr < BTB_NWAY_ENTRIES_PER_BLOCK; bram_instr++)
    
    //     bram_1rport_1wport #(
    //         .INNER_WIDTH( // 2 * 32
    //             BTB_ENTRY_ASSOC * 
    //             (BTB_PRED_INFO_WIDTH + BTB_TAG_WIDTH + BTB_TARGET_WIDTH)
    //         ),
    //         .OUTER_WIDTH(BTB_SETS)
    //     ) PRED_INFO_TAG_TARGET_BRAM_ARRAY (
    //         .CLK(CLK),
    //         .nRST(nRST),

    //         .ren(valid_REQ),
    //         .rindex(index_REQ),
    //         .rdata(array_pred_info_tag_target_by_instr_by_way_RESP[bram_instr]),

    //         .wen_byte(update1_byte_mask_pred_info_tag_target_by_instr_by_way[bram_instr]),
    //         .windex(update1_index),
    //         .wdata({2{update1_pred_info, update1_hashed_tag, update1_target_PC}})
    //     );

    // endgenerate

    //////////////////
    // LRU DistRAM: //
    //////////////////

    // LRU DistRAM array
    distram_2rport_1wport #(
        .INNER_WIDTH(BTB_NWAY_ENTRIES_PER_BLOCK),
        .OUTER_WIDTH(BTB_SETS)
    ) LRU_DISTRRAM_ARRAY (
        .CLK(CLK),

        .port0_rindex(index_REQ),
        .port0_rdata(array_pred_lru_by_instr_REQ),

        .port1_rindex(update0_index),
        .port1_rdata(update0_old_pred_lru_by_instr),

        .wen(update1_valid),
        .windex(update1_index),
        .wdata(update1_new_pred_lru_by_instr)
    );

endmodule