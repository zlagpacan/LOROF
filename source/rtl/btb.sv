/*
    Filename: btb.sv
    Author: zlagpacan
    Description: RTL for Branch Target Buffer
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
    input logic [29:0]  PC30_REQ,

    // RESP stage
    input logic [3:0][29:0] PC30_by_way_RESP,

    output logic [3:0]                              vtm_by_way_RESP,
    output logic [3:0][BTB_PRED_INFO_WIDTH-1:0]     pred_info_by_way_RESP,
    output logic [3:0][BTB_TARGET_WIDTH-1:0]        target_by_way_RESP,

    // update
    input logic                             update_valid,
    input logic [29:0]                      update_start_PC30,
    input logic [BTB_PRED_INFO_WIDTH-1:0]   update_pred_info,
    input logic [29:0]                      update_target_PC30
);

    // ----------------------------------------------------------------
    // Signals:

    // REQ Stage:
    logic [1:0][BTB_INDEX_WIDTH-1:0] index_by_bank_REQ;

    // RESP Stage:
    logic [3:0]                                             bank_by_way_RESP;
    logic [3:0][1:0]                                        offset_by_way_RESP;

    logic [1:0][3:0][BTB_PRED_INFO_WIDTH-1:0]               pred_info_by_bank_by_offset_RESP;
    logic [1:0][3:0][BTB_TAG_WIDTH+BTB_TARGET_WIDTH-1:0]    tag_target_by_bank_by_offset_RESP;
    logic [3:0][BTB_TAG_WIDTH-1:0]                          tag_by_way_RESP;
    logic [3:0][BTB_TAG_WIDTH-1:0]                          pipeline_tag_by_way_RESP;

    // Update:
    logic [1:0]                             update_valid_by_bank;
    logic [BTB_INDEX_WIDTH-1:0]             update_index;

    logic [1:0][BTB_PRED_INFO_WIDTH/8-1:0]  update_pred_info_byte_mask_by_bank;
    // already have update_pred_info // make 4 copies at each bank
    
    logic [1:0][(BTB_TAG_WIDTH+BTB_TARGET_WIDTH)/8-1:0]     update_tag_target_byte_mask_by_bank;
    logic [1:0][BTB_TAG_WIDTH-1:0]                          update_tag; // make 4 copies at each bank
    logic [1:0][BTB_TARGET_WIDTH-1:0]                       update_target; // make 4 copies at each bank

    // ----------------------------------------------------------------
    // REQ Stage Logic:

    always_comb begin

        // start bank 0: bank 0 gets PC30, bank 1 gets PC30
        if (~PC30_REQ[2]) begin
            index_by_bank_REQ[0] = PC30_REQ[LOG_BTB_ENTRIES-1:3];
            index_by_bank_REQ[1] = PC30_REQ[LOG_BTB_ENTRIES-1:3];
                // lower 3 PC30 bits for bank and offset
        end

        // start bank 1: bank 1 gets PC30, bank 0 gets PC30 + 8
        else begin
            index_by_bank_REQ[1] = PC30_REQ[LOG_BTB_ENTRIES-1:3];
            index_by_bank_REQ[0] = PC30_REQ[LOG_BTB_ENTRIES-1:3] + 1;
                // lower 3 PC30 bits for bank and offset
        end
    end

    // ----------------------------------------------------------------
    // RESP Stage Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            bank_by_way_RESP <= 4'b0000;
            offset_by_way_RESP <= {2'h0, 2'h0, 2'h0, 2'h0};
        end
        else begin
            case (PC30_REQ[2:0])
                3'b000: begin
                    bank_by_way_RESP <= 4'b0000;
                    offset_by_way_RESP <= {2'h0, 2'h1, 2'h2, 2'h3};
                end
                3'b001: begin
                    bank_by_way_RESP <= 4'b0001;
                    offset_by_way_RESP <= {2'h1, 2'h2, 2'h3, 2'h0};
                end
                3'b010: begin
                    bank_by_way_RESP <= 4'b0011;
                    offset_by_way_RESP <= {2'h2, 2'h3, 2'h0, 2'h1};
                end
                3'b011: begin
                    bank_by_way_RESP <= 4'b0111;
                    offset_by_way_RESP <= {2'h3, 2'h0, 2'h1, 2'h2};
                end
                3'b100: begin
                    bank_by_way_RESP <= 4'b1111;
                    offset_by_way_RESP <= {2'h0, 2'h1, 2'h2, 2'h3};
                end
                3'b101: begin
                    bank_by_way_RESP <= 4'b1110;
                    offset_by_way_RESP <= {2'h1, 2'h2, 2'h3, 2'h0};
                end
                3'b110: begin
                    bank_by_way_RESP <= 4'b1100;
                    offset_by_way_RESP <= {2'h2, 2'h3, 2'h0, 2'h1};
                end
                3'b111: begin
                    bank_by_way_RESP <= 4'b1000;
                    offset_by_way_RESP <= {2'h3, 2'h0, 2'h1, 2'h2};
                end
            endcase
        end
    end

    // RESP PC30 hash's
    genvar hash_way;
    generate
        for (hash_way = 0; hash_way < 4; hash_way++) begin

            btb_tag_hash PC30_RESP (
                .PC30(PC30_by_way_RESP[hash_way]),
                .tag(pipeline_tag_by_way_RESP[hash_way])
            );
        end
    endgenerate

    // gather values with bank and offset by way
    always_comb begin

        for (int i = 0; i < 4; i++) begin

            pred_info_by_way_RESP[i] = pred_info_by_bank_by_offset_RESP
                [bank_by_way_RESP[i]]
                [offset_by_way_RESP[i]]
            ;

            // tag in upper bits
            tag_by_way_RESP[i] = tag_target_by_bank_by_offset_RESP
                [bank_by_way_RESP[i]]
                [offset_by_way_RESP[i]]
                [BTB_TAG_WIDTH+BTB_TARGET_WIDTH-1:BTB_TARGET_WIDTH]
            ;

            // target in lower bits
            target_by_way_RESP[i] = tag_target_by_bank_by_offset_RESP
                [bank_by_way_RESP[i]]
                [offset_by_way_RESP[i]]
                [BTB_TARGET_WIDTH-1:0]
            ;

            // VTM against pipeline tag
            vtm_by_way_RESP[i] = (tag_by_way_RESP[i] == pipeline_tag_by_way_RESP[i]);
        end
    end

    // ----------------------------------------------------------------
    // Update Logic:

    assign update_valid_by_bank[0] = update_valid & ~update_start_PC30[2];
    assign update_valid_by_bank[1] = update_valid & update_start_PC30[2];
    assign update_index = update_start_PC30[LOG_BTB_ENTRIES-1:3];
        // lower 3 PC30 bits for bank and offset

    // update PC30 hash
    btb_tag_hash PC30_HASH (
        .PC30(update_start_PC30),
        .tag(update_tag)
    );
    
    assign update_target = update_target_PC30[BTB_TARGET_WIDTH-1:0];
        // lower target PC30 bits

    always_comb begin
        for (int bank = 0; bank < 2; bank++) begin
            update_pred_info_byte_mask_by_bank[bank] = '0;
            update_tag_target_byte_mask_by_bank[bank] = '0;

            // wide one-hot for bytes corresponding to this offset
            if (update_valid_by_bank[bank]) begin
                update_pred_info_byte_mask_by_bank[bank][update_start_PC30[1:0]] = '1;
                update_tag_target_byte_mask_by_bank[bank][update_start_PC30[1:0]] = '1;
            end
        end
    end

    // ----------------------------------------------------------------
    // BRAMs:

    // 2-bank BRAM

    genvar bank;
    generate
        for (bank = 0; bank < 2; bank++) begin
            
            ///////////////////////////////////////////////////////////
            // Unified BRAM:



            ///////////////////////////////////////////////////////////
            // Separate BRAMs:

            // pred info BRAM bank
            bram_1rport_1wport #(
                .INNER_WIDTH(BTB_PRED_INFO_WIDTH * 4),
                .OUTER_WIDTH(BTB_BLOCKS_PER_BANK)
            ) PRED_INFO_BRAM_BANK (
                .CLK(CLK),
                .nRST(nRST),
                .ren(valid_REQ),
                .rindex(index_by_bank_REQ[bank]),
                .rdata(pred_info_by_bank_by_offset_RESP[bank]),
                .wen_byte(update_pred_info_byte_mask_by_bank[bank]),
                .windex(update_index),
                .wdata({4{update_pred_info}})
            );

            // tag + target BRAM bank
            bram_1rport_1wport #(
                .INNER_WIDTH((BTB_TAG_WIDTH + BTB_TARGET_WIDTH) * 4),
                .OUTER_WIDTH(BTB_BLOCKS_PER_BANK)
            ) TAG_TARGET_BRAM_BANK (
                .CLK(CLK),
                .nRST(nRST),
                .ren(valid_REQ),
                .rindex(index_by_bank_REQ[bank]),
                .rdata(tag_target_by_bank_by_offset_RESP[bank]),
                .wen_byte(update_tag_target_byte_mask_by_bank[bank]),
                .windex(update_index),
                .wdata({4{update_tag, update_target}})
            );

            ///////////////////////////////////////////////////////////
        end
    endgenerate

endmodule