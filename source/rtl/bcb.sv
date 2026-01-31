/*
    Filename: bcb.sv
    Author: zlagpacan
    Description: RTL for Branch Checkpoint Buffer
    Spec: LOROF/spec/design/bcb.md
*/

`include "corep.vh"

module bcb (

    // seq
    input logic CLK,
    input logic nRST,

    // save control
    input logic                 save_valid,
    input corep::bcb_info_t     save_bcb_info,

    output corep::bcb_idx_t     save_bcb_idx,

    // restore control
    input corep::bcb_idx_t      restore_bcb_idx,

    output corep::bcb_info_t    restore_bcb_info
);

    // ----------------------------------------------------------------
    // Signals:

    corep::bcb_idx_t save_bcb_idx_plus_1;

    // ----------------------------------------------------------------
    // Logic: 

    generate
        // power-of-2 # entries can use simple +1 for ptr
        if (corep::BCB_ENTRIES & (corep::BCB_ENTRIES - 1) == 0) begin
            assign save_bcb_idx_plus_1 = save_bcb_idx + 1;
        end

        // otherwise, manual wraparound for ptr
        else begin
            always_comb begin
                if (save_bcb_idx == corep::BCB_ENTRIES - 1) begin
                    save_bcb_idx_plus_1 = 0;
                end
                else begin
                    save_bcb_idx_plus_1 = save_bcb_idx + 1;
                end
            end
        end
    endgenerate

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            save_bcb_idx <= 0;
        end
        else begin
            if (save_valid) begin
                save_bcb_idx <= save_bcb_idx_plus_1;
            end
        end
    end

    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::bcb_info_t)),
        .OUTER_WIDTH(corep::BCB_ENTRIES)
    ) DISTRAM_BUFFER (
        .CLK(CLK),
        .rindex(restore_bcb_idx),
        .rdata(restore_bcb_info),
        .wen(save_valid),
        .windex(save_bcb_idx),
        .wdata(save_bcb_info)
    );

endmodule