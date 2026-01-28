/*
    Filename: ras.sv
    Author: zlagpacan
    Description: RTL for Return Address Stack
    Spec: LOROF/spec/design/ras.md
*/

`include "corep.vh"

module ras (

    // seq
    input logic CLK,
    input logic nRST,

    // pc_gen link control
    input logic                 link_valid,
    input corep::PC38_t         link_pc38,

    // pc_gen return control
    input logic                 ret_valid,
    output corep::PC38_t        ret_pc38,
    output corep::RAS_idx_t     ret_ras_index,

    // update control
    input logic                 update_valid,
    input corep::RAS_idx_t      update_ras_index
);

    // ----------------------------------------------------------------
    // Signals:

    // ras array distram IO
    corep::RAS_idx_t    ras_array_distram_read_index;
    corep::PC38_t       ras_array_distram_read_data;

    logic               ras_array_distram_write_valid;
    corep::RAS_idx_t    ras_array_distram_write_index;
    corep::PC38_t       ras_array_distram_write_data;

    // sp control
    corep::RAS_idx_t sp, next_sp, sp_plus_1, sp_minus_1;

    // ----------------------------------------------------------------
    // Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            sp <= 0;
        end
        else begin
            sp <= next_sp;
        end
    end

    always_comb begin
        sp_plus_1 = sp + 1;
        sp_minus_1 = sp - 1;
    end

    // sp control
    always_comb begin

        // default hold sp
        next_sp = sp;

        // default write
        ras_array_distram_write_valid = 1'b0;
        ras_array_distram_write_index = sp;
        ras_array_distram_write_data = link_pc38;

        // first priority: update
        if (update_valid) begin

            // take update sp
            next_sp = update_ras_index;
        end

        // otherwise, check for link and ret
        else if (link_valid & ret_valid) begin

            // link addr at current sp
            ras_array_distram_write_valid = 1'b1;
            ras_array_distram_write_index = sp;
        end

        // otherwise, check for just link
        else if (link_valid) begin

            // link addr at next sp
            ras_array_distram_write_valid = 1'b1;
            ras_array_distram_write_index = sp_plus_1;

            // incr sp
            next_sp = sp_plus_1;
        end

        // otherwise, check for just ret
        else if (ret_valid) begin

            // decr sp
            next_sp = sp_minus_1;
        end
    end

    // always read out current sp and current addr and sp
    always_comb begin
        ras_array_distram_read_index = sp;

        ret_ras_index = sp;
        ret_pc38 = ras_array_distram_read_data;
    end

    // ras array distram
    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::PC38_t)),
        .OUTER_WIDTH(corep::RAS_ENTRIES)
    ) PLRU_ARRAY_DISTRAM (
        .CLK(CLK),
        .rindex(ras_array_distram_read_index),
        .rdata(ras_array_distram_read_data),
        .wen(ras_array_distram_write_valid),
        .windex(ras_array_distram_write_index),
        .wdata(ras_array_distram_write_data)
    );
endmodule
