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
    input corep::pc38_t         link_pc38,

    // pc_gen return control
    input logic                 ret_valid,

    output logic                ret_fallback,
    output corep::pc38_t        ret_pc38,
    output corep::ras_idx_t     ret_ras_idx,
    output corep::ras_cnt_t     ret_ras_cnt,

    // update control
    input logic                 update_valid,
    input corep::ras_idx_t      update_ras_idx,
    input corep::ras_cnt_t      update_ras_cnt
);

    // ----------------------------------------------------------------
    // Signals:

    // ras array distram IO
    corep::ras_idx_t    ras_array_distram_read_index;
    corep::pc38_t       ras_array_distram_read_data;

    logic               ras_array_distram_write_valid;
    corep::ras_idx_t    ras_array_distram_write_index;
    corep::pc38_t       ras_array_distram_write_data;

    // sp control
    corep::ras_idx_t sp, next_sp, sp_plus_1, sp_minus_1;

    // count control
    corep::ras_cnt_t count, next_count, count_plus_1, count_minus_1;

    // ----------------------------------------------------------------
    // Logic:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            sp <= 0;
            count <= 0;
        end
        else begin
            sp <= next_sp;
            count <= next_count;
        end
    end

    always_comb begin
        sp_plus_1 = sp + 1;
        sp_minus_1 = sp - 1;

        // count saturates
        if (count == corep::RAS_ENTRIES) begin
            count_plus_1 = corep::RAS_ENTRIES;
        end
        else begin
            count_plus_1 = count + 1;
        end
        count_minus_1 = count - 1;
    end

    // sp control
    always_comb begin

        // default hold sp, count
        next_sp = sp;
        next_count = count;

        // default write
        ras_array_distram_write_valid = 1'b0;
        ras_array_distram_write_index = sp;
        ras_array_distram_write_data = link_pc38;

        // first priority: update
        if (update_valid) begin

            // take update sp, count
            next_sp = update_ras_idx;
            next_count = update_ras_cnt;
        end

        // otherwise, check for link and ret
        else if (link_valid & ret_valid) begin

            // check fallback
            if (ret_fallback) begin
                // link addr at next sp
                ras_array_distram_write_valid = 1'b1;
                ras_array_distram_write_index = sp_plus_1;

                // incr sp, count
                next_sp = sp_plus_1;
                next_count = count_plus_1;
            end
            else begin
                // link addr at current sp
                ras_array_distram_write_valid = 1'b1;
                ras_array_distram_write_index = sp;
            end
        end

        // otherwise, check for just link
        else if (link_valid) begin

            // link addr at next sp
            ras_array_distram_write_valid = 1'b1;
            ras_array_distram_write_index = sp_plus_1;

            // incr sp, count
            next_sp = sp_plus_1;
            next_count = count_plus_1;
        end

        // otherwise, check for just ret
        else if (ret_valid) begin

            // check no fallback
            if (~ret_fallback) begin
                // decr sp, count
                next_sp = sp_minus_1;
                next_count = count_minus_1;
            end
        end
    end

    // always read out current sp and current addr and sp
    always_comb begin
        ras_array_distram_read_index = sp;

        ret_pc38 = ras_array_distram_read_data;

        ret_fallback = (count == 0);
        ret_ras_idx = sp;
        ret_ras_cnt = count;
    end

    // ras array distram
    distram_1rport_1wport #(
        .INNER_WIDTH($bits(corep::pc38_t)),
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
