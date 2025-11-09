/*
    Filename: stamofu_aq.sv
    Author: zlagpacan
    Description: RTL for Store-AMO-Fence Unit Acquire Queue
    Spec: LOROF/spec/design/stamofu_aq.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module stamofu_aq #(
    parameter STAMOFU_AQ_ENTRIES = 4
) (
    // seq
    input logic CLK,
    input logic nRST,

    // op enqueue to acquire queue
    input logic                         stamofu_aq_enq_valid,
    input logic                         stamofu_aq_enq_mem_aq,
    input logic                         stamofu_aq_enq_io_aq,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_enq_ROB_index,

    // acquire queue enqueue feedback
    output logic                        stamofu_aq_enq_ready,

    // op update bank 0
    input logic                         stamofu_aq_update_bank0_valid,
    input logic                         stamofu_aq_update_bank0_mem_aq,
    input logic                         stamofu_aq_update_bank0_io_aq,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_update_bank0_ROB_index,

    // op update bank 1
    input logic                         stamofu_aq_update_bank1_valid,
    input logic                         stamofu_aq_update_bank1_mem_aq,
    input logic                         stamofu_aq_update_bank1_io_aq,
    input logic [LOG_ROB_ENTRIES-1:0]   stamofu_aq_update_bank1_ROB_index,

    // op dequeue from acquire queue
    input logic                         stamofu_aq_deq_valid,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_aq_deq_ROB_index,

    // ROB info and kill
    input logic [LOG_ROB_ENTRIES-1:0]   rob_abs_head_index,
    input logic                         rob_kill_valid,
    input logic [LOG_ROB_ENTRIES-1:0]   rob_kill_rel_kill_younger_index,

    // acquire advertisement
    output logic                        stamofu_aq_mem_aq_active,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_aq_mem_aq_oldest_abs_ROB_index,
    output logic                        stamofu_aq_io_aq_active,
    output logic [LOG_ROB_ENTRIES-1:0]  stamofu_aq_io_aq_oldest_abs_ROB_index
);

    // ----------------------------------------------------------------
    // Signals:

    // AQ entries
    logic [STAMOFU_AQ_ENTRIES-1:0]                          valid_by_entry;
    logic [STAMOFU_AQ_ENTRIES-1:0]                          killed_by_entry;
    logic [STAMOFU_AQ_ENTRIES-1:0]                          mem_aq_by_entry;
    logic [STAMOFU_AQ_ENTRIES-1:0]                          io_aq_by_entry;
    logic [STAMOFU_AQ_ENTRIES-1:0][LOG_ROB_ENTRIES-1:0]     ROB_index_by_entry;

    // new kill check
    logic [STAMOFU_AQ_ENTRIES-1:0] new_killed_by_entry;

    // update check
    logic [STAMOFU_AQ_ENTRIES-1:0] update_bank0_by_entry;
    logic [STAMOFU_AQ_ENTRIES-1:0] update_bank1_by_entry;

    // enqueue crossbar by entry
    logic [STAMOFU_AQ_ENTRIES-1:0] enq_valid_by_entry;

    // incoming enqueue req mask
    logic [STAMOFU_AQ_ENTRIES-1:0] enq_open_mask;
    logic [STAMOFU_AQ_ENTRIES-1:0] enq_pe_one_hot;
    logic [STAMOFU_AQ_ENTRIES-1:0] enq_one_hot;

    // mem aq PE
    logic [STAMOFU_AQ_ENTRIES-1:0] mem_aq_req_vec;
    logic [$clog2(STAMOFU_AQ_ENTRIES)-1:0] mem_aq_index;

    // io aq PE
    logic [STAMOFU_AQ_ENTRIES-1:0] io_aq_req_vec;
    logic [$clog2(STAMOFU_AQ_ENTRIES)-1:0] io_aq_index;

    // ----------------------------------------------------------------
    // Logic:

    // new killed and update checks
    always_comb begin
        for (int i = 0; i < STAMOFU_AQ_ENTRIES; i++) begin
            new_killed_by_entry[i] = rob_kill_valid & 
                (ROB_index_by_entry[i] - rob_abs_head_index) >= rob_kill_rel_kill_younger_index;

            update_bank0_by_entry[i] = stamofu_aq_update_bank0_valid
                & stamofu_aq_update_bank0_ROB_index == ROB_index_by_entry[i];

            update_bank1_by_entry[i] = stamofu_aq_update_bank1_valid
                & stamofu_aq_update_bank1_ROB_index == ROB_index_by_entry[i];
        end
    end

    // Enqueue Logic:

    assign enq_open_mask = ~valid_by_entry;
    pe_lsb #(.WIDTH(STAMOFU_AQ_ENTRIES)) ENQUEUE_PE_LSB (
        .req_vec(enq_open_mask),
        .ack_one_hot(enq_pe_one_hot),
        .ack_mask() // unused
    );
    assign enq_one_hot = enq_pe_one_hot & {STAMOFU_AQ_ENTRIES{stamofu_aq_enq_valid}};

    // give enqueue feedback
    assign stamofu_aq_enq_ready = |enq_open_mask;

    // route PE'd dispatch to entries
    assign enq_valid_by_entry = enq_one_hot;

    // always_ff @ (posedge CLK, negedge nRST) begin
    always_ff @ (posedge CLK) begin
        if (~nRST) begin
            valid_by_entry <= '0;
            killed_by_entry <= '0;
            mem_aq_by_entry <= '0;
            io_aq_by_entry <= '0;
            ROB_index_by_entry <= '0;
        end
        else begin

            // --------------------------------------------------------
            // highest entry only takes self:
                // self: [STAMOFU_AQ_ENTRIES-1]

            // check take above
            if (stamofu_aq_deq_valid) begin
                valid_by_entry[STAMOFU_AQ_ENTRIES-1] <= 1'b0;
            end

            // otherwise take self
            else begin

                // take self valid entry
                if (valid_by_entry[STAMOFU_AQ_ENTRIES-1]) begin
                    valid_by_entry[STAMOFU_AQ_ENTRIES-1] <= 1'b1;
                    killed_by_entry[STAMOFU_AQ_ENTRIES-1] <= killed_by_entry[STAMOFU_AQ_ENTRIES-1] | new_killed_by_entry[STAMOFU_AQ_ENTRIES-1];
                    ROB_index_by_entry[STAMOFU_AQ_ENTRIES-1] <= ROB_index_by_entry[STAMOFU_AQ_ENTRIES-1];

                    // check for update
                    if (update_bank0_by_entry[STAMOFU_AQ_ENTRIES-1]) begin
                        mem_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= stamofu_aq_update_bank0_mem_aq;
                        io_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= stamofu_aq_update_bank0_io_aq;
                    end
                    else if (update_bank1_by_entry[STAMOFU_AQ_ENTRIES-1]) begin
                        mem_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= stamofu_aq_update_bank1_mem_aq;
                        io_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= stamofu_aq_update_bank1_io_aq;
                    end
                    else begin
                        mem_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= mem_aq_by_entry[STAMOFU_AQ_ENTRIES-1];
                        io_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= io_aq_by_entry[STAMOFU_AQ_ENTRIES-1];
                    end
                end

                // take self enqueue
                else begin
                    valid_by_entry[STAMOFU_AQ_ENTRIES-1] <= enq_valid_by_entry[STAMOFU_AQ_ENTRIES-1];
                    killed_by_entry[STAMOFU_AQ_ENTRIES-1] <= 1'b0;
                    mem_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= stamofu_aq_enq_mem_aq;
                    io_aq_by_entry[STAMOFU_AQ_ENTRIES-1] <= stamofu_aq_enq_io_aq;
                    ROB_index_by_entry[STAMOFU_AQ_ENTRIES-1] <= stamofu_aq_enq_ROB_index;
                end
            end

            // --------------------------------------------------------
            // remaining lower entries can take self or above
            for (int i = 0; i <= STAMOFU_AQ_ENTRIES-2; i++) begin

                // check take above
                if (stamofu_aq_deq_valid) begin

                    // take valid entry above
                    if (valid_by_entry[i+1]) begin
                        valid_by_entry[i] <= 1'b1;
                        killed_by_entry[i] <= killed_by_entry[i+1] | new_killed_by_entry[i+1];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i+1];

                        // check for update
                        if (update_bank0_by_entry[i+1]) begin
                            mem_aq_by_entry[i] <= stamofu_aq_update_bank0_mem_aq;
                            io_aq_by_entry[i] <= stamofu_aq_update_bank0_io_aq;
                        end
                        else if (update_bank1_by_entry[i+1]) begin
                            mem_aq_by_entry[i] <= stamofu_aq_update_bank1_mem_aq;
                            io_aq_by_entry[i] <= stamofu_aq_update_bank1_io_aq;
                        end
                        else begin
                            mem_aq_by_entry[i] <= mem_aq_by_entry[i+1];
                            io_aq_by_entry[i] <= io_aq_by_entry[i+1];
                        end
                    end

                    // take enqueue above
                    else begin
                        valid_by_entry[i] <= enq_valid_by_entry[i+1];
                        killed_by_entry[i] <= 1'b0;
                        mem_aq_by_entry[i] <= stamofu_aq_enq_mem_aq;
                        io_aq_by_entry[i] <= stamofu_aq_enq_io_aq;
                        ROB_index_by_entry[i] <= stamofu_aq_enq_ROB_index;
                    end
                end

                // otherwise take self
                else begin

                    // take self valid entry
                    if (valid_by_entry[i]) begin
                        valid_by_entry[i] <= 1'b1;
                        killed_by_entry[i] <= killed_by_entry[i] | new_killed_by_entry[i];
                        ROB_index_by_entry[i] <= ROB_index_by_entry[i];

                        // check for update
                        if (update_bank0_by_entry[i]) begin
                            mem_aq_by_entry[i] <= stamofu_aq_update_bank0_mem_aq;
                            io_aq_by_entry[i] <= stamofu_aq_update_bank0_io_aq;
                        end
                        else if (update_bank1_by_entry[i]) begin
                            mem_aq_by_entry[i] <= stamofu_aq_update_bank1_mem_aq;
                            io_aq_by_entry[i] <= stamofu_aq_update_bank1_io_aq;
                        end
                        else begin
                            mem_aq_by_entry[i] <= mem_aq_by_entry[i];
                            io_aq_by_entry[i] <= io_aq_by_entry[i];
                        end
                    end

                    // take self enqueue
                    else begin
                        valid_by_entry[i] <= enq_valid_by_entry[i];
                        killed_by_entry[i] <= 1'b0;
                        mem_aq_by_entry[i] <= stamofu_aq_enq_mem_aq;
                        io_aq_by_entry[i] <= stamofu_aq_enq_io_aq;
                        ROB_index_by_entry[i] <= stamofu_aq_enq_ROB_index;
                    end
                end
            end
        end
    end

    // Output Logic:

    // deq lowest ROB index
        // just give info to cq
        // cq can use to check for unrecoverable fault if doesn't match cq dequeueing entry ROB index
    assign stamofu_aq_deq_ROB_index = ROB_index_by_entry[0];
    
    // mem aq check
    assign mem_aq_req_vec = 
        valid_by_entry
        & ~killed_by_entry
        & mem_aq_by_entry;

    // mem aq pe
    pe_lsb #(
        .WIDTH(STAMOFU_AQ_ENTRIES),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) MEM_AQ_PE (
        .req_vec(mem_aq_req_vec),
        .ack_mask(), // unused
        .ack_index(mem_aq_index)
    );

    // io aq check
    assign io_aq_req_vec = 
        valid_by_entry
        & ~killed_by_entry
        & io_aq_by_entry;

    // io aq pe
    pe_lsb #(
        .WIDTH(STAMOFU_AQ_ENTRIES),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) IO_AQ_PE (
        .req_vec(io_aq_req_vec),
        .ack_mask(), // unused
        .ack_index(io_aq_index)
    );

    // advertised aq latched mux
    // always_ff @ (posedge CLK, negedge nRST) begin
    always_ff @ (posedge CLK) begin
        if (~nRST) begin
            stamofu_aq_mem_aq_active <= 1'b0;
            stamofu_aq_mem_aq_oldest_abs_ROB_index <= '0;

            stamofu_aq_io_aq_active <= 1'b0;
            stamofu_aq_io_aq_oldest_abs_ROB_index <= '0;
        end
        else begin
            stamofu_aq_mem_aq_active <= |mem_aq_req_vec;
            stamofu_aq_mem_aq_oldest_abs_ROB_index <= ROB_index_by_entry[mem_aq_index];

            stamofu_aq_io_aq_active <= |io_aq_req_vec;
            stamofu_aq_io_aq_oldest_abs_ROB_index <= ROB_index_by_entry[io_aq_index];
        end
    end

endmodule