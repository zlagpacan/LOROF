/*
    Filename: q_classic.sv
    Author: zlagpacan
    Description: RTL for ready-valid Queue using classic msb + index method
    Spec: LOROF/spec/design/q_classic.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

`include "system_types_pkg.vh"
import system_types_pkg::*;

module q_classic #(
    parameter DATA_WIDTH = 32,
    parameter NUM_ENTRIES = 4,
    parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // enq
    input logic                     enq_valid,
    input logic [DATA_WIDTH-1:0]    enq_data,

    // enq feedback
    output logic                    enq_ready,

    // deq
    output logic                    deq_valid,
    output logic [DATA_WIDTH-1:0]   deq_data,

    // deq feedback
    input logic                     deq_ready
);

    // ----------------------------------------------------------------
    // Signals: 

    logic [NUM_ENTRIES-1:0][DATA_WIDTH-1:0] q_entries;

    typedef struct packed {
        logic                           msb;
        logic [LOG_NUM_ENTRIES-1:0]     index;
    } q_ptr_t;
    
    q_ptr_t enq_ptr, enq_ptr_plus_1;
    q_ptr_t deq_ptr, deq_ptr_plus_1;

    // ----------------------------------------------------------------
    // Logic: 

    assign deq_data = q_entries[deq_ptr.index];

    assign enq_ptr_plus_1 = enq_ptr + 1;
    assign deq_ptr_plus_1 = deq_ptr + 1;

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            q_entries <= '0;
            enq_ptr <= 0;
            deq_ptr <= 0;
        end
        else begin
            if (enq_ready & enq_valid) begin
                q_entries[enq_ptr.index] <= enq_data;
                enq_ptr <= enq_ptr_plus_1;
            end

            if (deq_ready & deq_valid) begin
                deq_ptr <= deq_ptr_plus_1;
            end
        end
    end

    // enq -> not full
    assign enq_ready = (enq_ptr.index != deq_ptr.index) | (enq_ptr.msb == deq_ptr.msb);

    // deq -> not empty
    assign deq_valid = (enq_ptr.index != deq_ptr.index) | (enq_ptr.msb != deq_ptr.msb);

endmodule