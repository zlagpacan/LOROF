/*
    Filename: q_fast_ready.sv
    Author: zlagpacan
    Description: RTL for ready-valid Queue which clocks its enq ready signal
    Spec: LOROF/spec/design/q_fast_ready.md
*/

module q_fast_ready #(
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

    logic [LOG_NUM_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_NUM_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    // ----------------------------------------------------------------
    // Logic: 

    assign deq_data = q_entries[deq_ptr];

    assign enq_ptr_plus_1 = enq_ptr + 1;
    assign deq_ptr_plus_1 = deq_ptr + 1;

    // always_ff @ (posedge CLK, negedge nRST) begin
    always_ff @ (posedge CLK) begin
        if (~nRST) begin
            q_entries <= '0;
            enq_ptr <= 0;
            deq_ptr <= 0;
            enq_ready <= 1'b1;
            deq_valid <= 1'b0;
        end
        else begin
            if (enq_ready & enq_valid) begin
                q_entries[enq_ptr] <= enq_data;
                enq_ptr <= enq_ptr_plus_1;
            end

            if (deq_ready & deq_valid) begin
                deq_ptr <= deq_ptr_plus_1;
            end

            if ((enq_ready & enq_valid) & ~(deq_ready & deq_valid)) begin
                enq_ready <= enq_ptr_plus_1 != deq_ptr;
                deq_valid <= 1'b1;
            end

            if ((deq_ready & deq_valid) & ~(enq_ready & enq_valid)) begin
                enq_ready <= 1'b1;
                deq_valid <= deq_ptr_plus_1 != enq_ptr;
            end
        end
    end

endmodule